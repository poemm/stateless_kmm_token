
/*
    stateless_kmm_token - An implementation of a stateless token, and some tools.
    Copyright (C) 2019  Paul Dworzanski

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/



/*

# to compile, read top of Makefile to make sure you have dependencies, then:
make

# to test with scout:
path/to/scout/target/release/phase2-scout test.yaml

*/

#include "ewasm.h"
#include "blake2.h"


// these consts can be changed, but for speedup can fix them with #define or const
uint32_t num_address_bits = {160}
uint32_t num_hash_bits = {160}
uint32_t num_balance_bits = {64}

uint32_t num_address_bytes;
uint32_t num_hash_bytes;
uint32_t num_balance_bytes;
void init_num_bytes(){
  num_hash_bytes = (num_hash_bits+7)/8;
  num_balance_bytes = (num_balance_bits+7)/8;
  num_address_bytes = (num_address_bits+7)/8;
}


// pointers related to merkle proofs, init to 0 otherwise linker has errors
uint8_t *calldata = 0;

uint8_t *node_labels_start = 0;
uint32_t node_label_current_idx = {0};
uint8_t node_label_byte = {0};

uint8_t *edge_labels_start = 0;
uint8_t *edge_label_current = 0;

uint8_t *edge_label_lengths_start = 0;
uint8_t *edge_label_length_current = 0;

uint8_t modified_subtree_info_start = 0;
uint8_t modified_subtree_info_current = 0;
uint32_t modified_subtree_info_bytelength = 0;

uint8_t *calldata_hashes_start = 0;
uint8_t *calldata_hashes_current = 0;

uint8_t *addresses_start = 0;
uint8_t *address_current = 0;

uint8_t *balances_old_start = 0;
uint8_t *balance_old_current = 0;
uint8_t *balances_new_start = 0;
uint8_t *balances_new_current = 0;

uint8_t *transactions_start = 0;
uint8_t *transaction_current = 0;


// more global data
uint32_t *num_pre_accounts = {0};
uint8_t *balances_new_start = {0};
uint32_t account_idx = 0;


// this is input to blake2b to hash the leaf, declare here for convenience
uint64_t leaf_buffer[] = {0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0};
uint64_t *leaf_buffer_balance = (uint64_t*)(((uint8_t*)leaf_buffer)+num_address_bytes);



// 0) decode calldata

void decode_calldata(uint8_t* calldata){
  int idx = 0;
  uint8_t *calldata_iter = calldata;
  uint16_t len = 0;

  // node labels
  len = (uint16_t)*calldata;
  node_labels_start = calldata+2;
  calldata+=2+len;

  // edge labels
  len = (uint16_t)*calldata;
  edge_labels_start = calldata+2;
  edge_label_current = edge_labels_start;
  calldata+=2+len;

  // edge label lengths
  len = (uint16_t)*calldata;
  edge_label_lengths_start = calldata+2;
  edge_label_length_current = edge_label_lengths_start;
  calldata+=2+len;

  // modified subtree info
  len = (uint16_t)*calldata;
  modified_subtree_info_start = calldata+2;
  modified_subtree_info_current = 0;
  modified_subtree_info_bytelength = len
  calldata+=2+len;

  // hashes
  len = (uint16_t)*calldata;
  calldata_hashes_start = calldata+2;
  calldata_hash_current = calldata_hashes_start;
  calldata+=2+len;

  // addresses, and compute num_pre_accounts
  len = (uint16_t)*calldata;
  addresses_start = calldata+2;
  address_current = addresses_start;
  calldata+=2+len;

  num_pre_accounts = len/num_address_bytes;

  // balances
  len = (uint16_t)*calldata;
  balances_old_start = calldata+2;
  balance_old_current = balances_old_start;
  calldata+=2+len;

  //transactions
  len = (uint16_t)*calldata;
  transactions_start = calldata+2;
  transaction_current = transactions_start;
  calldata+=2+len;
}



////////////////////////////////////////
// 1) copy pre-balances to post-balances

void init_new_balances(){
  int num_bytes_to_copy = num_pre_accounts*num_balance_bytes;
  balances_new_start = (uint8_t*) malloc(num_bytes_to_copy);
  memcpy(balances_new_start,balances_old_start,num_bytes_to_copy);
}



/////////////////////////////////
// 2) build each modified subtree


// bit twiddling helper
uint8_t* get_bits_big_endian(uint8_t* bytes, uint32_t start_bit_idx, uint32_t end_bit_idx){
  //todo: assertions that start_bit_idx <= end_bit_idx and are within bytes_
  uint32_t num_output_bytes = (end_bit_idx-start_bit_idx+8)/8;
  if (num_output_bytes == 0)
    return NULL;
  uint8_t* output_bytes = (uint8_t*)malloc(num_output_bytes);
  uint32_t start_byte_idx = start_bit_idx / 8;
  uint32_t end_byte_idx = end_bit_idx / 8;
  uint32_t start_bit_offset = start_bit_idx % 8;
  uint32_t end_bit_offset = end_bit_idx % 8;
  uint32_t num_bits_to_chop = 0;
  // first the case when no shift is needed
  if (start_bit_offset == 0){
    for (uint32_t i =0; i <= num_output_bytes; i++)
      output_bytes[i] = bytes[i+start_idx];
    num_bits_to_chop = 7-end_bit_idx%8;
  }
  else{
    // case where outputting one byte
    if (num_output_bytes == 1){
      output_bytes[0] = bytes[start_byte_idx]<<start_bit_offset;
      if (start_byte_idx < end_byte_idx)
        output_bytes[0] |= bytes[end_byte_idx]>>(7-end_bit_offset);
      num_bits_to_chop = (end_bit_idx-start_bit_idx+1)%8;
    }
    else {
      // left shift each byte before the last byte, and get remaining bits from next byte
      uint32_t i=0;
      for (i=0; i<num_output_bytes-1; i++)
        output_bytes[i] = (bytes[start_byte_idx+i]<<start_bit_offset) | (bytes[start_byte_idx+i+1]>>(8-start_bit_offset));
      // get last byte
      output_bytes[num_output_bytes-1] = bytes[start_byte_idx+i+1]<<start_bit_offset;
      if (num_output_bytes == end_byte_idx-start_byte_idx)
        output_bytes[num_output_bytes-1] |= bytes[end_byte_idx]>>(8-start_bit_offset);
      num_bits_to_chop = 7-(end_bit_idx-start_bit_idx);
    }
  }
  // chop off part at end
  output_bytes[num_output_bytes-1] &= (0xff<<num_bits_to_chop);
  return output_bytes;
}


// some getters

uint8_t get_next_node_label(){
  byteidx = node_label_current_idx/4;  
  bitidx = 2*(node_label_current_idx%4)
  node_label_current_idx += 1;
  // get the two bits
  node_label_byte = *(node_labels_start+byteidx);
  node_label_byte <<= bitidx;
  node_label_byte >>= 6;
  return node_label_byte;
}

uint8_t get_next_edge_label_length(){
  uint8_t len = *edge_label_length_current;
  edge_label_length_current+=1;
  return len;
}

uint8_t* get_next_address(){
  uint8_t* addy = address_current;
  address_current+=num_address_bytes;
  return addy;
}

uint32_t get_next_modified_subtree_info(){
  uint16_t idx;
 if (modified_subtree_info_current-modified_subtree_info_start >= modified_subtree_info_bytelength)
   idx = 0;
 else {
   idx = *(*uint16_t)modified_subtree_idxs;
   modified_subtree_info_current += 11;
 }
 return (uint32_t)idx;
}

uint32_t get_next_account_idx(){
  uint32_t idx = account_idx;
  account_idx+=1;
  return idx;
}

uint8_t* get_next_balance_new(){
  uint8_t* ptr = balances_new_current;
  balances_new_current += num_balance_bytes;
  return ptr;
}

uint8_t* get_next_hash(){
  uint8_t* ptr = calldata_hash_current;
  calldata_hash_current += num_hash_bytes;
  return ptr;
}

uint8_t* get_next_edge_label(uint8_t depth, uint8_t length){
  uint8_t* edge_label = get_bits_big_endian(address_current,depth,depth+length);
  return edge_label;
}

struct TreeNode{
  uint8_t* parent;
  // children
  uint8_t node_type;
  uint8_t* left;
  uint8_t* right;
  // edge label
  uint8_t* edge_label;
  uint8_t edge_label_len;
  uint8_t edge_label_len_total;
  // leaf stuff, sometimes null
  uint8_t* address;
  uint8_t* balance;
}

uint32_t _debug_build_idx = 0;
void build_tree_from_node_labels(uint8_t edge_label_len_total, TreeNode* node){
  _debut_build_idx+=1;
  uint8_t* node_label = get_next_node_label();
  if (node_label == 0){ //0b00
    // we have a leaf without an edge label or an edge label
    if (edge_label_len_total == num_address_bits-1){
      node->leaf_address = get_next_address();
      node->leaf_balance = get_next_balance_new();
      node->node_type = 0; //0b00
      node->edge_label_len_total = edge_label_len_total;
      return;
    } else {
      uint8_t edge_label_len = get_next_edge_label_length();
      uint8_t* edge_label = get_edge_label(edge_label_len_total, edge_label_len);
      node->edge_label_len = edge_label_len;
      node->edge_label = edge_label;
      edge_label_len_total += edge_label_len;
      // either a leaf or not a leaf
      if (edge_label_len_total == num_address_bits-1){
        node->leaf_address = get_next_address();
        node->leaf_balance = get_next_balance_new();
        node->node_type = 0; //0b00
        node->edge_label_len_total = edge_label_len_total;
        return;
      }
      else{
        // not leaf, get next node label and process it below
        node_label = get_next_node_label;
      }
    }
  }
  // so this is not a leaf, just an internal node
  node->edge_label_len_total = edge_label_len_total;
  node->node_type = node_label;
  if (node_label == 3/*0b11*/){
    node->left = (uint8_t*)malloc(sizeof(TreeNode));
    node->left->parent = node;
    build_tree_from_labels(edge_label_len_total+1, node->left);
  }
  else if (node_label == 2/*0b10*/){
  }
  else if (node_label == 1/*0b01*/){
  }
}

/*
This function does all of the merklization, in a single-pass, of both old and new root.

depth is the depth of the tree node corresponding to this recursive function call.

hash_stack_ptr is the stack which maintains hash inputs and outputs.
The stack grows with each recursive call of this function, and shrinks with each return.
A stack item looks like this, where "old hash left" means the pre-state hash of the left child:
byte offset:  0               20               40              60               80
data:         | old hash left | old hash right | new hash left | new hash right |
The hash output is put in indices to the left of this stack item, i.e. in its parent's stack item.

leftFlag is 1 if this function is called on the left child, and 0 if right.
*/
void merkleize_new_and_old_root(int depth, uint8_t *hash_stack_ptr, int leftFlag){
  // compute the offset to put the resulting hash for this node
  uint8_t* old_hash_output_ptr = hash_stack_ptr - (leftFlag?80:60);
  uint8_t* new_hash_output_ptr = hash_stack_ptr - (leftFlag?40:20);
  // if we are at a leaf, then hash it and return
  if (depth == num_address_bits){
    // fill buffer with address
    memcpy(leaf_buffer,addresses,num_address_bytes);
    //memcpy(leaf_buffer+num_address_bytes,balances_old,num_balance_bytes);
    memcpy(leaf_buffer_balance,balances_old,num_balance_bytes);
    blake2b( old_hash_output_ptr, num_hash_bytes, leaf_buffer, num_address_bytes+num_balance_bytes, NULL, 0 );
    // fill buffer with new value, then hash
    memcpy(leaf_buffer_balance,balances_new,num_balance_bytes);
    blake2b( new_hash_output_ptr, num_hash_bytes, leaf_buffer, num_address_bytes+num_balance_bytes, NULL, 0 );
    // increment pointers to next address and next balances
    addresses += num_address_bytes;
    balances_old += num_balance_bits/8;
    balances_new += num_balance_bits/8;
    return;
  }
  uint8_t opcode = *node_labels;
  node_labels++;
  uint8_t addy_chunk_bit_length, addy_chunk_byte_length;
  switch (opcode){
    case 0:
      // get address chunk
      addy_chunk_bit_length = *address_chunks;
      addy_chunk_byte_length = (addy_chunk_bit_length+7)/8;
      address_chunks += 1 + addy_chunk_byte_length;
      // recurse with updated depth, same hash_stack_ptr and leftFlag
      merkleize_new_and_old_root(depth+addy_chunk_bit_length, hash_stack_ptr, leftFlag);
      break;
    case 1:
      // recurse on right
      merkleize_new_and_old_root(depth+1, hash_stack_ptr+80, 0);
      // get hash from calldata, put in in both old and new left slots
      memcpy(hash_stack_ptr,proof_hashes,num_hash_bytes);
      memcpy(hash_stack_ptr+40,proof_hashes,num_hash_bytes);
      proof_hashes += num_hash_bytes;
      // finally hash old and new
      blake2b( old_hash_output_ptr, num_hash_bytes, hash_stack_ptr, num_hash_bytes*2, NULL, 0 );
      blake2b( new_hash_output_ptr, num_hash_bytes, hash_stack_ptr+40, num_hash_bytes*2, NULL, 0 );
      break;
    case 2:
      // recurse on left
      merkleize_new_and_old_root(depth+1, hash_stack_ptr+80, 1);
      // get hash from calldata, put in in both old and new right slots
      memcpy(hash_stack_ptr+20,proof_hashes,num_hash_bytes);
      memcpy(hash_stack_ptr+20+40,proof_hashes,num_hash_bytes);
      proof_hashes += num_hash_bytes;
      // finally hash old and new
      blake2b( old_hash_output_ptr, num_hash_bytes, hash_stack_ptr, num_hash_bytes*2, NULL, 0 );
      blake2b( new_hash_output_ptr, num_hash_bytes, hash_stack_ptr+40, num_hash_bytes*2, NULL, 0 );
      break;
    case 3:
      // recurse both left and right
      merkleize_new_and_old_root(depth+1, hash_stack_ptr+80, 1);
      merkleize_new_and_old_root(depth+1, hash_stack_ptr+80, 0);
      // hash what was returned
      blake2b( old_hash_output_ptr, num_hash_bytes, hash_stack_ptr, num_hash_bytes*2, NULL, 0 );
      blake2b( new_hash_output_ptr, num_hash_bytes, hash_stack_ptr+40, num_hash_bytes*2, NULL, 0 );
      break;
  }
}


// merkle roots, 32 bytes each
uint8_t post_state_root[] = {0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
uint8_t pre_state_root[] = {0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};


void _main(void){

  // get calldata
  uint32_t calldata_size = eth2_blockDataSize();
  if (calldata_size == 0)
    return; // error, revert
  uint8_t* calldata = (uint8_t*) malloc( calldata_size );
  eth2_blockDataCopy( (i32ptr*)calldata, 0, calldata_size  );

  // get old merkle root
  eth2_loadPreStateRoot((uint32_t*)pre_state_root);

  // parse calldata into pointers
  // proof hashes
  uint32_t proof_hashes_length = *(uint32_t*)calldata;
  proof_hashes = calldata+4;
  calldata += 4 + proof_hashes_length;
  // proof addresses
  uint32_t addresses_length = *(uint32_t*)calldata;
  addresses = calldata+4;
  calldata += 4 + addresses_length;
  // balances
  uint32_t balances_length = *(uint32_t*)calldata;
  balances_old = calldata+4;
  calldata += 4 + balances_length;
  // node_labels
  uint32_t node_labels_length = *(uint32_t*)calldata;
  node_labels = calldata+4;
  calldata += 4 + node_labels_length;
  // address_chunks
  uint32_t address_chunks_length = *(uint32_t*)calldata;
  address_chunks = calldata+4;
  calldata += 4 + address_chunks_length;

  // verify transactions
  // TODO: verify signatures here

  // apply balance transfers from transactions
  balances_new = malloc(balances_length);
  memcpy(balances_new, balances_old, balances_length);
  // TODO: apply balance transfers here, new balances are currently a copy of old ones

  // finally, merkleize prestate and poststate
  uint8_t* hash_stack_ptr = malloc(10000); // 10,000 bytes is bigger than needed for depth 50 tree
  merkleize_new_and_old_root(0, hash_stack_ptr+80, 1);

  // update hash, hash_stack_ptr+40 should correspond to new merkle root hash
  for (int i=0; i<20; i++)
    post_state_root[i] = hash_stack_ptr[40+i];

  // verify prestate against old merkle root hash
  for (int i=0; i<20; i++){
    if (hash_stack_ptr[i] != pre_state_root[i]){
    //  return; // error, revert
    }
  }

}




