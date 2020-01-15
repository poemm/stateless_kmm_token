
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


TODO
 - get_next_ check bounds

*/

//#define WASM 0
#define DEBUG 0

#if WASM
#include "ewasm.h"
#else
#include<stdio.h>	// for printf, etc
#include<stdint.h>	// for uint32_t, etc
#include<inttypes.h>	// for to print uint64_t, etc
#include<string.h>	// for memcpy, etc
#include<stdlib.h>	// for malloc, etc
#include <stdlib.h>	// for rand()
#include <time.h>	// to init rand()
#endif

#include "blake2.h"

int debug = 0;

///////////////
// some globals

uint8_t* state_root = NULL;

// BYTE SIZES
// for speedup can fix them with #define or const, but leave them as variables for now
// accounts
uint32_t num_address_bits=256;
uint32_t num_accountdata_bits=64;
uint32_t num_accountdata_bytes = 0; //{(num_accountdata_bits+7)/8};
uint32_t num_address_bytes = 0; //(num_address_bits+7)/8;
// hashes
uint32_t num_hash_bits=256;
uint32_t num_hash_bytes = 0; //(num_hash_bits+7)/8;
uint32_t num_hashes_bytes = 2;
uint32_t num_hash_byte_idx_bytes = 4;
uint32_t num_hash_navigation_bytes = 0; //num_address_bytes+num_hashes_bytes+num_hash_byte_idx_bytes;
// signature
uint32_t num_signature_bytes = 64;
uint32_t num_signature_bits = 0; //num_signature_bytes*8;
uint32_t num_message_bytes = 40;
uint32_t num_message_bits = 0; //num_message_bytes*8;
// transactions:
uint32_t num_transaction_bytes = 0; //1+1+num_signature_bytes+num_address_bytes+num_accountdata_bytes;
uint32_t num_transaction_bits = 0; //num_transaction_bytes*8;
// modified subtree idxs
uint32_t num_modified_subtree_idxs_bytes = 11;


// if change these consts later, must update
void init_num_bytes_and_bits() {
  num_accountdata_bytes = (num_accountdata_bits+7)/8;
  num_address_bytes = (num_address_bits+7)/8;
  num_hash_bytes = (num_hash_bits+7)/8;
  num_hash_navigation_bytes = num_address_bytes+num_hashes_bytes+num_hash_byte_idx_bytes;
  num_signature_bits = num_signature_bytes*8;
  num_message_bits = num_message_bytes*8;
  num_transaction_bytes=1+1+num_signature_bytes+num_address_bytes+num_accountdata_bytes;
  num_transaction_bits=num_transaction_bytes*8;
}



// CALLDATA INFO
uint32_t max_tree_depth = 0;

uint8_t* node_labels_start = 0;
uint32_t node_label_currentidx = 0;
uint32_t node_labels_bytelen = 0;

uint8_t* edge_label_lengths_start = 0;
uint8_t* edge_label_length_current = 0;
uint32_t edge_label_lengths_bytelen = 0;

uint8_t* edge_labels_start = 0;
uint8_t* edge_label_current = 0;
uint32_t edge_labels_bytelen = 0;

uint8_t* calldata_hashes_start = 0;
uint8_t* hash_current = 0;
uint32_t calldata_hashes_bytelen = 0;

uint8_t* modified_subtree_idxs_start = 0;
uint8_t* modified_subtree_idx_current = 0;
uint32_t modified_subtree_idxs_bytelen = 0;

uint8_t* addresses_start = 0;
uint8_t* address_current = 0;
uint32_t addresses_bytelen = 0;
uint32_t addresses_idx = 0;

uint8_t* accountdatas_start = 0;
uint8_t* accountdata_current = 0;
uint32_t accountdatas_bytelen = 0;

uint8_t* transactions_start = 0;
uint8_t* transaction_current = 0;
uint32_t transactions_bytelen = 0;

// globals related to accounts and account data
uint32_t account_idx = 0;
uint32_t post_accountdatas_idx = 0;
uint8_t* post_accountdatas_start = 0;
uint32_t num_original_accounts = 0;
uint32_t num_modified_subtrees = 0;




/*
// pointers related to merkle proofs, init to 0 otherwise linker has errors

// this is input to blake2b to hash the leaf, declare here for convenience
uint64_t leaf_buffer[] = {0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0};
uint64_t *leaf_buffer_balance = (uint64_t*)(((uint8_t*)leaf_buffer)+num_address_bytes);
uint64_t *leaf_buffer_nonce = (uint64_t*)(((uint8_t*)leaf_buffer)+num_address_bytes+num_balance_bytes);
*/


////////////////
// bit twiddling

uint8_t getbit(uint8_t* byteptr, uint32_t bitidx){
  //printf("getbit(%u, %u)\n", *(uint32_t*)byteptr, bitidx);
  uint8_t byte = *(byteptr + bitidx/8);
  uint8_t bit = ((byte<<(bitidx%8))%256)>>7;
  //printf("byte %u, bit %u  bitidxmod8 %u  (byte<<(bitidxmod8)))mod256 %u\n", byte, bit, bitidx%8, (((byte<<(bitidx%8))%256)>>7));
  return bit;
}

uint32_t bitcompare(uint8_t* byteptr1, uint8_t* byteptr2, uint32_t startbitidx, uint32_t len){
  //if(debug) printf("bitcompare(%p,%p,%u,%u)\n",byteptr1,byteptr2,startbitidx, len);
  for (int idx = startbitidx; idx<startbitidx+len; idx++){
    if (getbit(byteptr1, idx) != getbit(byteptr2, idx))
      return idx;
  }
  return startbitidx+len;
}


// 0) decode calldata

void decode_calldata(uint8_t* calldata){

  uint8_t *calldata_iter = calldata;

  // max tree depth
  max_tree_depth = (uint32_t) *calldata_iter;
  calldata+=1;

  // node labels
  node_labels_bytelen = (uint32_t)(*(uint16_t*)calldata);
  node_labels_start = calldata+2;
  node_label_currentidx = 0;
  calldata+=2+node_labels_bytelen;

  // edge label lengths
  edge_label_lengths_bytelen = (uint32_t)(*(uint16_t*)calldata);
  edge_label_lengths_start = calldata+2;
  edge_label_length_current = edge_label_lengths_start;
  calldata+=2+edge_label_lengths_bytelen;

  // edge labels
  edge_labels_bytelen = (uint32_t)(*(uint16_t*)calldata);
  edge_labels_start = calldata+2;
  edge_label_current = edge_labels_start;
  calldata+=2+edge_labels_bytelen;

  // modified subtree info
  modified_subtree_idxs_bytelen = (uint32_t)(*(uint16_t*)calldata);
  modified_subtree_idxs_start = calldata+2;
  modified_subtree_idx_current = modified_subtree_idxs_start;
  calldata+=2+modified_subtree_idxs_bytelen;

  // hashes
  calldata_hashes_bytelen = (uint32_t)(*(uint32_t*)calldata);
  calldata_hashes_start = calldata+4;
  hash_current = calldata_hashes_start;
  calldata+=4+calldata_hashes_bytelen;

  // addresses, and compute num_pre_accounts
  addresses_bytelen = (uint32_t)(*(uint16_t*)calldata);
  addresses_start = calldata+2;
  address_current = addresses_start;
  calldata+=2+addresses_bytelen;

  num_original_accounts = addresses_bytelen/num_address_bytes;

  // account data, eg balance
  accountdatas_bytelen = (uint32_t)(*(uint16_t*)calldata);
  accountdatas_start = calldata+2;
  accountdata_current = accountdatas_start;
  calldata+=2+accountdatas_bytelen;

  //transactions
  transactions_bytelen = (uint32_t)(*(uint16_t*)calldata);
  transactions_start = calldata+2;
  transaction_current = transactions_start;
  //calldata+=2+transactions_bytelen;

}



////////////////////////////////////////
// 1) copy pre-balances to post-balances

void init_new_balances(){
  //int num_bytes_to_copy = num_pre_accounts*num_balance_bytes;
  //balances_new_start = (uint8_t*) malloc(num_bytes_to_copy);
  //memcpy(balances_new_start,balances_old_start,num_bytes_to_copy);
  post_accountdatas_start = (uint8_t*)malloc(accountdatas_bytelen);
  memcpy(post_accountdatas_start, accountdatas_start, accountdatas_bytelen);
  num_original_accounts = accountdatas_bytelen/num_accountdata_bytes;
}


/////////////////////////////////
// 2) build each modified subtree

// some getters

uint8_t get_next_node_label_bitpair(){
  // get byte and bit
  uint8_t byteidx = node_label_currentidx/4;
  uint8_t bitidx = 2*(node_label_currentidx%4);
  // increment for next time
  node_label_currentidx += 1;
  // get two bits
  uint8_t byte = * (node_labels_start+byteidx);
  byte = (byte<<bitidx)%256;
  byte >>= 6;
  return byte;
}

uint32_t get_next_edge_label_length(){
  // this is used to build subtree and to merkleize pre&post
  //printf("get_next_edge_label_length() %u %u",edge_label_lengths_startbyteidx,edge_label_lengths_idx);
  uint32_t len = *edge_label_length_current;
  edge_label_length_current += 1;
  return len;
}

uint8_t* get_next_address(){
  //printf("get_next_address()");
  // this is used to build subtree and to merkleize pre&post
  uint8_t* addy = address_current;
  address_current += num_address_bytes;
  return addy;
}

uint32_t next_modified_subtree_node_label_idx = 0;
void get_next_modified_subtree_node_label_idx(){
  // this is used to merkleize pre&post
  //printf("get_next_modified_subtree_node_label_idx()");
  if (modified_subtree_idx_current-modified_subtree_idxs_start >= modified_subtree_idxs_bytelen)
    next_modified_subtree_node_label_idx = -1;
  else{
    next_modified_subtree_node_label_idx = *(uint16_t*)modified_subtree_idx_current;
    modified_subtree_idx_current += num_modified_subtree_idxs_bytes;
  }
}

uint32_t get_next_account_idx(){
  // this is used to build subtree
  account_idx += 1;
  return account_idx;
}

uint8_t* get_next_postaccountdata(){
  // this is used to build subtree
  uint8_t* current = post_accountdatas_start + post_accountdatas_idx*num_accountdata_bytes;
  post_accountdatas_idx += 1;
  return current;
}

// TODO: make sure this agrees with everywhere it is used
uint8_t* get_next_hash(){
  // this is used to build subtree and to merkleize pre&post
  uint8_t* hash = hash_current;
  hash_current += num_hash_bytes;
  return hash;
}


struct Tree_node{
  // children
  struct Tree_node* parent;
  uint8_t* left;
  uint8_t* right;
  // edge label
  uint8_t* edge_label;
  uint32_t edge_label_startbitidx;
  uint32_t edge_label_len;
  // node type
  uint8_t node_type;
};



#if DEBUG
uint32_t debug_build_idx = 0;
#endif
void build_tree_from_node_labels(struct Tree_node* node, uint32_t edge_label_startbitidx){
  #if DEBUG
    debug_build_idx+=1;
    printf("%u build_tree_from_node_labels(%u)\n",debug_build_idx,edge_label_startbitidx);
  #endif
  node->edge_label_len = 0;
  node->edge_label_startbitidx = edge_label_startbitidx;
  node->edge_label = address_current;
  // get node label
  uint8_t node_label = get_next_node_label_bitpair();
  #if DEBUG
    printf("%u build_tree_from_node_labels() node_label %u\n",debug_build_idx,node_label);
  #endif
  // todo: assert we are within bound of label length, etc
  if (node_label == 0){
    // either we are already at a leaf, or there is an edge label
    if (edge_label_startbitidx == num_address_bits){ // a leaf without an edge label, this is unlikely
      node->left = get_next_address();
      node->right = get_next_postaccountdata();
      node->node_type = 0;
      node->edge_label = node->left;
      return;
    }
    else{
      // there is an edge label, get it
      node->edge_label_len = get_next_edge_label_length();
      // either leaf or not leaf
      if (node->edge_label_startbitidx + node->edge_label_len == num_address_bits){
        node->left = get_next_address();
        node->right = get_next_postaccountdata();
        node->node_type = 0;
        return;
      }
      else{
        // not a leaf, get next node label and process it below
        node_label = get_next_node_label_bitpair();
      }
    }
  }
  // this is an internal node, we already got the edge label if there was one
  node->node_type = node_label;
  if (node_label == 3){
    // recurse left and right
    struct Tree_node* left_subtree = (struct Tree_node*) malloc(sizeof(struct Tree_node));
    left_subtree->parent = node;
    node->left = (uint8_t*)left_subtree;
    build_tree_from_node_labels( left_subtree, node->edge_label_startbitidx+node->edge_label_len+1 );
    struct Tree_node* right_subtree = (struct Tree_node*) malloc(sizeof(struct Tree_node));
    right_subtree->parent = node;
    node->right = (uint8_t*)right_subtree;
    build_tree_from_node_labels( right_subtree, node->edge_label_startbitidx+node->edge_label_len+1 );
  }
  else if (node_label == 2){
    // recurse left, get hash for right
    struct Tree_node* left_subtree = (struct Tree_node*) malloc(sizeof(struct Tree_node));
    left_subtree->parent = node;
    node->left = (uint8_t*)left_subtree;
    build_tree_from_node_labels( left_subtree, node->edge_label_startbitidx+node->edge_label_len+1 );
    node->right = get_next_hash();
  }
  else if (node_label == 1){
    // get hash for left, recurse right
    node->left = get_next_hash();
    struct Tree_node* right_subtree = (struct Tree_node*) malloc(sizeof(struct Tree_node));
    right_subtree->parent = node;
    node->right = (uint8_t*)right_subtree;
    build_tree_from_node_labels( right_subtree, node->edge_label_startbitidx+node->edge_label_len+1 );
  }
}


// build each subtree, put them in a global array
struct Tree_node* modified_subtrees = NULL;
void build_modified_subtrees(){
  #if DEBUG
    printf("build_modified_subtrees()\n");
  #endif
  modified_subtrees = (struct Tree_node*) malloc(num_modified_subtrees*sizeof(struct Tree_node));
  //printf("modified_subtree_idx_current %p\n",modified_subtree_idx_current);
  //printf("%p\n",modified_subtree_idx_current);
  //uint8_t* modified_subtree_idx_current = modified_subtree_idxs_start;
  //printf("%p\n",modified_subtree_idx_current);
  for (int i=0; i<num_modified_subtrees; i++){
    // get all relevant idxs
    #if DEBUG
      for (int j=0; j<11; j++){ printf("%02x ",modified_subtree_idx_current[j]); }
    #endif
    uint32_t node_labels_idx            = (uint32_t) *((uint16_t*)modified_subtree_idx_current);
    uint32_t edge_label_lengths_idx     = (uint32_t) *((uint16_t*)(modified_subtree_idx_current+2));
    uint32_t edge_labels_idx            = (uint32_t) *((uint16_t*)(modified_subtree_idx_current+4));
    uint32_t hashes_idx                 = (uint32_t) *((uint16_t*)(modified_subtree_idx_current+6));
    uint32_t account_idx                = (uint32_t) *((uint16_t*)(modified_subtree_idx_current+8));
    uint32_t address_prefix_bitidx      = modified_subtree_idx_current[10];
    uint32_t post_accountdatas_idx	= account_idx;
    node_label_currentidx = node_labels_idx;
    edge_label_length_current = edge_label_lengths_start + edge_label_lengths_idx;
    hash_current = calldata_hashes_start + hashes_idx*num_hash_bytes;
    address_current = addresses_start + account_idx*num_address_bytes;
    accountdata_current = accountdatas_start + account_idx*num_accountdata_bytes;
    #if DEBUG
      printf("build_modified_subtrees() iter %u\n \
              node_labels_idx %u \n\
	      edge_labels_lengths_idx %u \n\
	      edge_labels_idx %u  hashes_idx %u \n\
	      account_idx %u \n\
	      address_prefix_bitidx %u\n", i, node_labels_idx,edge_label_lengths_idx,edge_labels_idx,hashes_idx,account_idx,address_prefix_bitidx);
    #endif
    modified_subtree_idx_current += 11;
    // build subtree of nodes
    build_tree_from_node_labels(&modified_subtrees[i], address_prefix_bitidx);
  }
}







//  3) process transactions 

struct Tree_node* find_account_or_neighbor_or_error(struct Tree_node* node, uint8_t* address_current, uint32_t depth){
  #if DEBUG
    printf("find_account_or_neighbor_or_error( %p, %p)\n", node, address_current);
  #endif
  if (node==NULL)
    return NULL;
  // if has edge label
  if (node->edge_label_len){
    //if (debug) printf("have edge label\n");
    // check edge label against corresponding bits in address from signature
    //printf("%p %p\n",address_current, node->edge_label);
    //printf("%u %u\n",node->edge_label_startbitidx, node->edge_label_len);
    //printf("%p %p %u %u\n",address_current, node->edge_label, node->edge_label_startbitidx, node->edge_label_len);
    if (bitcompare(address_current, node->edge_label, node->edge_label_startbitidx, node->edge_label_len) != node->edge_label_startbitidx+node->edge_label_len){
      return node; // leaf not present, but have neighbor
    }
    //if (debug) printf("ok2\n");
  }
  // if leaf
  if (node->node_type == 0){ // leaf; or, equivalently, label_endbitidx==num_address_bits-1
    #if DEBUG
      printf("found leaf\n");
    #endif
    return node;
  }
  // recurse left/right based on next bit
  uint8_t nextbit = getbit(address_current, node->edge_label_startbitidx+node->edge_label_len);
  if (nextbit == 0){
    if (node->node_type == 1){
      #if DEBUG
        printf("error, can't recurse left into hash\n");
      #endif
      //if (depth>10)
      //  printf("depth %u\n",depth);
      return NULL;
    }
    #if DEBUG
      printf("recurse left %i\n",nextbit);
    #endif
    return find_account_or_neighbor_or_error((struct Tree_node*)node->left, address_current, depth+1);
  }
  else {
    if (node->node_type == 2){
      #if DEBUG
        printf("error, can't recurse right into hash\n");
      #endif
      //if (depth>10)
      //  printf("depth %u\n",depth);
      return NULL;
    }
    #if DEBUG
      printf("recurse right %i\n",nextbit);
    #endif
    return find_account_or_neighbor_or_error((struct Tree_node*)node->right, address_current,depth+1);
  }
}


struct Tree_node* insert_leaf(struct Tree_node* neighbor, uint8_t* address, uint8_t* accountdata){
  #if DEBUG
    printf("insert_leaf( %p, %p, %p )\n", neighbor, address, accountdata);
  #endif
  // if tree is empty, insert this address and accountdata and return
  if (neighbor == NULL){
    #if DEBUG
      printf("inserting one\n");
    #endif
    struct Tree_node* new_leaf = (struct Tree_node*) malloc(sizeof(struct Tree_node));
    new_leaf->node_type = 0;
    new_leaf->left = address;
    new_leaf->right = accountdata;
    new_leaf->edge_label_startbitidx = 0;
    new_leaf->edge_label_len = num_address_bits;
    new_leaf->edge_label = address;
    return new_leaf;
  }
  // get bit where address and edge_label diverge
  uint32_t i = bitcompare(address, neighbor->edge_label, neighbor->edge_label_startbitidx, neighbor->edge_label_len);
  uint32_t addybit = getbit(address,i);
  #if DEBUG
    printf("i %i\n",i);
  #endif
  // insert node
  struct Tree_node* new_interior_node = (struct Tree_node*) malloc(sizeof(struct Tree_node));
  new_interior_node->node_type = 3;
  struct Tree_node* new_leaf = (struct Tree_node*) malloc(sizeof(struct Tree_node));
  new_leaf->node_type = 0;
  new_leaf->left = address;
  new_leaf->right = accountdata;
  // first take care of edge labels and lengths
  new_interior_node->edge_label_startbitidx = neighbor->edge_label_startbitidx;
  new_interior_node->edge_label_len = i-neighbor->edge_label_startbitidx;
  new_interior_node->edge_label = address;
  new_leaf->edge_label_startbitidx = i+1;
  new_leaf->edge_label_len = num_address_bits-(i+1);
  new_leaf->edge_label = address;
  neighbor->edge_label_len -= i+1-neighbor->edge_label_startbitidx;
  neighbor->edge_label_startbitidx = i+1;
  // adjust parent and children pointers
  new_leaf->parent = new_interior_node;
  new_interior_node->parent = neighbor->parent;
  if (neighbor->parent){
    if (neighbor->parent->left == (uint8_t*)neighbor)
      neighbor->parent->left = (uint8_t*)new_interior_node;
    else if (neighbor->parent->right == (uint8_t*)neighbor)
      neighbor->parent->right = (uint8_t*)new_interior_node;
  }
  neighbor->parent = new_interior_node;
  // two cases: diverge left or right
  //printf("ok %i %p",addybit,new_interior_node);
  if (addybit==0){ // diverge right
    //printf("diverge right\n");
    new_interior_node->right = (uint8_t*)neighbor;
    new_interior_node->left = (uint8_t*)new_leaf;
  }
  else { // diverge left
    //printf("diverge left\n");
    new_interior_node->right = (uint8_t*)new_leaf;
    new_interior_node->left = (uint8_t*)neighbor;
  }
  return new_leaf;
}


// this update code can be modified to do custom things, eg update accountdata, increment nonce, etc
uint32_t num_balance_bytes = 6;
uint32_t num_nonce_bytes = 2;
void update_accounts(uint8_t* to_address, uint8_t* from_address, uint8_t* to_data, uint8_t* from_data, uint8_t* data){
  #if DEBUG
    printf("update_accounts()\n");
  #endif
  uint64_t from_balance = (*(uint64_t*)from_data)&0xffffffffffff;
  uint64_t from_nonce = (uint64_t) *(uint16_t*)(from_data+num_balance_bytes);
  uint64_t to_balance = (*(uint64_t*)to_data)&0xffffffffffff;
  uint64_t value = (*(uint64_t*)data)&0xffffffffffff;
  uint64_t nonce = (uint64_t) *(uint16_t*)(data+num_balance_bytes);
  #if DEBUG
    printf("from ");
    for (int j=0; j<num_address_bytes; j++)
      printf("%02x", from_address[j]);
    printf(" balance %lu nonce %lu\n", from_balance, from_nonce);
    printf("to ");
    for (int j=0; j<num_address_bytes; j++)
      printf("%02x", to_address[j]);
    printf(" balance %lu nonce %lu\n", to_balance,nonce);
    printf("value %lu\n", value);
  #endif
  if (from_balance < value)
    return;     // error
  if (nonce != from_nonce)
    return;     // error
  if (from_data == to_data)
    return;     // error
  from_balance -= value;
  to_balance += value;
  nonce += 1;
  *from_data = (*from_data) - value;
  *(uint16_t*)(from_data+num_balance_bytes) = (uint16_t)nonce; //((uint64_t)1)<<48; // increment nonce
  *to_data = (*to_data) + value;
  #if DEBUG
    printf("from ");
    for (int j=0; j<num_address_bytes; j++)
      printf("%02x", from_address[j]);
    printf(" balance %lu nonce %lu\n", from_balance, from_nonce);
    printf("to ");
    for (int j=0; j<num_address_bytes; j++)
      printf("%02x", to_address[j]);
    printf(" balance %lu nonce %lu\n", to_balance,nonce);
    printf("value %lu\n", value);
  #endif
}


void process_transactions(){
  #if DEBUG
    printf("process_transactions()\n");
  #endif
  uint32_t num_accountdatas = accountdatas_bytelen/num_accountdata_bytes;
  uint8_t* tx = transactions_start;
  uint8_t* txs_end = transactions_start+transactions_bytelen;
  while (tx < txs_end){
    #if DEBUG
      printf("tx iter, tx < txs_end\n");
    #endif
    // parse tx
    uint32_t from_idx = tx[0];
    uint32_t to_idx = tx[1];
    tx += 2;
    uint8_t* signature = tx;
    tx += num_signature_bytes;
    uint8_t* to_address = tx;
    tx += num_address_bytes;
    uint8_t* data = tx;
    tx += num_accountdata_bytes;
    // get accounts
    // from address and data
    if (from_idx >= num_accountdatas)
      return;  // error, from account must be in calldata, not newly created
    uint8_t* from_address = addresses_start + from_idx*num_address_bytes;
    uint8_t* from_data = post_accountdatas_start + from_idx*num_accountdata_bytes;
    // to_data, note we have to_address from signature message
    uint8_t* to_data = NULL;
    if (to_idx < num_accountdatas)
      to_data = post_accountdatas_start + to_idx*num_accountdata_bytes;
    else if (to_idx < num_accountdatas + num_modified_subtrees){
      // traverse tree until leaf, possibly inserting a new leaf
      #if DEBUG
        printf("must traverse tree.   to_idx %u  num_orignal_accounts %u\n", to_idx, num_original_accounts);
      #endif
      struct Tree_node* node = (struct Tree_node*) (modified_subtrees + sizeof(struct Tree_node)*(to_idx-num_original_accounts));
      #if DEBUG
        printf("node %p\n",node);
      #endif
      // check subtree address prefix against to address prefix
      if (bitcompare(node->edge_label, to_address, node->edge_label_startbitidx, node->edge_label_len) != node->edge_label_startbitidx+node->edge_label_len){
        #if DEBUG
          printf("error address prefix not equal\n");
        #endif
        return; // error
      }
      // find leaf for this account or the neighbor which it branches from if there is a new node
      struct Tree_node* found_node = find_account_or_neighbor_or_error(node, to_address, 0);
      // if not a leaf, must insert leaf
      if (found_node->node_type!=0)
        found_node = insert_leaf(found_node, to_address, malloc(num_accountdata_bytes));
      to_data = found_node->right;
    }
    else{
      #if DEBUG
        printf("error, to_idx is too large");
      #endif
      return; // error
    }
    // apply account updates
    update_accounts(to_address, from_address, to_data, from_data, data);
  }

}




//  4) Merkleize pre and post root

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


// globals related to merkelization, maybe could also pass as args
uint32_t num_hash_block_bytes = 1024;
uint32_t num_hash_state_bytes = 512;
uint32_t hash_state = 0;
uint32_t hash_inplace_flag = 0;
uint32_t num_hashblock_bytes = 0;
uint8_t* max_hashstack = NULL;
uint32_t modifiable_subtree_idx = 0;

void init_hash(){
  num_hashblock_bytes = 2*num_hash_bytes+1;
}

void hash_(uint8_t* dst, uint8_t* src, uint32_t len){
  #if DEBUG
  printf("to be hashed ");
  for(int i=0;i<len;i++){
    printf("%02x",src[i]);
  }
  printf("\n");
  #endif
  //printf("%u\n",num_hash_bytes);
  if (len==2*num_hash_bytes+1){
    #if DEBUG
    printf("ok1 %u %u\n",src[0],src[num_hash_bytes]);
    #endif
    dst[0] = src[0]+src[num_hash_bytes];
  }
  else{
    #if DEBUG
    printf("ok2 %u\n",src[num_address_bytes]);
    #endif
    dst[0] = src[num_address_bytes];
  }
}

void merkleize_modifiable_subtree(uint8_t* hash_block, struct Tree_node* node, uint32_t recursion_depth){
  #if DEBUG
    printf("%*smerkleize_modifiable_subtree(%p, %p, %u)\n",recursion_depth,"",hash_block,node,recursion_depth);
  #endif
  if (max_hashstack <= hash_block){
    #if DEBUG
      printf("error: bad max_tree_depth");
    #endif
    return;
  }
  // zero workspace
  for (int i=0; i<num_hashblock_bytes; i++)
    hash_block[i] = 0;
  uint32_t hash_len = num_hashblock_bytes;
  #if DEBUG
    printf("%*snode type: %u\n",recursion_depth,"",node->node_type);
  #endif
  if (node->node_type==0) { // # leaf
    memcpy(hash_block, node->left, num_address_bytes);
    memcpy(hash_block+num_address_bytes, node->right, num_accountdata_bytes);
    hash_block[num_address_bytes+num_accountdata_bytes+1] = node->edge_label_len;
    hash_len = num_address_bytes+num_accountdata_bytes+1;
  }
  else if (node->node_type==1) {
    memcpy(hash_block, node->left, num_hash_bytes);
    merkleize_modifiable_subtree(hash_block+num_hashblock_bytes, (struct Tree_node*)node->right, recursion_depth+1);
    memcpy(hash_block+num_hash_bytes, hash_block+num_hashblock_bytes, num_hash_bytes);
    hash_block[2*num_hash_bytes+1] = node->edge_label_len;
  }
  else if (node->node_type == 2){
    merkleize_modifiable_subtree(hash_block+num_hashblock_bytes, (struct Tree_node*)node->left, recursion_depth+1);
    memcpy(hash_block, hash_block+num_hashblock_bytes, num_hash_bytes);
    memcpy(hash_block+num_hash_bytes, node->right, num_hash_bytes);
    hash_block[2*num_hash_bytes+1] = node->edge_label_len;
  }
  else if (node->node_type == 3){
    merkleize_modifiable_subtree(hash_block+num_hashblock_bytes, (struct Tree_node*)node->left, recursion_depth+1);
    memcpy(hash_block, hash_block+num_hashblock_bytes, num_hash_bytes);
    merkleize_modifiable_subtree(hash_block+num_hashblock_bytes, (struct Tree_node*)node->right, recursion_depth+1);
    memcpy(hash_block+num_hash_bytes, hash_block+num_hashblock_bytes, num_hash_bytes);
    hash_block[2*num_hash_bytes+1] = node->edge_label_len;
  }
  hash_(hash_block, hash_block, hash_len);
}


void merkleize_pre_and_post(uint8_t* hash_block, uint32_t depth, uint32_t recursion_depth, uint32_t post_hash_flag){
  #if DEBUG
    printf("%*smerkleize_pre_and_post(%p, %u, %u, %u)\n",recursion_depth,"",hash_block,depth,recursion_depth,post_hash_flag);
  #endif
  uint32_t num_workspace_bytes = num_hashblock_bytes + post_hash_flag*num_hashblock_bytes;
  if (max_hashstack <= hash_block){
    #if DEBUG
      printf("%*serror: bad max_tree_depth\n",recursion_depth,"");
    #endif
    return;
  }
  // zero it out
  for (int i=0; i<num_workspace_bytes; i++)
    hash_block[i]=0;
  uint32_t hash_len = num_hashblock_bytes;
  uint8_t edge_label_len = 0;
  if (node_label_currentidx == next_modified_subtree_node_label_idx){
    post_hash_flag = 0;
    struct Tree_node* node = (struct Tree_node*) (modified_subtrees + modifiable_subtree_idx*sizeof(struct Tree_node));
    merkleize_modifiable_subtree(hash_block+num_hashblock_bytes, node, recursion_depth);
    // set up for next modifiable subtree
    modifiable_subtree_idx+=1;
    get_next_modified_subtree_node_label_idx();
  }
  uint8_t node_label = get_next_node_label_bitpair();
  if (node_label == 0){
    if (depth==num_address_bits) { // leaf with no edge label, this is rare
      // put address, prestate accountdata, and edge_label_len=0
      memcpy(hash_block, addresses_start+account_idx*num_address_bytes,num_address_bytes);
      memcpy(hash_block+num_address_bytes, accountdatas_start+account_idx*num_accountdata_bytes,num_accountdata_bytes);
      if (post_hash_flag==1){
        memcpy(hash_block+num_hashblock_bytes, addresses_start+account_idx*num_address_bytes,num_address_bytes);
        memcpy(hash_block+num_hashblock_bytes+num_address_bytes, post_accountdatas_start+account_idx*num_accountdata_bytes,num_accountdata_bytes);
      }
      account_idx = get_next_account_idx();
      hash_len = num_address_bytes+num_accountdata_bytes+1;
    }
    else {
      edge_label_len = get_next_edge_label_length();
      depth += edge_label_len;
      if (depth==num_address_bits) { // a leaf with an edge label
        memcpy(hash_block, addresses_start+account_idx*num_address_bytes,num_address_bytes);
        memcpy(hash_block+num_address_bytes, accountdatas_start+account_idx*num_accountdata_bytes,num_accountdata_bytes);
        hash_block[num_address_bytes+num_accountdata_bytes+1] = edge_label_len;
        if (post_hash_flag==1){
          // put address, poststate accountdata, and edge_label_len=0
          memcpy(hash_block+num_hashblock_bytes, addresses_start+account_idx*num_address_bytes,num_address_bytes);
          memcpy(hash_block+num_hashblock_bytes+num_address_bytes, post_accountdatas_start+account_idx*num_accountdata_bytes,num_accountdata_bytes);
          hash_block[num_hashblock_bytes+num_address_bytes+num_accountdata_bytes+1] = edge_label_len;
	}
        account_idx = get_next_account_idx();
        hash_len = num_address_bytes+num_accountdata_bytes+1;
      }
      else { // not a leaf, get next node label and process it below
        node_label = get_next_node_label_bitpair();
      }
    }
  }
  if (node_label == 1){
    // get left witness hash for prestate
    uint8_t* left_hash = get_next_hash();
    memcpy(hash_block, left_hash, num_hash_bytes);
    if (post_hash_flag==1)
      memcpy(hash_block+num_hashblock_bytes, left_hash, num_hash_bytes);
    // compute and get right hash
    uint8_t* right_hash = hash_block+num_workspace_bytes;
    merkleize_pre_and_post(right_hash, depth+1, recursion_depth+1, post_hash_flag);
    memcpy(hash_block+num_hash_bytes, right_hash, num_hash_bytes);
    if (post_hash_flag==1)
      memcpy(hash_block+num_hashblock_bytes+num_hash_bytes, right_hash+num_hashblock_bytes, num_hash_bytes);
  }
  else if (node_label == 2){
    // compute and get left hash
    uint8_t* left_hash = hash_block+num_workspace_bytes;
    merkleize_pre_and_post(left_hash, depth+1, recursion_depth+1, post_hash_flag);
    memcpy(hash_block, left_hash, num_hash_bytes);
    if (post_hash_flag==1)
      memcpy(hash_block+num_hashblock_bytes, left_hash+num_hashblock_bytes, num_hash_bytes);
    // get right witness hash for prestate
    uint8_t* right_hash = get_next_hash();
    memcpy(hash_block+num_hash_bytes, right_hash, num_hash_bytes);
    if (post_hash_flag==1)
      memcpy(hash_block+num_hashblock_bytes+num_hash_bytes, right_hash, num_hash_bytes);
  }
  else if (node_label == 3){
    // compute and get left hash
    uint8_t* left_hash = hash_block+num_workspace_bytes;
    merkleize_pre_and_post(left_hash,depth+1,recursion_depth+1,post_hash_flag);
    memcpy(hash_block, left_hash, num_hash_bytes);
    if (post_hash_flag==1)
      memcpy(hash_block+num_hashblock_bytes, left_hash+num_hashblock_bytes, num_hash_bytes);
    // compute and get right hash
    uint8_t* right_hash = hash_block+num_workspace_bytes;
    merkleize_pre_and_post(right_hash, depth+1, recursion_depth+1, post_hash_flag);
    memcpy(hash_block+num_hash_bytes, right_hash, num_hash_bytes);
    if (post_hash_flag==1)
      memcpy(hash_block+num_hashblock_bytes+num_hash_bytes, right_hash+num_hashblock_bytes, num_hash_bytes);
  }
  hash_(hash_block, hash_block, hash_len);
  if (post_hash_flag==1)
    hash_(hash_block+num_hashblock_bytes, hash_block+num_hashblock_bytes, hash_len);
}


uint8_t* init_merkleization_and_merkleize(){

  // init traversal values to the beginning
  node_label_currentidx = 0;
  edge_label_length_current = edge_label_lengths_start;
  hash_current = calldata_hashes_start;
  address_current = addresses_start;
  accountdata_current = accountdatas_start;
  modified_subtree_idx_current = modified_subtree_idxs_start;
  get_next_modified_subtree_node_label_idx();
  init_hash();
  // other globals
  modifiable_subtree_idx = 0;
  account_idx = 0;
  // init stack
  uint8_t* stack = malloc((max_tree_depth+1)*num_hashblock_bytes);
  max_hashstack = stack+(max_tree_depth+1)*2*num_hashblock_bytes;
  // finally, compute new and old hashes
  merkleize_pre_and_post(stack,0,0,1);
  return stack;

}








#if DEBUG
void print_tree(struct Tree_node* node, int indent);
#endif


// merkle roots, 32 bytes each
uint8_t pre_state_root[] = {0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
uint8_t post_state_root[] = {0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
uint8_t calldata_[] = {0x6,0x3,0x0,0xe2,0x30,0x40,0x5,0x0,0x1,0xfc,0xfe,0x1,0xfc,0x0,0x0,0xb,0x0,0x1,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x60,0x0,0x0,0x0,0x1,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x60,0x0,0x20,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xf0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x18,0x0,0x2,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x5,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x7,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xd4,0x0,0x0,0x2,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xf0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x3,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3,0x0,0x0,0x0,0x0,0x0,0x0,0x0};

#if WASM
#else
// Dummy functions for testing
uint32_t eth2_blockDataSize(){
  return sizeof(calldata_) / sizeof(calldata_[0]);
}
void eth2_blockDataCopy(uint32_t* dst, uint32_t start, uint32_t len){
  memcpy(dst, calldata_+start, len);
}
uint32_t eth2_loadPreStateRoot(uint32_t* dst){
  memcpy(dst, pre_state_root, num_hash_bytes);
}
#endif




int _main(void){

  //uint32_t calldata_size = eth2_blockDataSize();
  uint32_t calldata_size = sizeof(calldata_);
  uint8_t* calldata = calldata_;
  //uint8_t* calldata = (uint8_t*) malloc( calldata_size );
  //eth2_blockDataCopy( (uint32_t*)calldata, 0, calldata_size  );

  init_num_bytes_and_bits();

  //printf("calldata %p\n",calldata);

  // get calldata
  //if (calldata_size == 0)
  //  return; // error, revert

  // 0) decode calldata
  #if DEBUG
    printf("0) decode calldata\n");
  #endif
  decode_calldata(calldata);
  #if DEBUG
    printf("node_labels\t %p %i\n",node_labels_start, node_labels_bytelen);
    printf("edge_label_lengths %p %i\n",edge_label_lengths_start, edge_label_lengths_bytelen);
    printf("edge_labels\t %p %i\n",edge_labels_start, edge_labels_bytelen);
    printf("modified_subtrees %p %i\n",modified_subtree_idxs_start, modified_subtree_idxs_bytelen);
    printf("hashes\t\t %p %i\n",calldata_hashes_start, calldata_hashes_bytelen);
    printf("addresses\t %p %i\n",addresses_start, addresses_bytelen);
    printf("accountdatas\t %p %i\n",accountdatas_start, accountdatas_bytelen);
    printf("transactions\t %p %i\n",transactions_start, transactions_bytelen);
  #endif

  // 1) copy pre-accountdatas to post-accountdatas
  #if DEBUG
    printf("1) copy pre-accountdatas to post-accountdatas\n");
  #endif
  init_new_balances();

  // 2) build each modified subtree
  #if DEBUG
    debug_build_idx = 0;
    printf("2) build each modified subtree");
  #endif
  num_modified_subtrees = modified_subtree_idxs_bytelen/11;
  build_modified_subtrees();
  #if DEBUG
    for(int i=0; i<num_modified_subtrees; i++){
      printf("printing modified subtree %u\n",i);
      print_tree(&modified_subtrees[i],0);
    }
  #endif

  // 3) process transactions 
  #if DEBUG
    printf("3) process transactions\n");
  #endif
  process_transactions();
  #if DEBUG
    // print subtrees
    printf("\nprinting subtrees");
    for (int i=0; i<num_modified_subtrees; i++){
      struct Tree_node* node = &modified_subtrees[i];
      printf("subtree with address prefix of length %u and prefix",node->edge_label_startbitidx);
      for (int j=0; j<(node->edge_label_startbitidx+7)/8; j++)
        printf("%02x", node->edge_label[j]);
      printf("\n");
      print_tree(node,0);
    }
    // print preaccountdatas
    printf("\npreaccountdatas\n");
    for (int i=0; i<num_original_accounts; i++){
      uint8_t* acct = accountdatas_start + i*num_accountdata_bytes;
      for (int j=0; j<num_accountdata_bytes; j++)
        printf("%02x", acct[j]);
      printf("\n");
    }
    // print postaccountdatas
    printf("\npostaccountdatas\n");
    for (int i=0; i<num_original_accounts; i++){
      uint8_t* acct = post_accountdatas_start + i*num_accountdata_bytes;
      for (int j=0; j<num_accountdata_bytes; j++)
        printf("%02x", acct[j]);
      printf("\n");
    }
    printf("\n");
  #endif

  // 4) Merkleize pre and post root
  #if DEBUG
    printf("4) Merkleize pre and post root\n");
  #endif
  //uint8_t* hash_block = malloc(2*num_hashblock_bytes);
  uint8_t* hash_block = init_merkleization_and_merkleize();
  #if DEBUG
    printf("preroot:");
    for (int j=0; j<num_hash_bytes; j++)
      printf("%02x", hash_block[j]);
    printf("\n");
    printf("postroot:");
    for (int j=num_hashblock_bytes; j<num_hashblock_bytes+num_hash_bytes; j++)
      printf("%02x", hash_block[j]);
    printf("\n");
  #endif


  // verify prestate against old merkle root hash
  //eth2_loadPreStateRoot((uint32_t*)pre_state_root);
  for (int i=0; i<num_hash_bytes; i++){
    if (hash_block[i] != pre_state_root[i]){
    //  return; // error, revert
      #if DEBUG
        printf("error: prehashes different\n");
      #endif
    }
  }
  return hash_block[0];

}

















#if WASM
#else


//////////////
// print stuff

int dot_idx = 0;
int dot_hash_idx = 0;
void print_tree_dot_recursive_helper(FILE* fp, struct Tree_node* node, int parent_idx, char* edge_label){
  int node_idx = dot_idx++;
  int max_label_len = 5;

  // edge and edge label
  if (node_idx != 0){
    fprintf(fp,"n%u -> n%u[ label = \"%c",parent_idx, node_idx, *edge_label);
    for (int i=0; i < ((node->edge_label_len < max_label_len) ? node->edge_label_len : max_label_len) ; i++){
      if (getbit(node->edge_label, node->edge_label_startbitidx+i))
        fprintf(fp,"1");
      else
        fprintf(fp,"0");
    }
    if (node->edge_label_len > max_label_len)
      fprintf(fp,"...");
    fprintf(fp,"\"];\n");
  }

  // node and node label
  if (node->node_type == 0){ // leaf
    fprintf(fp,"n%u [  label = \"leaf",node_idx);
    //fprintf(fp,"%u", node->edge_label_startbitidx)
    for (int i=0; i<max_label_len; i++){
      if (getbit(node->left, i)){
        //fprintf(fp,"1");
      }
      else{
        //fprintf(fp,"0");
      }
    }
    //fprintf(fp," %02x%02x%02x%02x", node->left[0], node->left[1],node->left[2],node->left[3]);
    fprintf(fp,"\", color=blue, shape=box, style=filled];\n");
  }
  else if (node->node_type==1){
    fprintf(fp,"n%u [  label = \"01\"];\n", node_idx);
    fprintf(fp,"h%u [  label = \"h%u\", color=red, shape=point, width=0.2];\n", dot_hash_idx, dot_hash_idx);
    fprintf(fp,"n%u -> h%u[ label = \"0\"]", node_idx, dot_hash_idx);
    dot_hash_idx++;
    //fprintf(fp,"//recursing right\n");
    print_tree_dot_recursive_helper(fp,(struct Tree_node*)(node->right), node_idx, "1");
  }
  else if (node->node_type==2){
    fprintf(fp,"n%u [  label = \"10\"];\n",node_idx);
    //fprintf(fp,"//recursing left\n");
    print_tree_dot_recursive_helper(fp,(struct Tree_node*)(node->left), node_idx, "0");
    fprintf(fp,"h%u [  label = \"h%u\", color=red, shape=point, width=0.2];\n", dot_hash_idx, dot_hash_idx);
    fprintf(fp,"n%u -> h%u[ label = \"1\"]", node_idx, dot_hash_idx);
    dot_hash_idx++;
  }
  else if (node->node_type==3){
    fprintf(fp,"n%u [  label = \"11\"];\n",node_idx);
    //fprintf(fp,"//recursing left and right\n");
    print_tree_dot_recursive_helper(fp,(struct Tree_node*)(node->left), node_idx, "0");
    print_tree_dot_recursive_helper(fp,(struct Tree_node*)(node->right), node_idx, "1");
  }
}

void print_tree_dot(struct Tree_node* node, int parent_idx, char* edge_label){

  FILE * fp;
  int n;

  dot_idx = 0;

  fp = fopen ("tree1.dot","w");
  fprintf (fp, "digraph G {\n");
  print_tree_dot_recursive_helper(fp, node, dot_idx, " ");
  fprintf (fp, "}\n");
  fclose (fp);
}





void print_tree(struct Tree_node* node, int indent){

  printf("%*snode %p\n", indent, "", node);
  printf("%*snode_type %u\n", indent, "", node->node_type);
  printf("%*sedge_label_startbitidx %u\n", indent, "", node->edge_label_startbitidx);
  printf("%*sedge_label_len %u\n", indent, "", node->edge_label_len);
  if (node->node_type == 0){
    printf("%*saddress %02x%02x%02x%02x%02x%02x%02x%02x...\n", indent, "", node->left[0], node->left[1],node->left[2],node->left[3],node->left[4],node->left[5],node->left[6],node->left[7]);
    printf("%*sbalance %02x%02x%02x%02x%02x%02x%02x%02x\n", indent, "", node->right[0], node->right[1],node->right[2],node->left[3],node->right[4],node->right[5],node->right[6],node->right[7]);
  }
  else if (node->node_type==2){
    //printf("recursing left\n");
    printf("%*sright hash", indent, "");
    for (int i=0;i<num_hash_bytes;i++)
      printf("%02x", node->right[i]);
    printf("\n");
    print_tree((struct Tree_node*)node->left, indent+1);
  }
  else if (node->node_type==1){
    //printf("recursing right\n");
    printf("%*sleft hash", indent, "");
    for (int i=0;i<num_hash_bytes;i++)
      printf("%02x", node->left[i]);
    printf("\n");
    print_tree((struct Tree_node*)node->right, indent+1);
  }
  else if (node->node_type==3){
    //printf("recursing left and right\n");
    print_tree((struct Tree_node*)node->left, indent+1);
    print_tree((struct Tree_node*)node->right, indent+1);
  }
}





//////////////////
// test generation
//
#include "rand.h"
pcg32_random_t rng;

uint32_t rand_histogram[256];
void get_random_bytes(uint8_t* dst, uint32_t num_bytes){
  //uint8_t* ret = (uint8_t*) malloc(num_bytes);
  //printf("\nget_random_bytes(%u) ",num_bytes);
  for (int i=0; i<num_bytes; i++){
    //dst[i] = (random())%256;
    dst[i] = pcg32_boundedrand_r(&rng, 256);
    //dst[i] += rand()>>16;
    rand_histogram[dst[i]]++;
  }
  //for (int i=0; i<num_bytes; i++)
  //  printf("%02x", dst[i]);
  //printf("\n");
}

/* not needed, can get from traversal which accumulates labels
uint8_t get_max_tree_depth(struct Tree_node* node, uint8_t depth){
  if (node->node_type==0){
    return depth;
  }
  if (node->node_type==2){
    return get_max_tree_depth((struct Tree_node*)node->left, depth+1);
  }
  else if (node->node_type==1){
    return get_max_tree_depth((struct Tree_node*)node->right, depth+1);
  }
  else if (node->node_type==3){
    int depth_left = get_max_tree_depth((struct Tree_node*)node->left, depth+1);
    int depth_right = get_max_tree_depth((struct Tree_node*)node->right, depth+1);
    if (depth_right<depth_left)
      return depth_left;
    else
      return depth_right;
  }
}
*/


struct Tree_node* tree_generator(uint64_t num_accounts_in_witness, uint64_t num_accounts_in_state){
  printf("#accts in witnes: %"PRIu64",  #accts in state: %"PRIu64"\n", num_accounts_in_witness, num_accounts_in_state);

  struct Tree_node* tree = NULL;

  srand(time(NULL));
  srandom(time(NULL));
  pcg32_srandom_r(&rng, time(NULL), 54u);

  // generate addresses in witness and build a tree with just them
  for (uint64_t i=0; i<num_accounts_in_witness; i++){
    if(debug) printf("i %"PRIu64"\n",i);
    uint8_t* address = malloc(num_address_bytes);
    //printf("calling get_random_bytes(%u) ", (int)num_address_bytes);
    get_random_bytes(address, num_address_bytes);
    uint8_t* data = (uint8_t*) malloc(num_accountdata_bytes);
    struct Tree_node* found_node = find_account_or_neighbor_or_error(tree, address, 0);
    if (!found_node){
      if (debug) printf("tree was empty");
      tree = insert_leaf(NULL, address, data);
    }
    else if (found_node){
      // insert next to neighbor
      insert_leaf(found_node, address, data);
    }
    while (tree->parent)
      tree = tree->parent;
  }
  uint32_t rand_histogram_sum = 0;
  for (int i=0;i<256;i++){
    printf("%u %u\n",i,rand_histogram[i]);
    rand_histogram_sum += rand_histogram[i];
  }
  printf("rand_histogram_sum %u\n", rand_histogram_sum);
  //printf("\n\n tree before insertions\n");
  //print_tree(tree,0);
  //print_tree_dot(tree,0,"");

  // generate remaining state and insert into tree as dummy hashes
  uint8_t* data = (uint8_t*) malloc(num_accountdata_bytes);
  uint8_t* address = (uint8_t*) malloc(num_address_bytes);
  for (uint64_t i=0; i<num_accounts_in_state; i++){
    if(debug) printf("j %"PRIu64"\n",i);
    if(i%1000000==0) printf("j %"PRIu64"\n",i);
    get_random_bytes(address, num_address_bytes);
    struct Tree_node* found_node = find_account_or_neighbor_or_error(tree, address, 0);
    if (!found_node){
      //printf("found node NULL: %p",found_node);
    }
    else {
      // insert next to neighbor
      struct Tree_node* new_leaf = insert_leaf(found_node, address, data);
      //printf("\n\ninserting address %02x%02x%02x%02x%02x%02x%02x%02x...\n", new_leaf->left[0], new_leaf->left[1], new_leaf->left[2], new_leaf->left[3], new_leaf->left[4], new_leaf->left[5], new_leaf->left[6], new_leaf->left[7]);
      if (new_leaf->parent->right == (uint8_t*)new_leaf){
        //printf("inserting right\n");
        uint8_t* hash = malloc(num_hash_bytes);
        for (int i=0; i<num_hash_bytes; i++) hash[i] = 0;
        new_leaf->parent->right = hash;
        new_leaf->parent->node_type = 2;
        //free(new_leaf); //(struct Tree_node*)new_leaf->parent->right);
      }
      else if (new_leaf->parent->left == (uint8_t*)new_leaf){
        //printf("inserting left\n");
        uint8_t* hash = malloc(num_hash_bytes);
        for (int i=0; i<num_hash_bytes; i++) hash[i] = 0;
        new_leaf->parent->left = hash;
        new_leaf->parent->node_type = 1;
        //free(new_leaf); //(struct Tree_node*)new_leaf->parent->left);
      }
      while (tree->parent)
        tree = tree->parent;

    }

    //printf("\n\n tree %llu\n",i);
    //print_tree(tree,0);
    
  }
  for (int i=0;i<256;i++){
    printf("%u %u\n",i,rand_histogram[i]);
    rand_histogram_sum += rand_histogram[i];
  }
  printf("rand_histogram_sum %u\n", rand_histogram_sum);

  //printf("\n\nfinal tree\n");
  //print_tree(tree,0);
  print_tree_dot(tree,0,"");

  return tree;
}





struct bytes {
  uint8_t* startptr;
  uint8_t* ptr;
  uint32_t len;
};

struct bytes* node_labels_bytes_naive = NULL;
struct bytes* node_labels_bytes = NULL;
struct bytes* edge_label_lens_bytes = NULL;
struct bytes* edge_labels_bytes = NULL;
struct bytes* addresses_bytes = NULL;
struct bytes* accountdata_bytes = NULL;
struct bytes* hashes_bytes = NULL;




void tree2calldata_recursive_helper(struct Tree_node* node, uint32_t depth, uint32_t recursion_depth){
  if (max_tree_depth<recursion_depth)
    max_tree_depth = recursion_depth;
  // if leaf
  if (node->node_type == 0){
    node_labels_bytes_naive->ptr[0] = 0; node_labels_bytes_naive->ptr++;
    if (node->edge_label_len != 0){
      edge_label_lens_bytes->ptr[0] = node->edge_label_len; edge_label_lens_bytes->ptr++;
    }
    memcpy(addresses_bytes->ptr, node->left, num_address_bytes); addresses_bytes->ptr+=num_address_bytes;
    memcpy(accountdata_bytes->ptr, node->right, num_accountdata_bytes); accountdata_bytes->ptr+=num_accountdata_bytes;
    return;
  }
  // if edge label, not leaf
  if (node->edge_label_len){
    node_labels_bytes_naive->ptr[0] = 0; node_labels_bytes_naive->ptr++;
    edge_label_lens_bytes->ptr[0] = node->edge_label_len; edge_label_lens_bytes->ptr++;
    depth += node->edge_label_len;
  }
  // Node type. note: not a leaf and edge label, if any, already handled above
  if (node->node_type == 1){
    node_labels_bytes_naive->ptr[0] = 1; node_labels_bytes_naive->ptr++;
    tree2calldata_recursive_helper((struct Tree_node*)node->right, depth+1, recursion_depth+1);
    memcpy(hashes_bytes->ptr, node->left, num_hash_bytes); hashes_bytes->ptr+=num_hash_bytes;
  }
  else if (node->node_type == 2){
    node_labels_bytes_naive->ptr[0] = 2; node_labels_bytes_naive->ptr++;
    tree2calldata_recursive_helper((struct Tree_node*)node->left, depth+1, recursion_depth+1);
    memcpy(hashes_bytes->ptr, node->right, num_hash_bytes); hashes_bytes->ptr+=num_hash_bytes;
  }
  else if (node->node_type == 3){
    node_labels_bytes_naive->ptr[0] = 3; node_labels_bytes_naive->ptr++;
    tree2calldata_recursive_helper((struct Tree_node*)node->left, depth+1, recursion_depth+1);
    tree2calldata_recursive_helper((struct Tree_node*)node->right, depth+1, recursion_depth+1);
  }

}


uint32_t overestimate_bytes_len = 10000000; // for similicity, 1MB, make bigger if your witness may be bigger

void tree2calldata(struct Tree_node* root){

  node_labels_bytes_naive = (struct bytes*) malloc(sizeof(struct bytes));
  node_labels_bytes_naive->len = overestimate_bytes_len;
  node_labels_bytes_naive->startptr = (uint8_t*) malloc(node_labels_bytes_naive->len);
  node_labels_bytes_naive->ptr = node_labels_bytes_naive->startptr;

  edge_label_lens_bytes = (struct bytes*) malloc(sizeof(struct bytes));
  edge_label_lens_bytes->len = overestimate_bytes_len;
  edge_label_lens_bytes->startptr = (uint8_t*) malloc(edge_label_lens_bytes->len);
  edge_label_lens_bytes->ptr = edge_label_lens_bytes->startptr;

  addresses_bytes = (struct bytes*) malloc(sizeof(struct bytes));
  addresses_bytes->len = overestimate_bytes_len;
  addresses_bytes->startptr = (uint8_t*) malloc(addresses_bytes->len);
  addresses_bytes->ptr = addresses_bytes->startptr;

  accountdata_bytes = (struct bytes*) malloc(sizeof(struct bytes));
  accountdata_bytes->len = overestimate_bytes_len;
  accountdata_bytes->startptr = (uint8_t*) malloc(accountdata_bytes->len);
  accountdata_bytes->ptr = accountdata_bytes->startptr;

  hashes_bytes = (struct bytes*) malloc(sizeof(struct bytes));
  hashes_bytes->len = overestimate_bytes_len;
  hashes_bytes->startptr = (uint8_t*) malloc(hashes_bytes->len);
  hashes_bytes->ptr = hashes_bytes->startptr;

  // start traversal
  tree2calldata_recursive_helper(root,0,0);

  // fix byte arrays
  node_labels_bytes = (struct bytes*) malloc(sizeof(struct bytes));
  node_labels_bytes->len = overestimate_bytes_len;
  node_labels_bytes->startptr = (uint8_t*) malloc(node_labels_bytes->len);
  node_labels_bytes->ptr = node_labels_bytes->startptr;
  uint32_t num_node_label_bitpairs = node_labels_bytes_naive->ptr - node_labels_bytes_naive->startptr;
  for (int i=0; i<num_node_label_bitpairs/4+(num_node_label_bitpairs%4)>0?1:0; i++){
    uint8_t byte1 = node_labels_bytes_naive->ptr[0];
    uint8_t byte2 = node_labels_bytes_naive->ptr[1];
    uint8_t byte3 = node_labels_bytes_naive->ptr[2];
    uint8_t byte4 = node_labels_bytes_naive->ptr[3];
    *node_labels_bytes->ptr = (byte1<<6) | (byte2<<4) | (byte3<<2) | byte4;
    node_labels_bytes_naive->ptr+=4;
    node_labels_bytes->ptr++;
  }

}







struct bytes* generate_calldata(uint64_t num_accounts_in_witness, uint64_t num_accounts_in_state, uint64_t num_transactions_to_existing, uint64_t num_transactions_to_new){

  // generate tree
  struct Tree_node* tree = tree_generator(num_accounts_in_witness, num_accounts_in_state);

  printf("OK\n");
  printf("OK\n");
  printf("OK\n");
  printf("OK\n");
  printf("OK\n");
  printf("OK\n");
  printf("OK\n");
  printf("OK\n");

  // traverse tree collecting bytes of witness
  tree2calldata(tree);

  // generate transactions
  struct bytes* transactions_bytes = (struct bytes*) malloc(sizeof(struct bytes));
  transactions_bytes->len = 0;
  transactions_bytes->startptr = (uint8_t*) malloc(transactions_bytes->len);
  transactions_bytes->ptr = transactions_bytes->startptr;
  for (int i=0; i<num_transactions_to_existing; i++){
    uint8_t from_addy_idx = i%num_transactions_to_existing; //random.randint(0,num_accounts_in_witness-1)
    uint8_t to_addy_idx = (i+1)%num_transactions_to_existing; //random.randint(0,num_accounts_in_witness-1)
    uint64_t from_nonce = i/num_transactions_to_existing;
    uint64_t amount = 1;
    uint64_t accountdata = amount | (from_nonce<<48);
    transactions_bytes->ptr[0] = from_addy_idx;
    transactions_bytes->ptr[1] = to_addy_idx;
    transactions_bytes->ptr+=2;
    // TODO: signature, empty for now
    transactions_bytes->ptr+=num_signature_bytes;
    memcpy(transactions_bytes->ptr,addresses_bytes->startptr+to_addy_idx*num_address_bytes,num_address_bytes);
    transactions_bytes->ptr+=num_address_bytes;
    *(uint64_t*)transactions_bytes->ptr = accountdata;
    transactions_bytes->ptr+=num_accountdata_bytes;
  }


  // modified subtrees
  struct bytes* modified_subtree_idxs_bytes = (struct bytes*) malloc(sizeof(struct bytes));
  modified_subtree_idxs_bytes->len = 0;
  modified_subtree_idxs_bytes->startptr = (uint8_t*) malloc(modified_subtree_idxs_bytes->len);
  modified_subtree_idxs_bytes->ptr = modified_subtree_idxs_bytes->startptr;


  // edge labels aren't computed by tree2calldata(), should be empty
  edge_labels_bytes = (struct bytes*) malloc(sizeof(struct bytes));
  edge_labels_bytes->len = 0;
  edge_labels_bytes->startptr = (uint8_t*) malloc(edge_labels_bytes->len);
  edge_labels_bytes->ptr = edge_labels_bytes->startptr;



  uint32_t calldata_bytelen = (node_labels_bytes->ptr - node_labels_bytes->startptr) +
                              (edge_label_lens_bytes->ptr - edge_label_lens_bytes->startptr) +
                              (edge_labels_bytes->ptr - edge_labels_bytes->startptr) +
                              (modified_subtree_idxs_bytes->ptr - modified_subtree_idxs_bytes->startptr) +
                              (hashes_bytes->ptr - hashes_bytes->startptr) +
                              (addresses_bytes->ptr - addresses_bytes->startptr) +
                              (accountdata_bytes->ptr - accountdata_bytes->startptr) +
                              (transactions_bytes->ptr - transactions_bytes->startptr);
  struct bytes* calldata_bytes = (struct bytes*) malloc(sizeof(struct bytes));
  calldata_bytes->len = calldata_bytelen;
  calldata_bytes->startptr = (uint8_t*) malloc(calldata_bytes->len);
  calldata_bytes->ptr = calldata_bytes->startptr;

  int len = 1;
  calldata_bytes->ptr[0] = max_tree_depth;
  calldata_bytes->ptr+=len;

  len = node_labels_bytes->ptr - node_labels_bytes->startptr;
  printf("node_labels_bytes len %u\n", len);
  *(uint16_t*)calldata_bytes->ptr = (uint16_t)len;
  memcpy(calldata_bytes->ptr+2, node_labels_bytes->ptr, len);
  calldata_bytes->ptr+=2+len;

  len = edge_label_lens_bytes->ptr - edge_label_lens_bytes->startptr;
  printf("edge_label_lens_bytes len %u\n", len);
  *(uint16_t*)calldata_bytes->ptr = (uint16_t)len;
  memcpy(calldata_bytes->ptr+2, edge_label_lens_bytes->ptr, len);
  calldata_bytes->ptr+=2+len;

  len = edge_labels_bytes->ptr - edge_labels_bytes->startptr;
  printf("edge_labels_bytes len %u\n", len);
  *(uint16_t*)calldata_bytes->ptr = (uint16_t)len;
  memcpy(calldata_bytes->ptr, edge_labels_bytes->ptr, len);
  calldata_bytes->ptr+=2+len;

  len = modified_subtree_idxs_bytes->ptr - modified_subtree_idxs_bytes->startptr;
  printf("modified_subtree_idxs_bytes len %u\n", len);
  *(uint16_t*)calldata_bytes->ptr = (uint16_t)len;
  memcpy(calldata_bytes->ptr, modified_subtree_idxs_bytes->ptr, len);
  calldata_bytes->ptr+=2+len;

  len = hashes_bytes->ptr - hashes_bytes->startptr;
  printf("hashes_bytes len %u\n", len);
  *(uint32_t*)calldata_bytes->ptr = (uint32_t)len;
  memcpy(calldata_bytes->ptr, hashes_bytes->ptr, len);
  calldata_bytes->ptr+=4+len;

  len = addresses_bytes->ptr - addresses_bytes->startptr;
  printf("addresses_bytes len %u\n", len);
  *(uint16_t*)calldata_bytes->ptr = (uint16_t)len;
  memcpy(calldata_bytes->ptr, addresses_bytes->ptr, len);
  calldata_bytes->ptr+=2+len;

  len = accountdata_bytes->ptr - accountdata_bytes->startptr;
  printf("accountdata_bytes len %u\n", len);
  *(uint16_t*)calldata_bytes->ptr = (uint16_t)len;
  memcpy(calldata_bytes->ptr, accountdata_bytes->ptr, len);
  calldata_bytes->ptr+=2+len;

  len = transactions_bytes->ptr - transactions_bytes->startptr;
  printf("transactions_bytes len %u\n", len);
  *(uint16_t*)calldata_bytes->ptr = (uint16_t)len;
  memcpy(calldata_bytes->ptr, transactions_bytes->ptr, len);
  //calldata_bytes->ptr+=2+len;


  free(node_labels_bytes_naive->startptr);
  free(edge_label_lens_bytes->startptr);
  free(edge_labels_bytes->startptr);
  free(modified_subtree_idxs_bytes->startptr);
  free(hashes_bytes->startptr);
  free(addresses_bytes->startptr);
  free(accountdata_bytes->startptr);
  free(transactions_bytes->startptr);


  free(node_labels_bytes_naive);
  free(edge_label_lens_bytes);
  free(edge_labels_bytes);
  free(modified_subtree_idxs_bytes);
  free(addresses_bytes);
  free(accountdata_bytes);
  free(hashes_bytes);
  free(transactions_bytes);

  return calldata_bytes;

}


void generate_scout_test(uint64_t num_accounts_in_witness, uint64_t num_accounts_in_state, uint64_t num_transactions_to_existing, uint64_t num_transactions_to_new){

  FILE * fp;

  fp = fopen ("scout_test.txt","w");
  fprintf (fp, "blah\n");

  // randomly generate calldata
  struct bytes* calldata_bytes = generate_calldata(num_accounts_in_witness, num_accounts_in_state, num_transactions_to_existing, num_transactions_to_new);
  // print calldata
  for (int i=0; i<calldata_bytes->len; i++)
    fprintf(fp,"%02x",calldata_bytes->ptr[i]);

  fprintf (fp, "blah\n");
  fclose (fp);

}



/*
void test_get_bit(){
  uint32_t a = 0xf00ff00f;
  for (int i=0; i<16; i++){
    uint8_t bit = getbit((uint8_t*)&a, i);
    printf(" %u  ",bit);
    if (bit){
      //printf("1");
    }
    else {
      //printf("0");
    }
  }
}
*/
#endif


#if WASM
#else
int main(int argc, char** argv){

  init_num_bytes_and_bits();

  //_main();

  //struct Tree_node* test_witness = tree_generator(1, 1000000000);

  //test_get_bit();

  uint64_t num_accounts_in_witness = 1;
  uint64_t num_accounts_in_state = 80000000; //(uint64_t)1<<30;
  uint64_t num_transactions_to_existing = 0;
  uint64_t num_transactions_to_new = 0;
  struct bytes* calldata_bytes = generate_calldata(num_accounts_in_witness, num_accounts_in_state, num_transactions_to_existing, num_transactions_to_new);
  printf("calldata len: %i\n",calldata_bytes->len);

  return 0;

}
#endif
