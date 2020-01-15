"""
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
"""


"""
TODO:
 - signature verification
 - hash navigation, but this can be kept in the get_next_hash(), so can delay
 - problem: modified_subtree_indxs are adversierial:
   - soln: when merkleizing, check that modified_subtree_idxs are correct
   - soln: get_next_() functions check bounds
"""


import random   # for test generation


debug = 1

##############
# some globals

# This memory simulates C memory
memory = bytearray([0]*(2**20))     # more than enough

state_root = bytearray([])

# BYTE SIZES
# accounts
num_address_bits=256
num_accountdata_bits=64
num_accountdata_bytes = (num_accountdata_bits+7)//8
num_address_bytes = (num_address_bits+7)//8
# hashes
num_hash_bits=256
num_hash_bytes = (num_hash_bits+7)//8
num_hashes_bytes = 2
num_hash_byte_idx_bytes = 4
num_hash_navigation_bytes = num_address_bytes+num_hashes_bytes+num_hash_byte_idx_bytes
# signature
num_signature_bytes = 64
num_signature_bits = num_signature_bytes*8
num_message_bytes = 40
num_message_bits = num_message_bytes*8
# transactions: 
num_transaction_bytes=1+1+num_signature_bytes+num_address_bytes+num_accountdata_bytes
num_transaction_bits=num_transaction_bytes*8
# modified subtree idxs
num_modified_subtree_idxs_bytes = 11

# if change these consts later, must update
def init_num_bytes_and_bits():
  num_accountdata_bytes = (num_accountdata_bits+7)//8
  num_address_bytes = (num_address_bits+7)//8
  num_hash_bytes = (num_hash_bits+7)//8
  num_hash_navigation_bytes = num_address_bytes+num_hashes_bytes+num_hash_byte_idx_bytes
  num_signature_bits = num_signature_bytes*8
  num_message_bits = num_message_bytes*8
  num_transaction_bytes=1+1+num_signature_bytes+num_address_bytes+num_accountdata_bytes
  num_transaction_bits=num_transaction_bytes*8
  


# CALLDATA INFO
max_tree_depth=0

node_labels_startbyteidx = 0
node_labels_bytelen = 0
node_labels_idx = 0

edge_label_lengths_startbyteidx = 0
edge_label_lengths_bytelen = 0
edge_label_lengths_idx = 0

edge_labels_startbyteidx = 0
edge_labels_bytelen = 0
edge_labels_idx = 0

hashes_startbyteidx = 0
hashes_bytelen = 0
hashes_idx = 0

modified_subtree_idxs_startbyteidx = 0
modified_subtree_idxs_bytelen = 0
modified_subtree_idxs_byteidx = 0

addresses_startbyteidx = 0
addresses_bytelen = 0
addresses_idx = 0
addresses_byteidx = 0

accountdatas_startbyteidx = 0
accountdatas_bytelen = 0
accountdatas_idx = 0

transactions_startbyteidx = 0
transactions_bytelen = 0
transactions_idx = 0


# other values that could be arguments, but make leave them global for now
account_idx = 0
post_accountdatas_idx = 0
post_accountdatas_startbyteidx = 0
num_original_accounts = 0
num_modified_subtrees = 0

###############
# bit twiddling

"""
def get_bits_big_endian(dst, src, start_bit_idx, len_):
  #print("\nget_bits_big_endian(",dst,",","src",",",start_bit_idx,",",len_,")")
  # todo: assertions that start_bit_idx <= end_bit_idx and they are within src and dst
  # set up output bytes and indices
  num_output_bytes = (len_+7)//8 #(end_bit_idx-start_bit_idx+1+7)//8
  #print("num_output_bytes",num_output_bytes)
  # if we have no output bytes, then we are done
  if num_output_bytes == 0:
    return bytearray([])
  end_bit_idx = start_bit_idx + len_ - 1
  start_byte_idx = start_bit_idx // 8
  end_byte_idx = end_bit_idx // 8
  start_bit_offset = start_bit_idx % 8
  end_bit_offset = end_bit_idx % 8
  #print("start_byte_idx",start_byte_idx,"\nend_byte_idx",end_byte_idx,"\nstart_bit_offset",start_bit_offset,"\nend_bit_offset",end_bit_offset,"\nnum_output_bytes",num_output_bytes)
  #print("start_byte_idx",start_byte_idx,"end_byte_idx",end_byte_idx,"start_bit_offset",start_bit_offset,"end_bit_offset",end_bit_offset)
  # first the case when no shift is needed
  if start_bit_offset == 0:
    for i in range(num_output_bytes):
      dst[i] = src[i+start_byte_idx]
    num_bits_to_chop = 7-(end_bit_offset)
  else: # will left shift bytes
    # first the case of outputting one byte
    if num_output_bytes == 1:
      dst[0] = ((src[start_byte_idx]<<start_bit_offset)%256)
      if start_byte_idx < end_byte_idx: # get next byte
        dst[0] |= (src[end_byte_idx]>>(7-end_bit_offset))
      #num_bits_to_chop = (end_bit_idx-start_bit_idx+1)%8
    else:
      # left shift each byte before the last byte, and get remaining bits from next byte
      for i in range(num_output_bytes-1):
        dst[i] = ((src[start_byte_idx+i]<<start_bit_offset)%256) | (src[start_byte_idx+i+1]>>(8-start_bit_offset))
      # get last byte
      dst[num_output_bytes-1] = ((src[start_byte_idx+i+1]<<start_bit_offset)%256)
      if num_output_bytes == end_byte_idx - start_byte_idx:
        #print("num_output_bytes",num_output_bytes,"end_byte_idx",end_byte_idx,"len(src)",len(src))
        dst[num_output_bytes-1] |= (src[end_byte_idx]>>(8-start_bit_offset)%256)
    num_bits_to_chop = 7-(end_bit_idx-start_bit_idx)%8
  # chop off omitted part at end
  #print("num_bits_to_chop",num_bits_to_chop)
  dst[num_output_bytes-1] &= (0xff<<num_bits_to_chop)%256
  #print("  ","input",bytearray(src[:]).hex())
  #print("  ","output",bytearray(dst[:num_output_bytes]).hex())
  return dst
"""

def getbit(byteidx,bitidx):
  byte = memory[byteidx+bitidx//8]
  bit = (byte<<(bitidx%8))>>7
  return bit

def bitcompare(byteidx1, byteidx2, startbitidx, len_):
  for idx in range(startbitidx,startbitidx+len_):
    if getbit(byteidx1,idx) != getbit(byteidx2,idx):
      return idx
  return startbitidx+len_

######################################
# memory management, to make it like C

heap_byteidx = 0
def malloc(num_bytes):
  global memory
  global heap_byteidx
  print("malloc(",num_bytes,")")
  idx = heap_byteidx
  heap_byteidx += num_bytes
  return idx

def memcpy(dst_idx, src_idx, num_bytes):
  #print("memcpy(",dst_idx,",",src_idx,",",num_bytes,")")
  memory[dst_idx:dst_idx+num_bytes] = memory[src_idx:src_idx+num_bytes]

  






# 0) decode calldata

# calldata, arrays have a prefix with numbytes, see code for prefix sizes
#  max_tree_depth
#  node_labels
#  edge_label_lengths
#  edge_labels
#  hashes
#  addresses
#  accountdatas
#  transactions

def decode_calldata(memory_idx):
  global max_tree_depth
  global node_labels_startbyteidx
  global node_labels_bytelen
  global edge_label_lengths_startbyteidx
  global edge_label_lengths_bytelen
  global edge_labels_startbyteidx
  global edge_labels_bytelen
  global hashes_startbyteidx
  global hashes_bytelen
  global modified_subtree_idxs_startbyteidx
  global modified_subtree_idxs_bytelen
  global addresses_startbyteidx
  global addresses_bytelen
  global accountdatas_startbyteidx
  global accountdatas_bytelen
  global transactions_startbyteidx
  global transactions_bytelen
  global transactions_idx
  global memory
  # helper func
  def get_chunk(memidx, num_len_bytes):
    len_ = int.from_bytes(memory[memidx:memidx+num_len_bytes], byteorder="little")
    return memidx+num_len_bytes+len_, memidx+num_len_bytes, len_
  # parse
  max_tree_depth = memory[memory_idx]
  memory_idx+=1
  memory_idx, node_labels_startbyteidx, node_labels_bytelen                = get_chunk(memory_idx,2)
  memory_idx, edge_label_lengths_startbyteidx, edge_label_lengths_bytelen  = get_chunk(memory_idx,2)
  memory_idx, edge_labels_startbyteidx, edge_labels_bytelen                = get_chunk(memory_idx,2)
  memory_idx, modified_subtree_idxs_startbyteidx, modified_subtree_idxs_bytelen = get_chunk(memory_idx,2)
  memory_idx, hashes_startbyteidx, hashes_bytelen                          = get_chunk(memory_idx,4)
  memory_idx, addresses_startbyteidx, addresses_bytelen                    = get_chunk(memory_idx,2)
  memory_idx, accountdatas_startbyteidx, accountdatas_bytelen              = get_chunk(memory_idx,2)
  memory_idx, transactions_startbyteidx, transactions_bytelen              = get_chunk(memory_idx,2)







   


# 1) copy pre-accountdatas to post-accountdatas








# 2) build each modified subtree

# some getters
def get_next_node_label_bitpair():
  # this is used to build subtree and to merkleize pre&post
  global node_labels_idx
  global node_labels_startbyteidx
  #print("get_next_node_label_bitpair()",node_labels_startbyteidx,node_labels_idx)
  # get byte and bit
  byteidx = node_labels_idx // 4
  bitidx =  2 * (node_labels_idx % 4)
  # increment for next time
  node_labels_idx += 1
  # get two bits
  byte = memory[node_labels_startbyteidx+byteidx]
  byte = (byte << bitidx) % 256
  byte >>= 6
  return byte

def get_next_edge_label_length():
  # this is used to build subtree and to merkleize pre&post
  global edge_label_lengths_idx
  global edge_label_lengths_startbyteidx
  #print("get_next_edge_label_length()",edge_label_lengths_startbyteidx,edge_label_lengths_idx)
  len_ = memory[edge_label_lengths_startbyteidx+edge_label_lengths_idx]
  edge_label_lengths_idx += 1
  if len_ == 0:
     len_ = 256
  return len_

def get_next_address_byteidx():
  print()
  print()
  print("get_next_address_byteidx()")
  print()
  print()
  # this is used to build subtree and to merkleize pre&post
  global addresses_byteidx
  global num_address_bytes
  idx = addresses_byteidx
  addresses_byteidx += num_address_bytes
  #address = memory[addresses_byteidx:addresses_byteidx+num_address_bytes]
  return idx

next_modified_subtree_node_label_idx = 0
def get_next_modified_subtree_node_label_idx():
  # this is used to merkleize pre&post
  #print("get_next_modified_subtree_node_label_idx()")
  global modified_subtree_idxs_startbyteidx
  global modified_subtree_idxs_bytelen
  global modified_subtree_idxs_byteidx
  global next_modified_subtree_node_label_idx
  if modified_subtree_idxs_byteidx-modified_subtree_idxs_startbyteidx >= modified_subtree_idxs_bytelen:
    next_modified_subtree_node_label_idx = -1
  else:
    next_modified_subtree_node_label_idx = int.from_bytes(memory[modified_subtree_idxs_byteidx:modified_subtree_idxs_byteidx+2], byteorder="little")
    modified_subtree_idxs_byteidx += num_modified_subtree_idxs_bytes

def get_next_account_idx():
  # this is used to build subtree
  global account_idx
  account_idx += 1
  return account_idx

def get_next_postaccountdata_byteidx():
  # this is used to build subtree
  global post_accountdatas_idx
  global post_accountdatas_startbyteidx
  global num_accountdata_bytes
  byteidx = post_accountdatas_startbyteidx + post_accountdatas_idx*num_accountdata_bytes
  post_accountdatas_idx += 1
  #postaccountdata = int.from_bytes(postaccountdatas[post_accountdatas_idx:post_accountdatas_idx+num_accountdata_bytes], byteorder="little")
  return byteidx

def get_next_hash_byteidx():
  # this is used to build subtree and to merkleize pre&post
  global hashes_idx
  global hashes_startbyteidx
  hash_idx = hashes_idx
  hash_byteidx = hashes_startbyteidx + hash_idx*num_hash_bytes
  hashes_idx += 1
  return hash_byteidx




# tree node
num_treenode_bytes = 28
class Tree_node:
  # instantiate with TreeNode(malloc(num_treenode_bytes))
  """
  to read/write integer member, use .cast("I")[0]
  to read/write byte(s) member, use [0], [1], ..., [n-1], [:], etc
  """
  def __init__(self, startbyteidx):
    # raw bytes
    self.startbyteidx = startbyteidx
    self.mv = memoryview(memory)

    # parent+children/hash/address+data
    self.parent_byteidx                 = self.mv[self.startbyteidx:self.startbyteidx+4]
    self.left_or_address_byteidx        = self.mv[self.startbyteidx+4:self.startbyteidx+8]
    self.right_or_accountdata_byteidx       = self.mv[self.startbyteidx+8:self.startbyteidx+12]
    # node type
    self.node_type                      = self.mv[self.startbyteidx+12:self.startbyteidx+13]  # 0b00: leaf, 0b01: interior with only right child, 0b10: interior with only left child, 0b11: interior with both children
    # edge label
    self.edge_label_byteidx             = self.mv[self.startbyteidx+16:self.startbyteidx+20]
    self.edge_label_len                 = self.mv[self.startbyteidx+20:self.startbyteidx+24]
    self.edge_label_startbitidx           = self.mv[self.startbyteidx+24:self.startbyteidx+28]





debug_build_idx = 0
def build_tree_from_node_labels(edge_label_startbitidx, node):
  print("\n\n\nbuild_tree_from_node_labels(",edge_label_startbitidx,")")
  global num_address_bits
  global addresses_byteidx
  global num_address_bytes
  if debug:
    global debug_build_idx
    debug_build_idx+=1
    #print("  ",debug_build_idx,"build_tree_from_node_labels(",edge_label_startbitidx,")")
  node.edge_label_len.cast('I')[0] = 0
  node.edge_label_startbitidx.cast('I')[0] = edge_label_startbitidx
  node.edge_label_byteidx.cast('I')[0] = addresses_byteidx
  # get node label
  node_label = get_next_node_label_bitpair()
  if debug: print(debug_build_idx,"build_tree_from_node_labels()","node_label",node_label)
  # todo: assert we are within bound of label length, etc
  if node_label == 0b00:
    # either we are already at a leaf, or there is an edge label
    if edge_label_startbitidx == num_address_bits: # a leaf without an edge label, this is unlikely
      node.left_or_address_byteidx.cast('I')[0] = get_next_address_byteidx() 
      node.right_or_accountdata_byteidx.cast('I')[0] = get_next_postaccountdata_byteidx()
      node.node_type[0] = 0b00
      node.edge_label_byteidx.cast('I')[0] = node.left_or_address_byteidx.cast('I')[0]
      return
    else:
      # there is an edge label, get it
      print("there is an edge label len, get it")
      node.edge_label_len.cast('I')[0] = get_next_edge_label_length()
      print("edge_label_len, edge_label_startbitidx,edge_label_len",node.edge_label_len.cast('I')[0],node.edge_label_startbitidx.cast('I')[0])
      print("addresses_byteidx",addresses_byteidx)
      # either leaf or not leaf
      if debug: print("if leaf then true: ",node.edge_label_startbitidx.cast('I')[0] == num_address_bits-1, node.edge_label_startbitidx.cast('I')[0], num_address_bits-1)
      if node.edge_label_startbitidx.cast('I')[0] + node.edge_label_len.cast('I')[0] == num_address_bits:
        if debug: print(debug_build_idx,"build_tree_from_node_labels(",node.edge_label_startbitidx.cast('I')[0],")","found leaf")
        node.left_or_address_byteidx.cast('I')[0] = get_next_address_byteidx()
        node.right_or_accountdata_byteidx.cast('I')[0] = get_next_postaccountdata_byteidx()
        node.node_type[0] = 0b00
        return
      else:
        # not a leaf, get next node label and process it below
        node_label = get_next_node_label_bitpair()
        if debug: print(debug_build_idx,"build_tree_from_node_labels(",node.edge_label_startbitidx.cast('I')[0],")","node_label after 00",node_label)
  # this is an internal node, we already got the edge label if there was one
  print("ok",node.edge_label_startbitidx.cast('I')[0])
  node.node_type[0] = node_label
  if node_label == 0b11:
    # recurse left and right
    left_subtree = Tree_node(malloc(num_treenode_bytes))
    left_subtree.parent_byteidx.cast('I')[0] = node.startbyteidx
    node.left_or_address_byteidx.cast('I')[0] = left_subtree.startbyteidx
    if debug: print(debug_build_idx,"build_tree_from_node_labels(",edge_label_startbitidx,")","recursing left")
    build_tree_from_node_labels(node.edge_label_startbitidx.cast('I')[0]+node.edge_label_len.cast('I')[0]+1, left_subtree)
    right_subtree = Tree_node(malloc(num_treenode_bytes))
    right_subtree.parent_byteidx.cast('I')[0] = node.startbyteidx
    node.right_or_accountdata_byteidx.cast('I')[0] = right_subtree.startbyteidx
    if debug: print(debug_build_idx,"build_tree_from_node_labels(",edge_label_startbitidx,")","recursing right")
    build_tree_from_node_labels(node.edge_label_startbitidx.cast('I')[0]+node.edge_label_len.cast('I')[0]+1, right_subtree)
  elif node_label == 0b10:
    # recurse left, get hash for right
    left_subtree = Tree_node(malloc(num_treenode_bytes))
    left_subtree.parent_byteidx.cast('I')[0] = node.startbyteidx
    node.left_or_address_byteidx.cast('I')[0] = left_subtree.startbyteidx
    if debug: print(debug_build_idx,"build_tree_from_node_labels(",edge_label_startbitidx,")","recursing left")
    build_tree_from_node_labels(node.edge_label_startbitidx.cast('I')[0]+node.edge_label_len.cast('I')[0]+1, left_subtree)
    node.right_or_accountdata_byteidx.cast('I')[0] = get_next_hash_byteidx()
  elif node_label == 0b01:
    # get hash for left, recurse right
    node.left_or_address_byteidx.cast('I')[0] = get_next_hash_byteidx()
    right_subtree = Tree_node(malloc(num_treenode_bytes))
    right_subtree.parent_byteidx.cast('I')[0] = node.startbyteidx
    node.right_or_accountdata_byteidx.cast('I')[0] = right_subtree.startbyteidx
    if debug: print(debug_build_idx,"build_tree_from_node_labels(",edge_label_startbitidx,")","recursing right")
    build_tree_from_node_labels(node.edge_label_startbitidx.cast('I')[0]+node.edge_label_len.cast('I')[0]+1, right_subtree)


# build each subtree, put them in a global array
modified_subtrees_startbyteidx = 0
def build_modified_subtrees():
  print("build_modified_subtrees()")
  global modified_subtrees
  global modified_subtrees_startbyteidx
  modified_subtrees_startbyteidx = malloc(num_modified_subtrees*num_treenode_bytes)
  modified_subtrees_byteidx = modified_subtrees_startbyteidx
  global modified_subtree_idxs_bytelen
  global node_labels_idx
  global edge_label_lengths_idx
  global edge_labels_idx
  global hashes_idx
  global addresses_byteidx
  global post_accountdatas_idx
  modified_subtree_idxs_byteidx = modified_subtree_idxs_startbyteidx
  print("modified_subtree_idx",memory[modified_subtree_idxs_byteidx:modified_subtree_idxs_byteidx+11])
  for i in range(num_modified_subtrees):
    # get all relevant idxs
    # TODO: these idxs may be malicious, is it OK, or may have to rebuild addresses with a traversal and bittwiddling of address chunks. Should check indices during merkleization
    node_labels_idx           = int.from_bytes(memory[modified_subtree_idxs_byteidx:modified_subtree_idxs_byteidx+2], byteorder="little")
    edge_label_lengths_idx    = int.from_bytes(memory[modified_subtree_idxs_byteidx+2:modified_subtree_idxs_byteidx+4], byteorder="little")
    edge_labels_idx           = int.from_bytes(memory[modified_subtree_idxs_byteidx+4:modified_subtree_idxs_byteidx+6], byteorder="little")
    hashes_idx                = int.from_bytes(memory[modified_subtree_idxs_byteidx+6:modified_subtree_idxs_byteidx+8], byteorder="little")
    account_idx               = int.from_bytes(memory[modified_subtree_idxs_byteidx+8:modified_subtree_idxs_byteidx+10], byteorder="little")
    addresses_idx, post_accountdatas_idx = account_idx, account_idx
    addresses_byteidx = addresses_startbyteidx+addresses_idx*num_address_bytes
    address_prefix_bitidx     = int.from_bytes(memory[modified_subtree_idxs_byteidx+10:modified_subtree_idxs_byteidx+11], byteorder="little")
    if debug: print("build_modified_subtrees() iter  node_labels_idx",node_labels_idx,"edge_labels_lengths_idx",edge_label_lengths_idx,"edge_labels_idx",edge_labels_idx,"hashes_idx",hashes_idx,"account_idx",account_idx,"address_prefix_bitidx",address_prefix_bitidx)
    modified_subtree_idxs_byteidx += 11
    # create new node
    subtree_root_byteidx = modified_subtrees_byteidx
    subtree_root_node = Tree_node(subtree_root_byteidx)
    # build subtree of nodes
    build_tree_from_node_labels(address_prefix_bitidx, subtree_root_node)
    # iterate
    modified_subtrees_byteidx += num_treenode_bytes



  







# 3) process transactions 

def find_account_or_neighbor_or_error(node,address_byteidx):
  if debug: print("find_account_or_neighbor_or_error(", node.startbyteidx if node else node, address_byteidx,")")
  if node==None:
    return None, ""
  # if has edge label
  if node.edge_label_len.cast('I')[0]>0:
    #print("have edge label")
    # TODO: do we need to check against neighbor up to this point. Don't think so, since checked up to root of subtree, then checked each label, and left/right corresponded to 0/1. So no need I think.
    # check edge label against corresponding bits in address from signature
    if bitcompare(address_byteidx, node.edge_label_byteidx.cast('I')[0], node.edge_label_startbitidx.cast('I')[0], node.edge_label_len.cast('I')[0]) != node.edge_label_startbitidx.cast('I')[0]+node.edge_label_len.cast('I')[0]:
      return node.startbyteidx, "neighbor" # leaf not present, but have neighbor
    #corresponding_bits = bytearray([0]*((label_len+7)//8))
    #get_bits_big_endian(corresponding_bits, memory, 8*address_byteidx+label_endbitidx-label_len, label_len)
    #print(node.edge_label,corresponding_bits)
    #if node.edge_label[:(label_len+7)//8] != corresponding_bits:
    #  return node.startbyteidx, "neighbor" # leaf not present, but have neighbor
  # if leaf
  if node.node_type[0] == 0b00: # leaf; or, equivalently, label_endbitidx==num_address_bits-1
    # TODO: do we have to confirm leaf address matches sig address? maybe don't think that I have to compare leaf address to sig address, since couldn't get this far otherwise
    return node.startbyteidx, "account"
  # recurse left/right based on next bit
  nextbit = getbit(address_byteidx,node.edge_label_startbitidx.cast('I')[0]+node.edge_label_len.cast('I')[0])
  #print("nextbit",nextbit)
  #nextbit = bytearray([0])
  #get_bits_big_endian(nextbit, memory, address_byteidx*8+label_endbitidx,1)
  #print("nextbit",nextbit,"address_byteidx,label_endbitidx",address_byteidx,label_endbitidx)
  if nextbit == 0:
    if node.node_type[0] == 0b01:
      if debug: print("error, can't recurse left into hash")
      return None, ""
    if debug: print("recurse left",nextbit)
    return find_account_or_neighbor_or_error(Tree_node(node.left_or_address_byteidx.cast('I')[0]), address_byteidx)
  else:
    if node.node_type[0] == 0b10:
      if debug: print("error, can't recurse right into hash", node.node_type[0])
      return None, ""
    if debug: print("recurse right",nextbit)
    return find_account_or_neighbor_or_error(Tree_node(node.right_or_accountdata_byteidx.cast('I')[0]), address_byteidx)


def insert_leaf(neighbor,address_byteidx,accountdata_byteidx):
  print("insert_leaf(",neighbor.startbyteidx if neighbor else neighbor,",",address_byteidx,")")
  # if tree is empty, insert this address and accountdata and return
  # TODO: don't think there should be this possibility, since edge label lengths are unknown, so can't insert first node, but leave it for test generation
  if neighbor == None:
    new_leaf_byteidx = malloc(num_treenode_bytes)
    new_leaf = Tree_node(new_leaf_byteidx)
    new_leaf.node_type[0] = 0b00
    #address_byteidx = malloc(num_address_bytes)
    new_leaf.left_or_address_byteidx.cast('I')[0] = address_byteidx
    new_leaf.right_or_accountdata_byteidx.cast('I')[0] = accountdata_byteidx
    new_leaf.edge_label_startbitidx.cast('I')[0] = 0
    new_leaf.edge_label_len.cast('I')[0] = num_address_bits
    new_leaf.edge_label_byteidx.cast('I')[0] = address_byteidx
    return new_leaf
  # get bit where address and edge_label diverge
  i = bitcompare(address_byteidx, neighbor.edge_label_byteidx.cast('I')[0], neighbor.edge_label_startbitidx.cast('I')[0], neighbor.edge_label_len.cast('I')[0])
  addybit = getbit(address_byteidx,i)
  print("i",i)
  # insert node
  new_interior_node = Tree_node(malloc(num_treenode_bytes))
  new_interior_node.node_type[0] = 0b11
  new_leaf = Tree_node(malloc(num_treenode_bytes))
  new_leaf.node_type[0] = 0b00
  new_leaf.left_or_address_byteidx.cast('I')[0] = address_byteidx
  new_leaf.right_or_accountdata_byteidx.cast('I')[0] = accountdata_byteidx
  #print("new_interior_node and new_leaf", new_interior_node.startbyteidx, new_leaf.startbyteidx)
  # first take care of edge labels and lengths
  new_interior_node.edge_label_startbitidx.cast('I')[0] = neighbor.edge_label_startbitidx.cast('I')[0]
  new_interior_node.edge_label_len.cast('I')[0] = i-neighbor.edge_label_startbitidx.cast('I')[0]
  new_interior_node.edge_label_byteidx.cast('I')[0] = address_byteidx
  #print("new_interior_node.edge_label_endbitidx",new_interior_node.edge_label_endbitidx[0])
  new_leaf.edge_label_startbitidx.cast('I')[0] = i+1
  new_leaf.edge_label_len.cast('I')[0] = num_address_bits-(i+1)
  new_leaf.edge_label_byteidx.cast('I')[0] = address_byteidx
  neighbor.edge_label_len.cast('I')[0] -= i+1-neighbor.edge_label_startbitidx.cast('I')[0]
  neighbor.edge_label_startbitidx.cast('I')[0] = i+1
  # adjust parent and children pointers
  new_leaf.parent_byteidx.cast('I')[0] = new_interior_node.startbyteidx
  new_interior_node.parent_byteidx.cast('I')[0] = neighbor.parent_byteidx.cast('I')[0]
  if neighbor.parent_byteidx.cast('I')[0]:
    parent = Tree_node(neighbor.parent_byteidx.cast('I')[0])
    if parent.left_or_address_byteidx.cast('I')[0] == neighbor.startbyteidx:
      parent.left_or_address_byteidx.cast('I')[0] = new_interior_node.startbyteidx
    else:
      parent.right_or_accountdata_byteidx.cast('I')[0] = new_interior_node.startbyteidx
  neighbor.parent_byteidx.cast('I')[0] = new_interior_node.startbyteidx
  #print("new interior node has left and right children:")
  # two cases: diverge left or right
  #print("ok",addybit,new_interior_node)
  if addybit==0: # diverge right
    new_interior_node.right_or_accountdata_byteidx.cast('I')[0] = neighbor.startbyteidx
    new_interior_node.left_or_address_byteidx.cast('I')[0] = new_leaf.startbyteidx
  else: # diverge left
    new_interior_node.right_or_accountdata_byteidx.cast('I')[0] = new_leaf.startbyteidx
    new_interior_node.left_or_address_byteidx.cast('I')[0] = neighbor.startbyteidx
  return new_leaf


def delete_node(parent,side):
  pass


# this update code can be modified to do custom things, eg update accountdata, increment nonce, etc
num_balance_bytes = 6
num_nonce_bytes = 2
def update_accounts(to_address_byteidx, from_address_byteidx, to_data_byteidx, from_data_byteidx, data_byteidx):
  print("update_accounts(",to_address_byteidx, from_address_byteidx, to_data_byteidx, from_data_byteidx, data_byteidx,")")
  from_balance = int.from_bytes(memory[from_data_byteidx:from_data_byteidx+num_balance_bytes],"little")
  from_nonce = int.from_bytes(memory[from_data_byteidx+num_balance_bytes:from_data_byteidx+num_balance_bytes+num_nonce_bytes],"little")
  to_balance = int.from_bytes(memory[to_data_byteidx:to_data_byteidx+num_balance_bytes],"little")
  value = int.from_bytes(memory[data_byteidx:data_byteidx+num_balance_bytes],"little")
  nonce = int.from_bytes(memory[data_byteidx+num_balance_bytes:data_byteidx+num_balance_bytes+num_nonce_bytes],"little")
  print("from",memory[from_address_byteidx:from_address_byteidx+num_address_bytes].hex(), from_balance, nonce)
  print("to",memory[to_address_byteidx:to_address_byteidx+num_address_bytes].hex(), to_balance)
  print("value",value)
  if from_balance < value:
    return None     # error
  if nonce != from_nonce:
    return None     # error
  if from_data_byteidx == to_data_byteidx:
    return None     # error, can't send to self
  print("ok")
  from_balance -= value
  to_balance += value
  nonce += 1
  memory[to_data_byteidx:to_data_byteidx+num_balance_bytes] = to_balance.to_bytes(num_balance_bytes, "little")
  memory[from_data_byteidx:from_data_byteidx+num_balance_bytes] = from_balance.to_bytes(num_balance_bytes, "little")
  memory[from_data_byteidx+num_balance_bytes:from_data_byteidx+num_balance_bytes+num_nonce_bytes] = nonce.to_bytes(num_nonce_bytes, "little")
  print("from",memory[from_address_byteidx:from_address_byteidx+num_address_bytes].hex(), from_balance, nonce)
  print("to",memory[to_address_byteidx:to_address_byteidx+num_address_bytes].hex(), to_balance)
  print("todata",memory[to_data_byteidx:to_data_byteidx+num_balance_bytes+num_nonce_bytes].hex())
  print("fromdata",memory[from_data_byteidx:from_data_byteidx+num_balance_bytes+num_nonce_bytes].hex())


def process_transactions():
  print()
  print()
  print("process_transactions()")
  global transactions_startbyteidx
  global transactions_bytelen
  global memory
  global num_modified_subtrees
  global modified_subtrees
  txs_byteidx = transactions_startbyteidx
  txs_end_idx = transactions_startbyteidx+transactions_bytelen
  while txs_byteidx < txs_end_idx:
    print()
    print("transaction",txs_byteidx,"<", txs_end_idx)
    # parse tx
    from_idx = int.from_bytes(memory[txs_byteidx:txs_byteidx+1],"little")
    to_idx = int.from_bytes(memory[txs_byteidx+1:txs_byteidx+2],"little")
    txs_byteidx += 2
    signature = memory[txs_byteidx:txs_byteidx+num_signature_bytes]
    txs_byteidx += num_signature_bytes
    to_address_byteidx = txs_byteidx
    txs_byteidx += num_address_bytes
    data_byteidx = txs_byteidx #int.from_bytes(memory[txs_byteidx:txs_byteidx+num_accountdata_bytes],"little")
    txs_byteidx += num_accountdata_bytes
    # get accounts
    # from address and data
    from_address_byteidx = addresses_startbyteidx + from_idx*num_address_bytes
    from_data_byteidx = post_accountdatas_startbyteidx + from_idx*num_accountdata_bytes
    # to_data, note we have to_address from signature message
    if to_idx < num_original_accounts:
      to_data_byteidx = post_accountdatas_startbyteidx + to_idx*num_accountdata_bytes
    elif to_idx < num_original_accounts + num_modified_subtrees:
      # traverse tree until leaf, possibly inserting a new leaf
      print("must traverse tree.   to_idx>=num_orignal_accounts", to_idx, num_original_accounts)
      node = Tree_node(modified_subtrees_startbyteidx + num_treenode_bytes*(to_idx-num_original_accounts))
      print("node",node.startbyteidx)
      # check subtree address prefix against to address prefix
      if bitcompare(node.edge_label_byteidx.cast('I')[0], to_address_byteidx, node.edge_label_startbitidx.cast('I')[0], node.edge_label_len.cast('I')[0]) != node.edge_label_startbitidx.cast('I')[0]+node.edge_label_len.cast('I')[0]:
        print("error address prefix not equal")
        return None, "" # error
      # find leaf for this account or the neighbor which it branches from if there is a new node
      node_account_or_neighbor_byteidx,err = find_account_or_neighbor_or_error(node,to_address_byteidx)
      print("node_account_or_neighbor_byteidx,err",node_account_or_neighbor_byteidx,err)
      # if not a leaf, must insert leaf
      account = Tree_node(node_account_or_neighbor_byteidx)
      if err=="neighbor":
        account = insert_leaf(account,to_address_byteidx,malloc(num_accountdata_bytes))
      to_data_byteidx = account.right_or_accountdata_byteidx.cast('I')[0]
    else:
      print("error, to_idx is too large  to_idx",to_idx, "  num_original_accounts",num_original_accounts, "  num_modified_subtrees",num_modified_subtrees)
      return -1 # error, maybe should just continue
    # apply account updates
    update_accounts(to_address_byteidx, from_address_byteidx, to_data_byteidx, from_data_byteidx, data_byteidx)
  print("done with process_transactions()")
  print()
  print()









# 4) Merkleize pre and post root

num_hash_block_bytes = 1024
num_hash_state_bytes = 512
hash_state_byteidx = 0
hash_inplace_flag = 0
def init_hash():
  global hash_state_byteidx
  global num_hash_state_bytes
  global num_hash_block_bytes
  if hash_inplace_flag:
    hash_state_byteidx = malloc(num_hash_state_bytes)
  else:
    hash_state_byteidx = malloc(num_hash_state_bytes+num_hash_block_bytes)

num_hashblock_bytes = 2*num_hash_bytes+1
def hash_(dst_byteidx, src_byteidx, len_):
  print("hash(",dst_byteidx, src_byteidx, len_,")")
  global hash_state_byteidx
  global num_hash_state_bytes
  global num_hash_bytes
  global num_address_bytes
  print("to be hashed",memory[src_byteidx:src_byteidx+len_].hex())
  #print(num_hash_bytes)
  if len_==2*num_hash_bytes+1:
    print("ok1",memory[src_byteidx], memory[src_byteidx+num_hash_bytes])
    memory[dst_byteidx] = (memory[src_byteidx] + memory[src_byteidx+num_hash_bytes])%256
  else:
    print("ok2",memory[src_byteidx+num_address_bytes])
    memory[dst_byteidx] = memory[src_byteidx+num_address_bytes]
  print("result of hashing",memory[dst_byteidx])


max_hashstack_byteidx = 0

def merkleize_modifiable_subtree(hash_block_byteidx,node,recursion_depth):
  print(recursion_depth," "*recursion_depth+"merkleize_modifiable_subtree(",hash_block_byteidx,node.startbyteidx,recursion_depth,")")
  #print()
  #subtree = Subtree(modified_subtrees_startbyteidx)
  #print(node.startbyteidx,"subtree with address prefix of length ",subtree.address_prefix_len[0], bytearray(subtree.address_prefix.cast('B')[0:num_address_bytes]).hex())
  #print_subtree(subtree.root_byteidx.cast('I')[0],0,0)
  #print()
  if max_hashstack_byteidx <= hash_block_byteidx:
    print()
    print()
    print("error: bad max_tree_depth",max_tree_depth,max_hashstack_byteidx, hash_block_byteidx)
    print()
    print()
    return
  #if heap_byteidx < hash_block_byteidx + num_hashblock_bytes:
  #  malloc(hash_block_byteidx + num_hashblock_bytes - heap_byteidx)
  # zero workspace
  memory[hash_block_byteidx:hash_block_byteidx+num_hashblock_bytes] = bytearray([0]*num_hashblock_bytes)
  hash_len = num_hashblock_bytes
  print(recursion_depth," "*recursion_depth,node.node_type[0])
  if node.node_type[0]==0b00: # leaf
    memcpy(hash_block_byteidx, node.left_or_address_byteidx.cast('I')[0], num_address_bytes)
    memcpy(hash_block_byteidx+num_address_bytes, node.right_or_accountdata_byteidx.cast('I')[0], num_accountdata_bytes)
    memory[hash_block_byteidx+num_address_bytes+num_accountdata_bytes+1] = node.edge_label_len.cast("I")[0]
    #memcpy(hash_block_byteidx+num_address_bytes+num_accountdata_bytes+1, node.edge_label_len[0], 1)
    hash_len = num_address_bytes+num_accountdata_bytes+1
  elif node.node_type[0] == 0b01:
    memcpy(hash_block_byteidx, node.left_or_address_byteidx.cast('I')[0], num_hash_bytes)
    merkleize_modifiable_subtree(hash_block_byteidx+num_hashblock_bytes, Tree_node(node.right_or_accountdata_byteidx.cast('I')[0]), recursion_depth+1)
    memcpy(hash_block_byteidx+num_hash_bytes, hash_block_byteidx+num_hashblock_bytes, num_hash_bytes)
    #memcpy(hash_block_byteidx+num_hash_bytes+1, node.edge_label_len[0], 1)
    memory[hash_block_byteidx+2*num_hash_bytes+1] = node.edge_label_len.cast("I")[0]
  elif node.node_type[0] == 0b10:
    merkleize_modifiable_subtree(hash_block_byteidx+num_hashblock_bytes, Tree_node(node.left_or_address_byteidx.cast('I')[0]), recursion_depth+1)
    memcpy(hash_block_byteidx, hash_block_byteidx+num_hashblock_bytes, num_hash_bytes)
    memcpy(hash_block_byteidx+num_hash_bytes, node.right_or_accountdata_byteidx.cast('I')[0], num_hash_bytes)
    #memcpy(hash_block_byteidx+num_hash_bytes+1, node.edge_label_len[0], 1)
    #print("ok",node.edge_label_startbitidx.cast('I')[0], node.edge_label_len.cast('I')[0])
    memory[hash_block_byteidx+2*num_hash_bytes+1] = node.edge_label_len.cast("I")[0]
  elif node.node_type[0] == 0b11:
    merkleize_modifiable_subtree(hash_block_byteidx+num_hashblock_bytes, Tree_node(node.left_or_address_byteidx.cast('I')[0]), recursion_depth+1)
    memcpy(hash_block_byteidx, hash_block_byteidx+num_hashblock_bytes, num_hash_bytes)
    node_test = Tree_node(node.right_or_accountdata_byteidx.cast('I')[0])
    merkleize_modifiable_subtree(hash_block_byteidx+num_hashblock_bytes, Tree_node(node.right_or_accountdata_byteidx.cast('I')[0]), recursion_depth+1)
    memcpy(hash_block_byteidx+num_hash_bytes, hash_block_byteidx+num_hashblock_bytes, num_hash_bytes)
    #memcpy(hash_block_byteidx+num_hash_bytes+1, node.edge_label_len[0], 1)
    memory[hash_block_byteidx+2*num_hash_bytes+1] = node.edge_label_len.cast("I")[0]
  #print(recursion_depth," "*recursion_depth,"hashing")
  hash_(hash_block_byteidx, hash_block_byteidx, hash_len)


modifiable_subtree_idx = 0
def merkleize_pre_and_post(hash_block_byteidx,depth,recursion_depth,post_hash_flag):
  print(recursion_depth," "*recursion_depth+"merkleize_pre_and_post(",hash_block_byteidx,depth,recursion_depth,post_hash_flag,")")
  global memory
  global modifiable_subtree_idx
  global node_labels_idx
  global account_idx
  num_workspace_bytes = num_hashblock_bytes + post_hash_flag*num_hashblock_bytes
  if max_hashstack_byteidx <= hash_block_byteidx:
    print()
    print()
    print("error: bad max_tree_depth",max_tree_depth,max_hashstack_byteidx, hash_block_byteidx)
    print()
    print()
    return
  #if heap_byteidx < hash_block_byteidx + num_workspace_bytes:
  #  malloc(hash_block_byteidx + num_workspace_bytes - heap_byteidx)
  # zero workspace
  memory[hash_block_byteidx:hash_block_byteidx+num_workspace_bytes] = bytearray([0]*num_workspace_bytes)
  hash_len = num_hashblock_bytes
  edge_label_len = 0
  #print(recursion_depth," "*recursion_depth+"node_labels_idx",node_labels_idx,"next_modifiable_subtree_node_label_idx",next_modified_subtree_node_label_idx)
  if node_labels_idx == next_modified_subtree_node_label_idx:
    post_hash_flag = 0
    node = Tree_node(modified_subtrees_startbyteidx + modifiable_subtree_idx*num_treenode_bytes)
    print(recursion_depth," "*recursion_depth+"merklizing modifiable_subtree")
    print()
    merkleize_modifiable_subtree(hash_block_byteidx+num_hashblock_bytes, node, recursion_depth)
    print()
    print(recursion_depth," "*recursion_depth+"returned from merkleize_modifiable_subtree with hash")
    # set up for next modifiable subtree
    modifiable_subtree_idx+=1
    get_next_modified_subtree_node_label_idx()
  node_label = get_next_node_label_bitpair()
  #print(recursion_depth," "*recursion_depth+"node_label ",node_label)
  if node_label == 0b00:
    print(recursion_depth," "*recursion_depth+"node_label == 0b00 - edge label or leaf")
    #print(recursion_depth," "*recursion_depth+"depth",depth,"num_address_bis",num_address_bits)
    if depth==num_address_bits: # leaf with no edge label, this is rare
      # put address, prestate accountdata, and edge_label_len=0
      memcpy(hash_block_byteidx, addresses_startbyteidx+account_idx*num_address_bytes,num_address_bytes)
      memcpy(hash_block_byteidx+num_address_bytes, accountdatas_startbyteidx+account_idx*num_accountdata_bytes,num_accountdata_bytes)
      #address = memory[addresses_startbyteidx+account_idx*num_address_bytes:addresses_startbyteidx+(account_idx+1)*num_address_bytes]
      #pre_accountdata = memory[accountdatas_startbyteidx+account_idx*num_accountdata_bytes:accountdatas_startbyteidx+(account_idx+1)*num_accountdata_bytes]
      #pre_hash = hash_(address+pre_accountdata)
      if post_hash_flag==1:
        # put address, poststate accountdata, and edge_label_len=0
        memcpy(hash_block_byteidx+num_hashblock_bytes, addresses_startbyteidx+account_idx*num_address_bytes,num_address_bytes)
        memcpy(hash_block_byteidx+num_hashblock_bytes+num_address_bytes, post_accountdatas_startbyteidx+account_idx*num_accountdata_bytes,num_accountdata_bytes)
        #post_accountdata = postaccountdatas[account_idx*num_accountdata_bytes:account_idx*num_accountdata_bytes+num_accountdata_bytes]
        #post_hash = hash_(address+post_accountdata+bytearray([0]))
      account_idx = get_next_account_idx()
      #print(recursion_depth," "*recursion_depth+"1pre_hash:", pre_hash)
      #print(recursion_depth," "*recursion_depth+"post_hash:", post_hash)
      #print()
      #return pre_hash,post_hash
      hash_len = num_address_bytes+num_accountdata_bytes+1
    else: 
      edge_label_len = get_next_edge_label_length()
      depth += edge_label_len
      print(recursion_depth," "*recursion_depth+"edge_label_len",edge_label_len, "  depth",depth)
      #print(recursion_depth," "*recursion_depth+"    edge_label_len",edge_label_len)
      #print(recursion_depth," "*recursion_depth+depth,num_address_bits-1)
      if depth==num_address_bits: # a leaf with an edge label
        print(recursion_depth," "*recursion_depth+"its a leaf with an edge label")
        memcpy(hash_block_byteidx, addresses_startbyteidx+account_idx*num_address_bytes,num_address_bytes)
        memcpy(hash_block_byteidx+num_address_bytes, accountdatas_startbyteidx+account_idx*num_accountdata_bytes,num_accountdata_bytes)
        memory[hash_block_byteidx+num_address_bytes+num_accountdata_bytes+1] = edge_label_len
        if post_hash_flag==1:
        # put address, poststate accountdata, and edge_label_len=0
          memcpy(hash_block_byteidx+num_hashblock_bytes, addresses_startbyteidx+account_idx*num_address_bytes,num_address_bytes)
          memcpy(hash_block_byteidx+num_hashblock_bytes+num_address_bytes, post_accountdatas_startbyteidx+account_idx*num_accountdata_bytes,num_accountdata_bytes)
          memory[hash_block_byteidx+num_hashblock_bytes+num_address_bytes+num_accountdata_bytes+1] = edge_label_len
        account_idx = get_next_account_idx()
        #print(recursion_depth," "*recursion_depth+"2pre_hash:", pre_hash)
        #print(recursion_depth," "*recursion_depth+"post_hash:", post_hash)
        #print()
        #return pre_hash,post_hash
        hash_len = num_address_bytes+num_accountdata_bytes+1
      else: # not a leaf, get next node label and process it below
        node_label = get_next_node_label_bitpair()
    #print(recursion_depth," "*recursion_depth+"node_label after 00",node_label)
  if node_label == 0b01:
    print(recursion_depth," "*recursion_depth+"node_label == 0b01")
    #print(recursion_depth," "*recursion_depth+"ok 01")
    # get left witness hash for prestate
    left_hash_byteidx = get_next_hash_byteidx()
    memcpy(hash_block_byteidx, left_hash_byteidx, num_hash_bytes)
    if post_hash_flag==1:
      memcpy(hash_block_byteidx+num_hashblock_bytes, left_hash_byteidx, num_hash_bytes)
    # compute and get right hash
    right_hash_byteidx = hash_block_byteidx+num_workspace_bytes
    merkleize_pre_and_post(right_hash_byteidx,depth+1,recursion_depth+1,post_hash_flag)
    memcpy(hash_block_byteidx+num_hash_bytes, right_hash_byteidx, num_hash_bytes)
    if post_hash_flag==1:
      memcpy(hash_block_byteidx+num_hashblock_bytes+num_hash_bytes, right_hash_byteidx+num_hashblock_bytes, num_hash_bytes)
    #print(recursion_depth," "*recursion_depth+"3pre_hash:", pre_hash)
    #print(recursion_depth," "*recursion_depth+"post_hash:", post_hash)
    #print()
  elif node_label == 0b10:
    print(recursion_depth," "*recursion_depth+"node_label == 0b10")
    # compute and get left hash
    left_hash_byteidx = hash_block_byteidx+num_workspace_bytes
    merkleize_pre_and_post(left_hash_byteidx,depth+1,recursion_depth+1,post_hash_flag)
    memcpy(hash_block_byteidx, left_hash_byteidx, num_hash_bytes)
    if post_hash_flag==1:
      memcpy(hash_block_byteidx+num_hashblock_bytes, left_hash_byteidx+num_hashblock_bytes, num_hash_bytes)
    # get right witness hash for prestate
    right_hash_byteidx = get_next_hash_byteidx()
    memcpy(hash_block_byteidx+num_hash_bytes, right_hash_byteidx, num_hash_bytes)
    if post_hash_flag==1:
      memcpy(hash_block_byteidx+num_hashblock_bytes+num_hash_bytes, right_hash_byteidx, num_hash_bytes)
  elif node_label == 0b11:
    print(recursion_depth," "*recursion_depth+"node_label == 0b11")
    # compute and get left hash
    left_hash_byteidx = hash_block_byteidx+num_workspace_bytes
    merkleize_pre_and_post(left_hash_byteidx,depth+1,recursion_depth+1,post_hash_flag)
    memcpy(hash_block_byteidx, left_hash_byteidx, num_hash_bytes)
    if post_hash_flag==1:
      memcpy(hash_block_byteidx+num_hashblock_bytes, left_hash_byteidx+num_hashblock_bytes, num_hash_bytes)
    # compute and get right hash
    right_hash_byteidx = hash_block_byteidx+num_workspace_bytes
    merkleize_pre_and_post(right_hash_byteidx,depth+1,recursion_depth+1,post_hash_flag)
    memcpy(hash_block_byteidx+num_hash_bytes, right_hash_byteidx, num_hash_bytes)
    if post_hash_flag==1:
      memcpy(hash_block_byteidx+num_hashblock_bytes+num_hash_bytes, right_hash_byteidx+num_hashblock_bytes, num_hash_bytes)
  hash_(hash_block_byteidx, hash_block_byteidx, hash_len)
  if post_hash_flag==1:
    hash_(hash_block_byteidx+num_hashblock_bytes, hash_block_byteidx+num_hashblock_bytes, hash_len)





def init_merkleization_and_merkleize():
  global node_labels_idx
  global edge_labels_startbyteidx
  global edge_label_lengths_idx
  global hashes_idx
  global modified_subtree_idxs_startbyteidx
  global modified_subtree_idxs_byteidx
  global addresses_startbyteidx
  global accountdatas_startbyteidx
  global transactions_startbyteidx
  global max_hashstack_byteidx
  # init stuff
  node_labels_idx = 0
  edge_label_lengths_idx = 0
  edge_labels_idx = edge_labels_startbyteidx
  hashes_idx = 0
  addresses_byteidx = addresses_startbyteidx
  accountdatas_idx = accountdatas_startbyteidx
  transactions_idx = transactions_startbyteidx
  modified_subtree_idxs_byteidx = modified_subtree_idxs_startbyteidx
  get_next_modified_subtree_node_label_idx()
  init_hash()
  # other globals
  global modifiable_subtree_idx
  modifiable_subtree_idx = 0
  global account_idx
  account_idx = 0
  # init stack
  stack_byteidx = malloc((max_tree_depth+1)*num_hashblock_bytes)
  max_hashstack_byteidx = stack_byteidx+(max_tree_depth+1)*2*num_hashblock_bytes
  # finally, compute new and old hashes
  merkleize_pre_and_post(stack_byteidx,0,0,1)
  return stack_byteidx












def main(calldata):
  global post_accountdatas_startbyteidx
  global num_original_accounts
  global modified_subtrees
  global memory
  global state_root
  global max_tree_depth

  init_num_bytes_and_bits()

  print("calldata")
  print(calldata)

  # 0) decode calldata
  malloc(len(calldata))
  memory[:len(calldata)] = calldata[:]
  if debug:
    print("0) decode calldata")
  calldata_startbyteidx = 0
  decode_calldata(calldata_startbyteidx)
  if 1:
    print("max_tree_depth",max_tree_depth)
    print("node_labels idxs",node_labels_startbyteidx, node_labels_bytelen)
    print("edge_label_lengths idx",edge_label_lengths_startbyteidx, edge_label_lengths_bytelen)
    print("edge_labels idxs",edge_labels_startbyteidx, edge_labels_bytelen)
    print("modified_subtrees idxs",modified_subtree_idxs_startbyteidx, modified_subtree_idxs_bytelen)
    print("hashes idxs",hashes_startbyteidx, hashes_bytelen)
    print("addresses idxs",addresses_startbyteidx, addresses_bytelen)
    print("accountdatas idxs",accountdatas_startbyteidx, accountdatas_bytelen)
    print("transactions idxs",transactions_startbyteidx, transactions_bytelen)


  # 1) copy pre-accountdatas to post-accountdatas
  if debug:
    print()
    print("1) copy pre-accountdatas to post-accountdatas")
  post_accountdatas_startbyteidx = malloc(accountdatas_bytelen)
  memcpy(post_accountdatas_startbyteidx, accountdatas_startbyteidx, accountdatas_bytelen)
  num_original_accounts = accountdatas_bytelen//num_accountdata_bytes
  print("num_original_accounts, accountdatas_bytelen, num_accountdata_bytes",num_original_accounts, accountdatas_bytelen, num_accountdata_bytes)


  # 2) build each modified subtree
  if debug:
    print()
    print("2) build each modified subtree")
  if debug:
    global debug_build_idx
    debug_build_idx = 0
  global num_modified_subtrees
  num_modified_subtrees = modified_subtree_idxs_bytelen//11
  build_modified_subtrees()
  # print them
  if debug:
    global modified_subtrees_startbyteidx
    global num_subtree_bytes
    print()
    print("printing subtrees")
    modified_subtrees_byteidx = modified_subtrees_startbyteidx
    for i in range(num_modified_subtrees):
      node = Tree_node(modified_subtrees_byteidx)
      print()
      print("subtree with address prefix of length ",node.edge_label_len.cast('I')[0], memory[node.edge_label_byteidx.cast('I')[0]:node.edge_label_byteidx.cast('I')[0]+num_address_bytes].hex())
      print_subtree(node.startbyteidx,0,0)
      modified_subtrees_byteidx += num_treenode_bytes


  # 3) process transactions 
  if debug:
    print()
    print("3) process transactions")
  process_transactions()
  if debug:
    # print subtrees
    global print_idx
    print_idx = 0
    print()
    print("printing subtrees")
    modified_subtrees_byteidx = modified_subtrees_startbyteidx
    for i in range(num_modified_subtrees):
      node = Tree_node(modified_subtrees_byteidx)
      print()
      print("subtree with address prefix of length ",node.edge_label_startbitidx.cast('I')[0], memory[node.edge_label_byteidx.cast('I')[0]:node.edge_label_byteidx.cast('I')[0]+num_address_bytes].hex())
      print_subtree(node.startbyteidx,0,0)
      modified_subtrees_byteidx += num_treenode_bytes
    # print preaccountdatas
    print()
    print("preaccountdatas")
    for i in range(num_original_accounts):
      print(int.from_bytes(memory[accountdatas_startbyteidx+i*num_accountdata_bytes:accountdatas_startbyteidx+i*num_accountdata_bytes+num_balance_bytes], byteorder="little"))
    print()
    # print postaccountdatas
    print()
    print("postaccountdatas")
    for i in range(num_original_accounts):
      print(int.from_bytes(memory[post_accountdatas_startbyteidx+i*num_accountdata_bytes:post_accountdatas_startbyteidx+i*num_accountdata_bytes+num_balance_bytes], byteorder="little"))
      #print(int.from_bytes(memory[accountdatas_startbyteidx+i*num_accountdata_bytes:accountdatas_startbyteidx+i*num_accountdata_bytes+num_accountdata_bytes], byteorder="little"))
    print()


  # 4) Merkleize pre and post root
  if debug:
    print()
    print("4) Merkleize pre and post root")
  hash_block_byteidx = init_merkleization_and_merkleize()
  

  print("preroot:",memory[hash_block_byteidx:hash_block_byteidx+num_hash_bytes].hex())
  print("postroot:",memory[hash_block_byteidx+num_hashblock_bytes:hash_block_byteidx+num_hashblock_bytes+num_hash_bytes].hex())

  """
  # 5) check if computed_old_root equas old_root
  if debug:
    print()
    print("5) check if computed_old_root equas old_root")
  if computed_old_root == state_root:
    state_root = new_root

  return computed_old_root, new_root
  """











####################################
# code before here is the contract #
#  code below here is for testing  #
####################################









#######################
# helper to print stuff

print_idx = 0

def bytearray_to_hex(memory,startbyteidx,len_):
  return memory[startbyteidx:startbyteidx+len_].hex()

def print_node(node,indent):
  print("print_node(",node,",",indent,")")
  print("\n" + " "*indent + str(indent) + " startbyteidx "             + str(node.startbyteidx) + \
        "\n" + " "*indent + str(indent) + " parent_byteidx "           + str(node.parent_byteidx.cast('I')[0]) + \
        "\n" + " "*indent + str(indent) + " left_or_address_byteidx "  + str(node.left_or_address_byteidx.cast('I')[0]) + \
        "\n" + " "*indent + str(indent) + " right_or_accountdata_byteidx " + str(node.right_or_accountdata_byteidx.cast('I')[0]) + \
        "\n" + " "*indent + str(indent) + " node_type "                + str(node.node_type[0]) + \
        "\n" + " "*indent + str(indent) + " edge_label_startbitidx "     + str(node.edge_label_startbitidx.cast('I')[0]) + \
        "\n" + " "*indent + str(indent) + " edge_label_len "           + str(node.edge_label_len.cast('I')[0]) + \
        "\n" + " "*indent + str(indent) + " edge_label_byteidx "       + str(node.edge_label_byteidx[0]) + \
        "\n" + " "*indent + str(indent) + " edge_label "               + bytearray_to_hex(memory, node.edge_label_byteidx.cast('I')[0], num_address_bytes ) )
  if node.node_type[0]==0:
    print(       " "*indent + str(indent) + " address " + memory[node.left_or_address_byteidx.cast('I')[0]:node.left_or_address_byteidx.cast('I')[0]+num_address_bytes].hex())
    print(       " "*indent + str(indent) + " accountdata " + memory[node.right_or_accountdata_byteidx.cast('I')[0]:node.right_or_accountdata_byteidx.cast('I')[0]+num_accountdata_bytes].hex())
  if node.node_type[0]==1:
    print(       " "*indent + str(indent) + " left hash " + memory[node.left_or_address_byteidx.cast('I')[0]:node.left_or_address_byteidx.cast('I')[0]+num_hash_bytes].hex())
  if node.node_type[0]==2:
    print(       " "*indent + str(indent) + " right hash " + memory[node.right_or_accountdata_byteidx.cast('I')[0]:node.right_or_accountdata_byteidx.cast('I')[0]+num_hash_bytes].hex())

def print_subtree(node_byteidx,depth,indent):
  global print_idx
  if debug: print("print_subtree(",node_byteidx,",",depth,",",indent,")")
  print_idx += 1
  node = Tree_node(node_byteidx)
  depth = node.edge_label_startbitidx.cast('I')[0]+node.edge_label_len.cast('I')[0]
  print_node(node,indent)
  if node.node_type[0] in {2,3}:  # recurse left
    print_subtree(node.left_or_address_byteidx.cast('I')[0],depth,indent+1)
  if node.node_type[0] in {1,3}:  # recurse right
    print_subtree(node.right_or_accountdata_byteidx.cast('I')[0],depth,indent+1)


def print_subtree_addresses(node_byteidx,depth,indent):
  #print("print_subtree_addresses()")
  global print_idx
  print_idx += 1
  node = Tree_node(node_byteidx)
  depth = node.edge_label_startbitidx.cast('I')[0]+node.edge_label_len.cast('I')[0]+1
  if node.node_type[0]==0b00:
    address = memory[node.left_or_address_byteidx.cast('I')[0]: node.left_or_address_byteidx.cast('I')[0]+num_address_bytes]
    print(print_idx," "*indent,address.hex())
  if node.node_type[0] in {2,3}:  # recurse left
    print_subtree_addresses(node.left_or_address_byteidx.cast('I')[0],depth,indent+1)
  if node.node_type[0] in {1,3}:  # recurse right
    print_subtree_addresses(node.right_or_accountdata_byteidx.cast('I')[0],depth,indent+1)





################################
# Tests of general functionality 

# THIS IS OLD
def test_insert_leaves():
  global print_idx
  accountdata = bytearray([0]*num_accountdata_bytes)
  tree = None

  #addresses = [bin2bytes('0010'.ljust(num_address_bits,'0')), \
  #             bin2bytes('1010'.ljust(num_address_bits,'0')), \
  #             bin2bytes('1111'.ljust(num_address_bits,'0'))]
  addresses = [ bin2bytes('00110011'.ljust(num_address_bits,'0')),\
                bin2bytes('00111011'.ljust(num_address_bits,'0')),\
                bin2bytes('10111011'.ljust(num_address_bits,'0'))
               ]
  for address in addresses:
    print()
    print("inserting address",address.hex(),"accountdata",accountdata)
    neighbor,err = find_account_or_neighbor(tree,address,0)
    if err == "":
      print("tree was empty")
      tree = insert_leaf(neighbor,address,accountdata)
    elif err=="neighbor":
      print("found neighbor",neighbor,"must insert leaf")
      # must insert next to neighbor
      insert_leaf(neighbor,address,accountdata)
    elif err=="account":
      print("this account is already present")
    while tree.parent:
      tree=tree.parent
    print("done inserting address",address,"accountdata",accountdata)
    # print tree
    print_idx = 0
    print_subtree(tree,0,0)



def test_find_and_insert(idx):
  tree = None
  accountdata_byteidx = malloc(num_accountdata_bytes)
  memory[accountdata_byteidx] = 100
  addresses = []
  if idx == 0:
    addresses = ['a24eaaf2265062570012569bce29bf73802b1cc4e37c8e52fd9bba9c1334e4e1', 'b4ed0fc3b4075bd62921836b8e32013040fde20544d13eeffad5c4383a7bbccb', 'f5983b4b07bef728caf161c436c36517be3dfc91dee499b2a2e93034a0a43e62']
    #addresses = ['a24eaaf2265062570012569bce29bf73802b1cc4e37c8e52fd9bba9c1334e4e1', 'b4ed0fc3b4075bd62921836b8e32013040fde20544d13eeffad5c4383a7bbccb', 'f5983b4b07bef728caf161c436c36517be3dfc91dee499b2a2e93034a0a43e62','0000000000000000000000000000000000000000000000000000000000000000']
    #addresses = ['0000000000000000000000000000000000000000000000000000000000000000','a24eaaf2265062570012569bce29bf73802b1cc4e37c8e52fd9bba9c1334e4e1', 'b4ed0fc3b4075bd62921836b8e32013040fde20544d13eeffad5c4383a7bbccb', 'f5983b4b07bef728caf161c436c36517be3dfc91dee499b2a2e93034a0a43e62']
  elif idx == 1:
    addresses = ['006f4fbbe815b1f24d0fb918e01d84ae36c981ea2feb31f2a0dfdde60c1eafb1', 'c59c32187761bdda3d303e2c9a7832f2e43520292c24da43d6fc89e63c62caf0', '2f21cedf4a4be30b8ea21d762226991373adb443c21243d941f9378dfa05faa0']
  elif idx == 2:
    addresses = ['130d7941e164c7780694936ef61f1a67b78943052787cb0238e19b09fb0b3d16','aa7466fa5168be169eef6511af50caf95f800e2ca45e03175df9a2078626ba01','c7e5a7d17fe3e2050c067a0418249473ea7c2c3b89c6824e2b569222293cd186']
  elif idx == 3:
    addresses = ['77b071a033b60109319dac6b0b9296e6de9610cb29cd90007125bb2fa3564100','80d2f28782ba5b1818f08632b3514ef6e7b163efacac43806e5be3b6c2d99d0e','5bcb5a5bd43e28c9a43a3f0d67fb9b8d45a619f078570665c1e206d318210848']

  tree = None

  for address in addresses:
    address_byteidx = malloc(num_address_bytes)
    memory[address_byteidx:address_byteidx+num_address_bytes] = bytes.fromhex(address)
    print()
    print()
    print()
    print("inserting",memory[address_byteidx:address_byteidx+num_address_bytes].hex())
    found_node_byteidx,err = find_account_or_neighbor_or_error(tree,address_byteidx)
    print("back to main",found_node_byteidx,err)
    if found_node_byteidx:
      found_node = Tree_node(found_node_byteidx)
    else:
      found_node = None
    tree = insert_leaf(found_node,address_byteidx,accountdata_byteidx)
    
    while tree.parent_byteidx.cast('I')[0]:
      tmp_node = Tree_node(tree.parent_byteidx.cast('I')[0])
      tree = Tree_node(tmp_node.startbyteidx)

    print_idx = 0
    print_subtree(tree.startbyteidx,0,0)

  print_idx = 0
  print_subtree_addresses(tree.startbyteidx,0,0)





#########################
# Test witness generators


# helpers to write tests

def int2bytes(int_,len_):
  return int_.to_bytes(len_, byteorder='little')

def bin2bytes(binstr):
  binstr = binstr.ljust(8*((len(binstr)+7) // 8), '0')
  bytes_ = int(binstr, 2).to_bytes((len(binstr)+7) // 8, byteorder='big')
  return bytes_

def bytes2bin(bytes_):
  binstr = ''
  for b in bytes_:
    binstr += bin(b)[2:].zfill(8)
  return binstr

def encode_chunk(chunk, num_len_bytes):
  chunk_encoded = len(chunk).to_bytes(num_len_bytes, byteorder='little') + chunk
  #print("encoding chunk:",chunk, "to", chunk_encoded)
  return chunk_encoded






def test_handwritten1():
  global num_address_bits
  global num_accountdata_bits
  global num_hash_bits
  """
  11
   l 10
    l 00 10
     l 00
     r h
    r h
   r 11
    l 00
    r 00 01
     l h
     r 00


    0/   \1
   0/   0/ \1
   1|   1| |1
   0/   0|  \1
  """
  # node labels
  node_labels = bin2bytes('11''10''00''10''00''11''00''00''01''00')
  # edge label lengths, where 0 == 256
  edge_label_lengths = bytearray([1,num_address_bits-4,num_address_bits-2,1,num_address_bits-4])
  # edge labels
  edge_labels = bytearray([])
  # modified_subtree_idxs: node label idx, edge label lengths idx, edge labels idx, hashes idx, accounts idx, depth
  modified_subtree_idxs = int2bytes(1,2) + int2bytes(0,2) + int2bytes(0,2) + int2bytes(0,2) + int2bytes(0,2) + int2bytes(1,1)
  # hashes
  hashes = bin2bytes( \
          '00000001'.ljust(num_hash_bits,'0') + \
          '00000010'.ljust(num_hash_bits,'0') + \
          '00000011'.ljust(num_hash_bits,'0') )
  # addresses
  addresses = bin2bytes( \
         '0010'.ljust(num_address_bits,'0') + \
         '1010'.ljust(num_address_bits,'0') + \
         '1111'.ljust(num_address_bits,'0'))
  # accountdatas 
  accountdatas = \
          (2).to_bytes(num_accountdata_bytes,'little') + \
          (5).to_bytes(num_accountdata_bytes,'little') + \
          (7).to_bytes(num_accountdata_bytes,'little')
  # transactions: sender idx, receiver idx, signature, message (receiver address, value)
  #   0010.. sends 1 to 1111..    1010.. sends 3 to 0000.. 
  transactions = \
      bytearray([0,2]) + bin2bytes('0'.ljust(num_signature_bits,'0') + '1111'.ljust(num_address_bits,'0')) + int2bytes(1,num_accountdata_bytes) + \
      bytearray([1,3]) + bin2bytes('0'.ljust(num_signature_bits,'0') + '0000'.ljust(num_address_bits,'0')) + int2bytes(3,num_accountdata_bytes)
  calldata = bytearray([6]) + \
             encode_chunk(node_labels,2) + \
             encode_chunk(edge_label_lengths,2) + \
             encode_chunk(edge_labels,2) + \
             encode_chunk(modified_subtree_idxs,2) + \
             encode_chunk(hashes,4) + \
             encode_chunk(addresses,2) + \
             encode_chunk(accountdatas,2) + \
             encode_chunk(transactions,2)
  calldata = bytearray(calldata)

  # print calldata
  hex_str_commas = ''
  for b in calldata:
    hex_str_commas +=','+hex(b)
  print("calldata as hex separated by commas:")
  print(hex_str_commas)

  state_root = bytearray([0])

  main(calldata)
  if debug:
    print()
    print()
    #print("final pre_hash:", pre_hash)
    #print("final post_hash:", post_hash)










# traverse tree, accumulating calldata bytearrays
node_labels_bits=None
node_labels_bytes=None
edge_label_lens_bytes=None
addresses_bytes=None
accountdata_bytes=None
hashes_bytes=None
def tree2calldata_recursive_helper(node,depth,recursion_depth):
  #print("tree2calldata_recursive_helper(",node,depth,")")
  global node_labels_bits
  global edge_labels_bytes
  global edge_label_lens_bytes
  global addresses_bytes
  global accountdata_bytes
  global hashes_bytes
  global max_tree_depth
  global num_accountdata_bytes
  if recursion_depth>max_tree_depth:
    max_tree_depth=recursion_depth
  # if leaf
  if node.node_type[0] == 0b00:
    node_labels_bits += "00"
    if node.edge_label_len.cast('I')[0] != 0:
      edge_label_lens_bytes += bytearray([node.edge_label_len.cast("I")[0]%256])
    addresses_bytes += memory[node.left_or_address_byteidx.cast("I")[0]:node.left_or_address_byteidx.cast("I")[0]+num_address_bytes]
    accountdata_bytes += memory[node.right_or_accountdata_byteidx.cast("I")[0]:node.right_or_accountdata_byteidx.cast("I")[0]+num_accountdata_bytes]
    return
  # if have edge label, not leaf
  if node.edge_label_len.cast('I')[0] != 0:
    node_labels_bits += "00"
    edge_label_lens_bytes += bytearray([node.edge_label_len.cast("I")[0]%256])
    depth+=node.edge_label_len.cast('I')[0]
  # node type. note: not a leaf and edge label, if any, already handled above
  if node.node_type[0] == 0b01:
    node_labels_bits += "01"
    tree2calldata_recursive_helper(Tree_node(node.right_or_accountdata_byteidx.cast('I')[0]), depth+1, recursion_depth+1)
    hashes_bytes += memory[node.left_or_address_byteidx.cast("I")[0]:node.left_or_address_byteidx.cast("I")[0]+num_hash_bytes]
  elif node.node_type[0] == 0b10:
    node_labels_bits += "10"
    tree2calldata_recursive_helper(Tree_node(node.left_or_address_byteidx.cast('I')[0]),depth+1, recursion_depth+1)
    hashes_bytes += memory[node.right_or_accountdata_byteidx.cast("I")[0]:node.right_or_accountdata_byteidx.cast("I")[0]+num_hash_bytes]
  elif node.node_type[0] == 0b11:
    node_labels_bits += "11"
    tree2calldata_recursive_helper(Tree_node(node.left_or_address_byteidx.cast('I')[0]),depth+1, recursion_depth+1)
    tree2calldata_recursive_helper(Tree_node(node.right_or_accountdata_byteidx.cast('I')[0]),depth+1, recursion_depth+1)


def tree2calldata(root):
  global node_labels_bits
  global node_labels_bytes
  global edge_label_lens_bytes
  global addresses_bytes
  global accountdata_bytes
  global hashes_bytes
  global max_tree_depth
  # init
  node_labels_bits=""
  edge_label_lens_bytes=bytearray([])
  edge_label_lengths_bytes=bytearray([])
  addresses_bytes=bytearray([])
  accountdata_bytes=bytearray([])
  hashes_bytes=bytearray([])
  max_tree_depth=0
  # start traversal
  tree2calldata_recursive_helper(root,0,0)
  # fix byte arrays
  node_labels_bytes = bytearray([])
  for bitstr8 in [node_labels_bits[i:i+8] for i in range(0, len(node_labels_bits), 8)]:
    if len(bitstr8)<8:
      bitstr8 += "0"*(8-len(bitstr8))
    node_labels_bytes += int(bitstr8, 2).to_bytes(1, byteorder='big')
  # return results
  return (node_labels_bytes, edge_label_lens_bytes, addresses_bytes, accountdata_bytes, hashes_bytes, max_tree_depth)





def test_generator(num_accounts_in_witness, num_accounts_in_state):
  global num_address_bits
  global num_accountdata_bits
  global num_hash_bits
  global print_idx

  # generate addresses in witness and build a tree with just them
  tree = None
  for i in range(num_accounts_in_witness):
    print("i",i)
    address = bin2bytes(bin(random.randint(0,2**num_address_bits-1))[2:].zfill(num_address_bits))
    accountdata_byteidx = malloc(num_accountdata_bytes) #random.randint(0, 2**num_accountdata_bits-1) #bytearray([100]+[0]*(num_accountdata_bytes-1)) # 
    memory[accountdata_byteidx]=100
    # put addy and bal into memory
    address_byteidx = malloc(num_address_bytes)
    memory[address_byteidx:address_byteidx+num_address_bytes] = address
    print()
    print("inserting address",address.hex(),"accountdata",memory[accountdata_byteidx:accountdata_byteidx+num_accountdata_bytes].hex())
    #neighbor,err = find_account_or_neighbor(tree,address,0)
    found_node_byteidx,err = find_account_or_neighbor_or_error(tree,address_byteidx)
    print("found",found_node_byteidx,err)
    if err == "":
      print("tree was empty")
      tree = insert_leaf(None,address_byteidx,accountdata_byteidx)
    elif err=="neighbor":
      print("found neighbor",found_node_byteidx,"must insert leaf")
      # must insert next to neighbor
      #insert_leaf(neighbor,address,accountdata=accountdata)
      insert_leaf(Tree_node(found_node_byteidx),address_byteidx,accountdata_byteidx)
    elif err=="account":
      print("this account is already present, this is rare")
    while tree.parent_byteidx.cast('I')[0]:
      tmp_node = Tree_node(tree.parent_byteidx.cast('I')[0])
      tree = Tree_node(tmp_node.startbyteidx)
    print("done inserting address",address.hex(),"accountdata",memory[accountdata_byteidx:accountdata_byteidx+num_accountdata_bytes].hex())

    # print tree
    print_idx = 0
    print_subtree(tree.startbyteidx,0,0)
    print_idx = 0
    print_subtree_addresses(tree.startbyteidx,0,0)

  # generate remaining state and insert into tree as dummy hashes
  address_byteidx = malloc(num_address_bytes)
  for i in range(num_accounts_in_state):
    address = bin2bytes(bin(random.randint(0,2**num_address_bits-1))[2:].zfill(num_address_bits))
    memory[address_byteidx:address_byteidx+num_address_bytes] = address
    neighbor_byteidx,err = find_account_or_neighbor_or_error(tree,address_byteidx)
    if err == "neighbor":
      neighbor = Tree_node(neighbor_byteidx)
      # found neighbor, so insert it, then change it to a hash
      new_leaf = insert_leaf(neighbor,address_byteidx,0)
      # change its neighbor's child to a hash
      # note: parent can't be none since new internal node is parent.
      parent = Tree_node(new_leaf.parent_byteidx.cast('I')[0])
      if parent.left_or_address_byteidx.cast('I')[0]==neighbor_byteidx:
        #print("make right child a dummy hash")
        # make right child a dummy hash
        hash_byteidx = malloc(num_hash_bytes)
        parent.right_or_accountdata_byteidx.cast('I')[0] = hash_byteidx
        parent.node_type[0] = 2
        memory[hash_byteidx:hash_byteidx+num_hash_bytes] = bytearray([0]*num_hash_bytes)
      elif parent.right_or_accountdata_byteidx.cast('I')[0]==neighbor_byteidx:
        #print("make left child a dummy hash")
        # make left child a dummy hash
        hash_byteidx = malloc(num_hash_bytes)
        parent.left_or_address_byteidx.cast('I')[0] = hash_byteidx
        parent.node_type[0] = 1
        memory[hash_byteidx:hash_byteidx+num_hash_bytes] = bytearray([0]*num_hash_bytes)
      else:
        print("huh?",parent.right_or_accountdata_byteidx.cast('I')[0],neighbor_byteidx)
    while tree.parent_byteidx.cast('I')[0]:
      tmp_node = Tree_node(tree.parent_byteidx.cast('I')[0])
      tree = Tree_node(tmp_node.startbyteidx)

  # print tree
  print_idx = 0
  print_subtree(tree.startbyteidx,0,0)
  print_idx = 0
  print_subtree_addresses(tree.startbyteidx,0,0)

  return tree


def generate_calldata(num_accounts_in_witness, num_accounts_in_state, num_transactions_to_existing, num_transactions_to_new):

  tree = test_generator(num_accounts_in_witness, num_accounts_in_state)

  # traverse tree collecting bytes of witness
  node_labels_bytes, edge_label_lens_bytes, addresses_bytes, accountdatas_bytes, hashes_bytes, max_tree_depth = tree2calldata(tree)

  # generate transactions
  transactions_bytes = bytearray([])
  for i in range(num_transactions_to_existing):
    from_addy_idx = random.randint(0,num_accounts_in_witness-1)
    to_addy_idx = random.randint(0,num_accounts_in_witness-1)
    from_nonce = 0 #TODO: bug here, must increment nonce for that address
    amount = 1
    # transactions: sender idx, receiver idx, signature, message (receiver address, value)
    transactions_bytes += bytearray([from_addy_idx,to_addy_idx]) + bin2bytes('0'.ljust(num_signature_bits,'0')) + addresses_bytes[to_addy_idx*num_address_bytes: to_addy_idx*num_address_bytes+num_address_bytes] + int2bytes(amount,num_balance_bytes) + int2bytes(from_nonce,num_nonce_bytes)

  modified_subtree_idxs_bytes = bytearray([])
  for i in range(num_transactions_to_new):
    pass
    #TODO
  

  # modified subtrees
  edge_labels_bytes = bytearray([])

  # finally, concatenate everything
  calldata = bytearray([max_tree_depth]) + \
             encode_chunk(node_labels_bytes,2) + \
             encode_chunk(edge_label_lens_bytes,2) + \
             encode_chunk(edge_labels_bytes,2) + \
             encode_chunk(modified_subtree_idxs_bytes,2) + \
             encode_chunk(hashes_bytes,4) + \
             encode_chunk(addresses_bytes,2) + \
             encode_chunk(accountdatas_bytes,2) + \
             encode_chunk(transactions_bytes,2)
             
  print("edge_label_lens_bytes",edge_label_lens_bytes)
  calldata = bytearray(calldata)
  return calldata





if __name__ == "__main__":
  #test_handwritten1()

  num_accounts_in_witness = 10
  num_accounts_in_state = 100
  num_transactions_to_existing = 4
  num_transactions_to_new = 0
  #test_generator(num_accounts_in_witness, num_accounts_in_state)

  num_accounts_in_witness = 10
  num_accounts_in_state = 200
  num_transactions_to_existing = 10
  num_transactions_to_new = 0
  calldata = generate_calldata(num_accounts_in_witness, num_accounts_in_state, num_transactions_to_existing, num_transactions_to_new)
  main(calldata)

  #test_find_and_insert(0)

  #test_insert_leaves()


