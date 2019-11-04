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

debug = 1

##############
# some globals

memory = bytearray([0]*(2**20))     # more than enough
postbalances_idx = 0
postbalances_byteidx = 0
postbalances_startbyteidx = 0
num_original_accounts = 0
num_modified_subtrees = 0

# BYTE SIZES
# accounts
num_address_bits=256
num_balance_bits=64
num_balance_bytes = (num_balance_bits+7)//8
num_address_bytes = (num_address_bits+7)//8
# hashes
num_hash_bits=160
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
num_transaction_bytes=1+1+num_signature_bytes+num_address_bytes+num_balance_bytes
num_transaction_bits=num_transaction_bytes*8


# CALLDATA INFO
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

balances_startbyteidx = 0
balances_bytelen = 0
balances_idx = 0

transactions_startbyteidx = 0
transactions_bytelen = 0
transactions_idx = 0

account_idx = 0

###############
# bit twiddling

def get_bits_big_endian(dst, src, start_bit_idx, len_):
  print("\nget_bits_big_endian(",dst,",","src",",",start_bit_idx,",",len_,")")
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

# calldata, each with a prefix for number of bytes:
#  node_labels
#  edge_label_lengths
#  edge_labels
#  hashes
#  addresses
#  balances
#  transactions

def decode_calldata(memory_idx):
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
  global balances_startbyteidx
  global balances_bytelen
  global transactions_startbyteidx
  global transactions_bytelen
  global transactions_idx
  global memory
  # helper func
  def get_chunk(memidx):
    len_ = int.from_bytes(memory[memidx:memidx+2], byteorder="little")
    return memidx+2+len_, memidx+2, len_
  # parse
  memory_idx, node_labels_startbyteidx, node_labels_bytelen                = get_chunk(memory_idx)
  memory_idx, edge_label_lengths_startbyteidx, edge_label_lengths_bytelen  = get_chunk(memory_idx)
  memory_idx, edge_labels_startbyteidx, edge_labels_bytelen                = get_chunk(memory_idx)
  memory_idx, modified_subtree_idxs_startbyteidx, modified_subtree_idxs_bytelen = get_chunk(memory_idx)
  memory_idx, hashes_startbyteidx, hashes_bytelen                          = get_chunk(memory_idx)
  memory_idx, addresses_startbyteidx, addresses_bytelen                    = get_chunk(memory_idx)
  memory_idx, balances_startbyteidx, balances_bytelen                      = get_chunk(memory_idx)
  memory_idx, transactions_startbyteidx, transactions_bytelen              = get_chunk(memory_idx)







   


# 1) copy pre-balances to post-balances








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
    next_modified_subtree_node_label_idx = 0
  else:
    next_modified_subtree_node_label_idx = int.from_bytes(memory[modified_subtree_idxs_byteidx:modified_subtree_idxs_byteidx+2], byteorder="little")
    modified_subtree_idxs_byteidx += num_subtree_bytes

def get_next_account_idx():
  # this is used to build subtree
  global account_idx
  account_idx += 1
  return account_idx

def get_next_postbalance_byteidx():
  # this is used to build subtree
  global postbalances_idx
  global postbalances_startbyteidx
  global num_balance_bytes
  byteidx = postbalances_startbyteidx + postbalances_idx*num_balance_bytes
  postbalances_idx += 1
  #postbalance = int.from_bytes(postbalances[postbalances_idx:postbalances_idx+num_balance_bytes], byteorder="little")
  return byteidx

def get_next_hash_byteidx():
  # this is used to build subtree and to merkleize pre&post
  global hashes_idx
  global hashes_startbyteidx
  hash_idx = hashes_idx
  hash_byteidx = hashes_startbyteidx + hash_idx*num_hash_bytes
  hashes_idx += 1
  return hash_byteidx


"""
class hey():
  def __init__(self):
    self.m = bytearray([0]*20)
    self.mv = memoryview(self.m)
    self.a = self.mv[:4]
    self.b = self.mv[4:8]

h=hey()
h.a[0]=1
h.b[0]=5
h.m

m = bytearray([0]*20)
mv = memoryview(m)
a = mv[:4]
b = mv[4:8]
a[0]=1
b[0]=5
m

import struct
packed = struct.pack('iiiiiccc20s', 1, 2, 3, 4, 5, bytes([1]), bytes([2]), bytes([3]), bytearray([0]*20))
a1,a2,a3,a4,a5,b1,b2,b3,c = struct.unpack('iiiiiccc20s', packed)

import collections
Tree_node = collections.namedtuple("Tree_node","parent left right leaf_address leaf_balance node_type edge_label_len edge_label_len_total edge_label", verbose=True)
tn = Tree_node._make(struct.unpack('iiiiiccc20s', packed))

"""



# tree node
num_treenode_bytes = 15+num_address_bytes
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

    # parent and children
    self.parent_byteidx                 = self.mv[self.startbyteidx:self.startbyteidx+4]
    self.left_or_address_byteidx        = self.mv[self.startbyteidx+4:self.startbyteidx+8]
    self.right_or_balance_byteidx       = self.mv[self.startbyteidx+8:self.startbyteidx+12]
    #self.lefthash_idx = None
    #self.righthash_idx = None
    # leaf stuff
    #self.leaf_address_byteidx           = self.mv[self.startbyteidx+12:self.startbyteidx+16]
    #self.leaf_balance_byteidx           = self.mv[self.startbyteidx+16:self.startbyteidx+20]
    # node type and edge label
    self.node_type                      = self.mv[self.startbyteidx+12:self.startbyteidx+13]  # 0b00: leaf, 0b01: interior with only right child, 0b10: interior with only left child, 0b11: interior with both children
    self.edge_label_len                 = self.mv[self.startbyteidx+13:self.startbyteidx+14]
    self.edge_label_len_total           = self.mv[self.startbyteidx+14:self.startbyteidx+15]
    self.edge_label                     = self.mv[self.startbyteidx+15:self.startbyteidx+15+num_address_bytes]


# subtree node
num_subtree_bytes = 5+num_address_bytes
class Subtree:
  def __init__(self, startbyteidx):
    # raw bytes
    self.startbyteidx = startbyteidx
    self.mv = memoryview(memory)

    self.root_byteidx           = self.mv[startbyteidx:startbyteidx+4]
    self.address_prefix_len     = self.mv[startbyteidx+4:startbyteidx+5]
    self.address_prefix         = self.mv[startbyteidx+5:startbyteidx+5+num_address_bytes]



debug_build_idx = 0
def build_tree_from_node_labels(edge_label_len_total, node):
  print("\nbuild_tree_from_node_labels(",edge_label_len_total,")")
  global num_address_bits
  global addresses_byteidx
  global num_address_bytes
  global postbalances
  if debug:
    global debug_build_idx
    debug_build_idx+=1
    print("  ",debug_build_idx,"build_tree_from_node_labels(",edge_label_len_total,")")
  # get node label
  node_label = get_next_node_label_bitpair()
  if debug: print(debug_build_idx,"build_tree_from_node_labels()","node_label",node_label)
  # todo: assert we are within bound of label length, etc
  if node_label == 0b00:
    # either we are already at a leaf, or there is an edge label
    if edge_label_len_total == num_address_bits-1: # a leaf without an edge label, this is unlikely
      node.left_or_address_byteidx.cast('I')[0] = get_next_address_byteidx() 
      node.right_or_balance_byteidx.cast('I')[0] = get_next_postbalance_byteidx()
      node.node_type[0] = 0b00
      self.edge_label_len[0] = 0
      node.edge_label_len_total[0] = edge_label_len_total
      node.edge_label[:] = bytearray([0]*num_address_bytes)
      return
    else:
      # there is an edge label, get it
      print()
      print()
      print("there is an edge label, get it")
      node.edge_label_len[0] = get_next_edge_label_length()
      get_bits_big_endian(node.edge_label, memory, 8*addresses_byteidx+edge_label_len_total, node.edge_label_len[0])
      edge_label_len_total += node.edge_label_len[0]
      node.edge_label_len_total[0] = edge_label_len_total
      print("edge_label_len, edge_label_len_total",node.edge_label_len[0],node.edge_label_len_total[0], edge_label_len_total)
      print("addresses_byteidx",addresses_byteidx)
      # either leaf or not leaf
      if debug: print("if leaf then true: ",node.edge_label_len_total[0] == num_address_bits-1, node.edge_label_len_total[0], num_address_bits-1)
      if node.edge_label_len_total[0] == num_address_bits-1:
        if debug: print(debug_build_idx,"build_tree_from_node_labels(",edge_label_len_total,")","found leaf")
        node.edge_label_len_total[0] = edge_label_len_total
        node.left_or_address_byteidx.cast('I')[0] = get_next_address_byteidx()
        node.right_or_balance_byteidx.cast('I')[0] = get_next_postbalance_byteidx()
        node.node_type[0] = 0b00
        return
      else:
        # not a leaf, get next node label and process it below
        node_label = get_next_node_label_bitpair()
        if debug: print(debug_build_idx,"build_tree_from_node_labels(",edge_label_len_total,")","node_label after 00",node_label)
  # this is an internal node, we already got the edge label if there was one
  print("ok",node.edge_label_len_total[0], edge_label_len_total)
  node.edge_label_len_total[0] = edge_label_len_total
  node.node_type[0] = node_label
  if node_label == 0b11:
    # recurse left and right
    left_subtree = Tree_node(malloc(num_treenode_bytes))
    left_subtree.parent_byteidx.cast('I')[0] = node.startbyteidx
    node.left_or_address_byteidx.cast('I')[0] = left_subtree.startbyteidx
    if debug: print(debug_build_idx,"build_tree_from_node_labels(",edge_label_len_total,")","recursing left")
    build_tree_from_node_labels(edge_label_len_total+1, left_subtree)
    right_subtree = Tree_node(malloc(num_treenode_bytes))
    right_subtree.parent_byteidx.cast('I')[0] = node.startbyteidx
    node.right_or_balance_byteidx.cast('I')[0] = right_subtree.startbyteidx
    if debug: print(debug_build_idx,"build_tree_from_node_labels(",edge_label_len_total,")","recursing right")
    build_tree_from_node_labels(edge_label_len_total+1, right_subtree)
  elif node_label == 0b10:
    # recurse left, get hash for right
    left_subtree = Tree_node(malloc(num_treenode_bytes))
    left_subtree.parent_byteidx.cast('I')[0] = node.startbyteidx
    node.left_or_address_byteidx.cast('I')[0] = left_subtree.startbyteidx
    if debug: print(debug_build_idx,"build_tree_from_node_labels(",edge_label_len_total,")","recursing left")
    build_tree_from_node_labels(edge_label_len_total+1, left_subtree)
    node.right_or_balance_byteidx.cast('I')[0] = get_next_hash_byteidx()
  elif node_label == 0b01:
    # get hash for left, recurse right
    node.left_or_balance_byteidx.cast('I')[0] = get_next_hash_byteidx()
    right_subtree = Tree_node(malloc(num_treenode_bytes))
    right_subtree.parent_byteidx.cast('I')[0] = node.startbyteidx
    node.right_or_balance_byteidx.cast('I')[0] = right_subtree.startbyteidx
    if debug: print(debug_build_idx,"build_tree_from_node_labels(",edge_label_len_total,")","recursing right")
    build_tree_from_node_labels(edge_label_len_total+1, right_subtree)


# build each subtree, put them in a global array
modified_subtrees_startbyteidx = 0
def build_modified_subtrees():
  print("build_modified_subtrees()")
  global modified_subtrees
  global modified_subtrees_startbyteidx
  modified_subtrees_startbyteidx = malloc(num_modified_subtrees*num_subtree_bytes)
  modified_subtrees_byteidx = modified_subtrees_startbyteidx
  global modified_subtree_idxs_bytelen
  global node_labels_idx
  global edge_label_lengths_idx
  global edge_labels_idx
  global hashes_idx
  global addresses_byteidx
  global postbalances_idx
  modified_subtree_idxs_byteidx = modified_subtree_idxs_startbyteidx
  for i in range(num_modified_subtrees):
    # get all relevant idxs
    # TODO: these idxs may be malicious, is it OK, or may have to rebuild addresses with a traversal and bittwiddling of address chunks
    node_labels_idx           = int.from_bytes(memory[modified_subtree_idxs_byteidx:modified_subtree_idxs_byteidx+2], byteorder="little")
    edge_label_lengths_idx    = int.from_bytes(memory[modified_subtree_idxs_byteidx+2:modified_subtree_idxs_byteidx+4], byteorder="little")
    edge_labels_idx           = int.from_bytes(memory[modified_subtree_idxs_byteidx+4:modified_subtree_idxs_byteidx+6], byteorder="little")
    hashes_idx                = int.from_bytes(memory[modified_subtree_idxs_byteidx+6:modified_subtree_idxs_byteidx+8], byteorder="little")
    account_idx               = int.from_bytes(memory[modified_subtree_idxs_byteidx+8:modified_subtree_idxs_byteidx+10], byteorder="little")
    addresses_idx, postbalances_idx = account_idx, account_idx
    addresses_byteidx = addresses_startbyteidx+addresses_idx*num_address_bytes
    edge_label_len_total     = int.from_bytes(memory[modified_subtree_idxs_byteidx+10:modified_subtree_idxs_byteidx+11], byteorder="little")
    print("build_modified_subtrees() iter  node_labels_idx",node_labels_idx,"edge_labels_lengths_idx",edge_label_lengths_idx,"edge_labels_idx",edge_labels_idx,"hashes_idx",hashes_idx,"account_idx",account_idx,"edge_label_len_total",edge_label_len_total)
    modified_subtree_idxs_byteidx += 11
    # create new node
    subtree_root_byteidx = malloc(num_treenode_bytes)
    subtree_root_node = Tree_node(subtree_root_byteidx)
    # encapsulate subtree in structure to maintain its edge label prefix
    subtree = Subtree(modified_subtrees_byteidx)
    subtree.root_byteidx.cast('I')[0] = subtree_root_byteidx
    subtree.address_prefix_len[0]     = edge_label_len_total
    get_bits_big_endian(subtree.address_prefix, memory, 8*addresses_byteidx, edge_label_len_total)
    #print(subtree.address_prefix.cast('B')[0], edge_label_len_total)
    # build subtree of nodes
    #print("building subtree with subtree.startbyteidx",subtree.startbyteidx)
    build_tree_from_node_labels(edge_label_len_total, subtree_root_node)
    # iterate
    modified_subtrees_byteidx += num_subtree_bytes



  







# 3) process transactions 

def find_account_or_neighbor_or_error(node,address_byteidx):
  print("find_account_or_neighbor_or_error(",node,address_byteidx,")")
  if node==None:
    return None, ""
  label_len = node.edge_label_len[0]
  label_endbitidx = node.edge_label_len_total[0]
  label_startbitidx = label_endbitidx-label_len
  # if has edge label
  if label_len>0:
    #print("have edge label")
    # check edge label against corresponding bits in address from signature
    corresponding_bits = bytearray([0]*((label_len+7)//8))
    get_bits_big_endian(corresponding_bits, memory, 8*address_byteidx+label_endbitidx-label_len, label_len)
    print(node.edge_label,corresponding_bits)
    if node.edge_label[:(label_len+7)//8] != corresponding_bits:
      # TODO: do we need to check against neighbor up to this point. Don't think so, since checked up to root of subtree, then checked each label, and left/right corresponded to 0/1. So no need I think.
      return node.startbyteidx, "neighbor" # leaf not present, but have neighbor
  # if leaf
  if node.node_type[0] == 0b00: # leaf; or, equivalently, label_endbitidx==num_address_bits-1
    # TODO: hmm, maybe don't think that I have to compare leaf address to sig address, since couldn't get this far otherwise
    return node.startbyteidx, "account"
    # confirm that address at leaf matches address from signature
    #leaf_address_from_node = memory[node.leaf_address_byteidx:node.leaf_address_byteidx+num_address_bytes]
    #leaf_address_from_sig = memory[address_byteidx:address_byteidx+num_address_bytes]
    #if leaf_address_from_node == leaf_address_from_sig:
    #  #print("found account")
    #  return node, "account"
    #else:
    #  #print("found neighbor")
    #  return node, "neighbor"
  # recurse left/right based on next bit
  nextbit = bytearray([0])
  get_bits_big_endian(nextbit, memory, address_byteidx+8*label_endbitidx+1,1) #print("nextbit",nextbit)
  if nextbit == bytearray([0]):
    #print("recurse left",nextbit)
    return find_account_or_neighbor_or_error(Tree_node(node.left_or_address_byteidx.cast('I')[0]), address_byteidx)
  else:
    #print("recurse right",nextbit)
    return find_account_or_neighbor_or_error(Tree_node(node.right_or_balance_byteidx.cast('I')[0]), address_byteidx)


def insert_leaf(neighbor,address_byteidx,balance=0):
  print("insert_leaf(",neighbor,",",address_byteidx,")")
  # if tree is empty, insert this address and balance and return
  # TODO: don't think there should be this possibility, since edge label lengths are unknown, so can't insert first node
  if neighbor == None:
    new_leaf_byteidx = malloc(num_treenode_bytes)
    new_leaf = Tree_node(new_leaf_byteidx)
    new_leaf.node_type[0] = 0b00
    address_byteidx = malloc(num_address_bytes)
    balance_byteidx = malloc(num_balance_bytes)
    new_leaf.left_or_address_byteidx.cast('I')[0] = address_byteidx
    new_leaf.right_or_balance_byteidx.cast('I')[0] = balance_byteidx
    new_leaf.edge_label_len[0] = num_address_bits - neighbor.edge_label_len_total[0] - neighbor.edge_label_len[0]
    new_leaf.edge_label_len_total[0] = num_address_bits - 1
    new_leaf.edge_label[0:num_address_bytes] = memory[address_byteidx:address_byteidx+num_address_bytes]
    return new_leaf
  # get bit where address and edge_label diverge
  #print("neighbor.edge_label_len",neighbor.edge_label_len)
  #print_node(neighbor,10)
  i=0
  while i < neighbor.edge_label_len[0]:
    print("i",i)
    bit_idx = neighbor.edge_label_len_total[0]-neighbor.edge_label_len[0]+i
    addybit = bytearray([0])
    get_bits_big_endian(addybit, memory, 8*address_byteidx + bit_idx,1)
    edge_label_bit = bytearray([0])
    get_bits_big_endian(edge_label_bit, neighbor.edge_label, i, 1)
    print(addybit,edge_label_bit)
    if addybit != edge_label_bit:
      break
    i+=1
  print("final i",i)
  # insert node
  new_interior_node = Tree_node(malloc(num_treenode_bytes))
  new_interior_node.node_type[0] = 0b11
  new_leaf = Tree_node(malloc(num_treenode_bytes))
  new_leaf.node_type[0] = 0b00
  new_leaf.left_or_address_byteidx.cast('I')[0] = address_byteidx
  new_leaf.right_or_balance_byteidx.cast('I')[0] = malloc(num_balance_bytes)
  print("new_interior_node and new_leaf", new_interior_node.startbyteidx, new_leaf.startbyteidx)
  # first take care of edge labels and lengths
  new_interior_node.edge_label_len[0] = i
  new_interior_node.edge_label_len_total[0] = neighbor.edge_label_len_total[0] - neighbor.edge_label_len[0] + i
  print("new_interior_node.edge_label_len_total",new_interior_node.edge_label_len_total[0])
  if new_interior_node.edge_label_len[0]:
    print("ok1")
    label_startidx = neighbor.edge_label_len_total[0]-neighbor.edge_label_len[0]
    label_len = new_interior_node.edge_label_len[0]
    get_bits_big_endian(new_interior_node.edge_label, memory, 8*address_byteidx + label_startidx, label_len)
  print("ok3")
  new_leaf.edge_label_len[0] = num_address_bits - new_interior_node.edge_label_len_total[0]-1
  new_leaf.edge_label_len_total[0] = num_address_bits-1
  get_bits_big_endian(new_leaf.edge_label, memory, 8*address_byteidx + new_interior_node.edge_label_len_total[0], num_address_bits-new_interior_node.edge_label_len_total[0])
  neighbor.edge_label_len[0] -= i+1
  if neighbor.edge_label_len[0] != 0:
    print("ok5")
    #neighbor.edge_label = get_bits_big_endian(neighbor.edge_label,i+1,i+1+neighbor.edge_label_len)
    label_startidx = neighbor.edge_label_len_total-neighbor.edge_label_len+i-1
    get_bits_big_endian(neighbor.edge_label, memory, label_startidx, neighbor.edge_label_len[0])
  # adjust parent and children pointers
  new_leaf.parent_byteidx.cast('I')[0] = new_interior_node.startbyteidx
  new_interior_node.parent_byteidx.cast('I')[0] = neighbor.parent_byteidx.cast('I')[0]
  if neighbor.parent_byteidx.cast('I')[0]:
    parent = Tree_node(neighbor.parent_byteidx.cast('I')[0])
    if parent.left_or_address_byteidx.cast('I')[0] == neighbor.startbyteidx:
      parent.left_or_address_byteidx.cast('I')[0] = new_interior_node.startbyteidx
    else:
      parent.right_or_balance_byteidx.cast('I')[0] = new_interior_node.startbyteidx
  neighbor.parent_byteidx.cast('I')[0] = new_interior_node.startbyteidx
  print("new interior node has left and right children:")
  # two cases: diverge left or right
  #print("ok",addybit,new_interior_node)
  if addybit==bytearray(b'\x00'): # diverge right
    new_interior_node.right_or_balance_byteidx.cast('I')[0] = neighbor.startbyteidx
    new_interior_node.left_or_address_byteidx.cast('I')[0] = new_leaf.startbyteidx
  else: # diverge left
    new_interior_node.right_or_balance_byteidx.cast('I')[0] = new_leaf.startbyteidx
    new_interior_node.left_or_address_byteidx.cast('I')[0] = neighbor.startbyteidx
  return new_leaf


def delete_node(parent,side):
  pass


# this update code can be modified to do custom things, eg update balance, increment nonce, etc
def update_accounts(to_address_byteidx, from_address_byteidx, to_data_byteidx, from_data_byteidx, data_byteidx):
  print("update_accounts(",to_address_byteidx, from_address_byteidx, to_data_byteidx, from_data_byteidx, data_byteidx,")")
  from_balance = int.from_bytes(memory[from_data_byteidx:from_data_byteidx+num_balance_bytes],"little")
  to_balance = int.from_bytes(memory[to_data_byteidx:to_data_byteidx+num_balance_bytes],"little")
  value = int.from_bytes(memory[data_byteidx:data_byteidx+num_balance_bytes],"little")
  print("from",memory[from_address_byteidx:from_address_byteidx+num_address_bytes].hex(), from_balance)
  print("to",memory[to_address_byteidx:to_address_byteidx+num_address_bytes].hex(), to_balance)
  print("value",value)
  if from_balance < value:
    return None     # error
  from_balance -= value
  to_balance += value
  memory[to_data_byteidx:to_data_byteidx+num_balance_bytes] = to_balance.to_bytes(num_balance_bytes, "little")
  memory[from_data_byteidx:from_data_byteidx+num_balance_bytes] = from_balance.to_bytes(num_balance_bytes, "little")
  print("from",memory[from_address_byteidx:from_address_byteidx+num_address_bytes].hex(), from_balance)
  print("to",memory[to_address_byteidx:to_address_byteidx+num_address_bytes].hex(), to_balance)


def process_transactions():
  print()
  print()
  print("process_transactions()")
  global transactions_startbyteidx
  global transactions_bytelen
  global memory
  global num_modified_subtrees
  global modified_subtrees
  num_balances = balances_bytelen//num_balance_bytes
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
    data_byteidx = txs_byteidx #int.from_bytes(memory[txs_byteidx:txs_byteidx+num_balance_bytes],"little")
    txs_byteidx += num_balance_bytes
    # get accounts
    # from address and data
    from_address_byteidx = addresses_startbyteidx + from_idx*num_address_bytes
    from_data_byteidx = postbalances_startbyteidx + from_idx*num_balance_bytes
    # to_data, note we have to_address from signature message
    if to_idx < num_balances:
      to_data_byteidx = postbalances_startbyteidx + to_idx*num_balance_bytes
    elif to_idx < num_balances + num_modified_subtrees:
      # traverse tree until leaf, possibly inserting a new leaf
      print("must traverse tree.   to_idx>=num_orignal_accounts", to_idx, num_original_accounts)
      subtree = Subtree(modified_subtrees_startbyteidx + num_subtree_bytes*(to_idx-num_original_accounts))
      node = Tree_node(subtree.root_byteidx.cast('I')[0])
      print("subtree",subtree.startbyteidx,"node",node.startbyteidx)
      # check subtree address prefix against to address prefix
      label_len = node.edge_label_len[0]
      label_endbitidx = node.edge_label_len_total[0]
      label_startbitidx = label_endbitidx-label_len
      to_bytes = memory[to_address_byteidx:to_address_byteidx+label_endbitidx//8]
      subtree_bytes = subtree.address_prefix[0:label_endbitidx//8]
      #bytes2 = uemory[subtree.address_prefix_byteidx.cast('I')[0]:subtree.address_prefix_byteidx.cast('I')[0]+(label_endbitidx+7)//8]
      print("0k")
      print(to_bytes,subtree_bytes)
      if to_bytes != subtree_bytes:
        print("error address prefix not equal")
        return None, "" # error
      to_lastbyte = bytearray([0])
      get_bits_big_endian(to_lastbyte, memory, 8*(to_address_byteidx+label_endbitidx//8), label_endbitidx%8)
      #get_bits_big_endian(lastbyte2, 8*(subtree.address_prefix_byteidx.cast('I')[0]+label_endbitidx//8), label_endbitidx%8)
      subtree_lastbyte = bytearray([subtree.address_prefix[label_endbitidx//8]])
      print(to_lastbyte,subtree_lastbyte)
      if to_lastbyte != subtree_lastbyte:
        print("error address prefix not equal at last byte")
        return None, "" # error
      # find leaf for this account or the neighbor which it branches from if there is a new node
      node_account_or_neighbor_byteidx,err = find_account_or_neighbor_or_error(node,to_address_byteidx)
      print("node_account_or_neighbor_byteidx,err",node_account_or_neighbor_byteidx,err)
      # if not a leaf, must insert leaf
      account = Tree_node(node_account_or_neighbor_byteidx)
      if err=="neighbor":
        account = insert_leaf(account,to_address_byteidx)
      to_data_byteidx = account.right_or_balance_byteidx.cast('I')[0]
    else:
      print("error, to_idx is too large")
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
  if hash_inplace_flag:
    hash_state_byteidx = malloc(num_hash_state_bytes)
  else:
    hash_state_byteidx = malloc(num_hash_state_bytes+num_hash_block_bytes)

num_hashblock_bytes = 2*num_hash_bytes+1
def hash_(dst_byteidx, src_byteidx, len_):
  print("hash(",dst_byteidx, src_byteidx, len_,")")
  if hash_inplace_flag:
    # TODO: hash here
    pass
  else:
    memcpy(hash_state_byteidx+num_hash_state_bytes, src_byteidx, len_)
    # TODO: hash here
    memcpy(dst_byteidx, hash_state_byteidx+num_hash_state_bytes, num_hash_bytes)
  print(memory[dst_byteidx:dst_byteidx+num_hash_bytes].hex())

def merkleize_modifiable_subtree(hash_block_byteidx,node,recursion_depth):
  print(recursion_depth," "*recursion_depth+"merkleize_modifiable_subtree(",node,recursion_depth,")")
  if heap_byteidx < hash_block_byteidx + num_hashblock_bytes:
    malloc(hash_block_byteidx + num_hashblock_bytes - heap_byteidx)
  memory[hash_block_byteidx:hash_block_byteidx+num_hashblock_bytes] = bytearray([0]*num_hashblock_bytes) # zero workspace
  if heap_byteidx < hash_block_byteidx + num_hashblock_bytes:
    hash_block_byteidx = malloc(num_hashblock_bytes)
  else:
    # zero out, but maybe this is only needed at end
    memory[hash_block_byteidx:hash_block_byteidx+num_hashblock_bytes] = bytearray([0]*num_hashblock_bytes)
  #print(node.leaf_balance_arr)
  print(recursion_depth," "*recursion_depth,node.node_type[0])
  if node.node_type[0]==0b00: # leaf
    memcpy(hash_block_byteidx, node.left_or_address_byteidx.cast('I')[0], num_address_bytes)
    memcpy(hash_block_byteidx+num_address_bytes, node.right_or_balance_byteidx.cast('I')[0], num_balance_bytes)
    memcpy(hash_block_byteidx+num_address_bytes+1, node.edge_label_len[0], 1)
  elif node.node_type[0] == 0b01:
    memcpy(hash_block_byteidx, node.left_or_address_byteidx.cast('I')[0], num_hash_bytes)
    merkleize_modifiable_subtree(hash_block_byteidx+num_hashblock_bytes, Tree_node(node.right_or_balance_byteidx.cast('I')[0]), recursion_depth+1)
    memcpy(hash_block_byteidx+num_hash_bytes, hash_block_byteidx+num_hashblock_bytes, num_hash_bytes)
    memcpy(hash_block_byteidx+num_hash_bytes+1, node.edge_label_len[0], 1)
  elif node.node_type[0] == 0b10:
    merkleize_modifiable_subtree(hash_block_byteidx+num_hashblock_bytes, Tree_node(node.left_or_address_byteidx.cast('I')[0]), recursion_depth+1)
    memcpy(hash_block_byteidx, hash_block_byteidx+num_hashblock_bytes, num_hash_bytes)
    memcpy(hash_block_byteidx, node.left_or_address_byteidx.cast('I')[0], num_hash_bytes)
    memcpy(hash_block_byteidx+num_hash_bytes+1, node.edge_label_len[0], 1)
  elif node.node_type[0] == 0b11:
    merkleize_modifiable_subtree(hash_block_byteidx+num_hashblock_bytes, Tree_node(node.left_or_address_byteidx.cast('I')[0]), recursion_depth+1)
    memcpy(hash_block_byteidx, hash_block_byteidx+num_hashblock_bytes, num_hash_bytes)
    merkleize_modifiable_subtree(hash_block_byteidx+num_hashblock_bytes, Tree_node(node.right_or_balance_byteidx.cast('I')[0]), recursion_depth+1)
    memcpy(hash_block_byteidx+num_hash_bytes, hash_block_byteidx+num_hashblock_bytes, num_hash_bytes)
    memcpy(hash_block_byteidx+num_hash_bytes+1, node.edge_label_len[0], 1)
  print(recursion_depth," "*recursion_depth,"hashing")
  hash_(hash_block_byteidx, hash_block_byteidx, num_hashblock_bytes)


modifiable_subtree_idx = 0
def merkleize_pre_and_post(hash_block_byteidx,depth,recursion_depth,post_hash_flag):
  print(recursion_depth," "*recursion_depth+"merkleize_pre_and_post(",hash_block_byteidx,depth,recursion_depth,post_hash_flag,")")
  global memory
  global modifiable_subtree_idx
  global node_labels_idx
  global account_idx
  num_workspace_bytes = num_hashblock_bytes + post_hash_flag*num_hashblock_bytes
  if heap_byteidx < hash_block_byteidx + num_workspace_bytes:
    malloc(hash_block_byteidx + num_workspace_bytes - heap_byteidx)
  memory[hash_block_byteidx:hash_block_byteidx+num_workspace_bytes] = bytearray([0]*num_workspace_bytes) # zero workspace
  edge_label_len = 0
  #print(recursion_depth," "*recursion_depth+"node_labels_idx",node_labels_idx,"next_modifiable_subtree_node_label_idx",next_modified_subtree_node_label_idx)
  if node_labels_idx == next_modified_subtree_node_label_idx:
    post_hash_flag = 0
    subtree = Subtree(modified_subtrees_startbyteidx + modifiable_subtree_idx*num_subtree_bytes)
    node = Tree_node(subtree.root_byteidx.cast('I')[0])
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
    print(recursion_depth," "*recursion_depth+"node_label == 0b00")
    #print(recursion_depth," "*recursion_depth+"depth",depth,"num_address_bis",num_address_bits)
    if depth==num_address_bits-1: # leaf with no edge label, this is rare
      # put address, prestate balance, and edge_label_len=0
      memcpy(hash_block_byteidx, addresses_startbyteidx+account_idx*num_address_bytes,num_address_bytes)
      memcpy(hash_block_byteidx+num_address_bytes, balances_startbyteidx+account_idx*num_balance_bytes,num_balance_bytes)
      #address = memory[addresses_startbyteidx+account_idx*num_address_bytes:addresses_startbyteidx+(account_idx+1)*num_address_bytes]
      #pre_balance = memory[balances_startbyteidx+account_idx*num_balance_bytes:balances_startbyteidx+(account_idx+1)*num_balance_bytes]
      #pre_hash = hash_(address+pre_balance)
      if post_hash_flag==1:
        # put address, poststate balance, and edge_label_len=0
        memcpy(hash_block_byteidx+num_hashblock_bytes, addresses_startbyteidx+account_idx*num_address_bytes,num_address_bytes)
        memcpy(hash_block_byteidx+num_hashblock_bytes+num_address_bytes, postbalances_startbyteidx+account_idx*num_balance_bytes,num_balance_bytes)
        #post_balance = postbalances[account_idx*num_balance_bytes:account_idx*num_balance_bytes+num_balance_bytes]
        #post_hash = hash_(address+post_balance+bytearray([0]))
      account_idx = get_next_account_idx()
      #print(recursion_depth," "*recursion_depth+"1pre_hash:", pre_hash)
      #print(recursion_depth," "*recursion_depth+"post_hash:", post_hash)
      #print()
      #return pre_hash,post_hash
    else: 
      edge_label_len = get_next_edge_label_length()
      print(recursion_depth," "*recursion_depth+"edge_label_len",edge_label_len)
      depth += edge_label_len
      #print(recursion_depth," "*recursion_depth+"    edge_label_len",edge_label_len)
      #print(recursion_depth," "*recursion_depth+depth,num_address_bits-1)
      if depth==num_address_bits-1: # a leaf with an edge label
        memcpy(hash_block_byteidx, addresses_startbyteidx+account_idx*num_address_bytes,num_address_bytes)
        memcpy(hash_block_byteidx+num_address_bytes, balances_startbyteidx+account_idx*num_balance_bytes,num_balance_bytes)
        memory[hash_block_byteidx+num_address_bytes+num_balance_bytes+1] = edge_label_len
        if post_hash_flag==1:
        # put address, poststate balance, and edge_label_len=0
          memcpy(hash_block_byteidx+num_hashblock_bytes, addresses_startbyteidx+account_idx*num_address_bytes,num_address_bytes)
          memcpy(hash_block_byteidx+num_hashblock_bytes+num_address_bytes, postbalances_startbyteidx+account_idx*num_balance_bytes,num_balance_bytes)
          memory[hash_block_byteidx+num_hashblock_bytes+num_address_bytes+num_balance_bytes+1] = edge_label_len
        account_idx = get_next_account_idx()
        #print(recursion_depth," "*recursion_depth+"2pre_hash:", pre_hash)
        #print(recursion_depth," "*recursion_depth+"post_hash:", post_hash)
        #print()
        #return pre_hash,post_hash
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
  hash_(hash_block_byteidx, hash_block_byteidx, num_hashblock_bytes)
  if post_hash_flag==1:
    hash_(hash_block_byteidx+num_hashblock_bytes, hash_block_byteidx+num_hashblock_bytes, num_hashblock_bytes)
  



def init_merkleization_and_merkleize(hash_block_byteidx):
  global node_labels_idx
  global edge_labels_startbyteidx
  global edge_label_lengths_idx
  global hashes_idx
  global modified_subtree_idxs_startbyteidx
  global modified_subtree_idxs_byteidx
  global addresses_startbyteidx
  global balances_startbyteidx
  global transactions_startbyteidx
  # init stuff
  node_labels_idx = 0
  edge_label_lengths_idx = 0
  edge_labels_idx = edge_labels_startbyteidx
  hashes_idx = 0
  addresses_byteidx = addresses_startbyteidx
  balances_idx = balances_startbyteidx
  transactions_idx = transactions_startbyteidx
  modified_subtree_idxs_byteidx = modified_subtree_idxs_startbyteidx
  get_next_modified_subtree_node_label_idx()
  init_hash()
  # other globals
  global modifiable_subtree_idx
  modifiable_subtree_idx = 0
  global account_idx
  account_idx = 0
  # finally, compute new and old hashes
  merkleize_pre_and_post(hash_block_byteidx,0,0,1)















def main(calldata,arg_state_root):
  global postbalances
  global postbalances_startbyteidx
  global num_original_accounts
  global modified_subtrees
  global memory
  global state_root

  # 0) decode calldata
  malloc(len(calldata))
  memory[:len(calldata)] = calldata[:]
  if debug:
    print("0) decode calldata")
  calldata_startbyteidx = 0
  decode_calldata(calldata_startbyteidx)
  if debug:
    print("node_labels idxs",node_labels_startbyteidx, node_labels_bytelen)
    print("edge_label_lengths idx",edge_label_lengths_startbyteidx, edge_label_lengths_bytelen)
    print("edge_labels idxs",edge_labels_startbyteidx, edge_labels_bytelen)
    print("modified_subtrees idxs",modified_subtree_idxs_startbyteidx, modified_subtree_idxs_bytelen)
    print("hashes idxs",hashes_startbyteidx, hashes_bytelen)
    print("addresses idxs",addresses_startbyteidx, addresses_bytelen)
    print("balances idxs",balances_startbyteidx, balances_bytelen)
    print("transactions idxs",transactions_startbyteidx, transactions_bytelen)



  # 1) copy pre-balances to post-balances
  if debug:
    print()
    print("1) copy pre-balances to post-balances")
  postbalances_startbyteidx = malloc(balances_bytelen)
  memcpy(postbalances_startbyteidx, balances_startbyteidx, balances_bytelen)
  num_original_accounts = balances_bytelen//num_balance_bytes



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
      subtree = Subtree(modified_subtrees_byteidx)
      print()
      print("subtree with address prefix of length ",subtree.address_prefix_len[0], bytearray(subtree.address_prefix.cast('B')[0:num_address_bytes]).hex())
      print_subtree2(subtree.root_byteidx.cast('I')[0],0,0)
      modified_subtrees_byteidx += num_subtree_bytes


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
      subtree = Subtree(modified_subtrees_byteidx)
      print()
      print("subtree with address prefix of length ",subtree.address_prefix_len[0], bytearray(subtree.address_prefix.cast('B')[0:num_address_bytes]).hex())
      print_subtree2(subtree.root_byteidx.cast('I')[0],0,0)
      modified_subtrees_byteidx += num_subtree_bytes
    # print prebalances
    print()
    print("prebalances")
    for i in range(num_original_accounts):
      print(int.from_bytes(memory[balances_startbyteidx+i*num_balance_bytes:balances_startbyteidx+i*num_balance_bytes+num_balance_bytes], byteorder="little"))
    print()
    # print postbalances
    print()
    print("postbalances")
    for i in range(num_original_accounts):
      print(int.from_bytes(memory[postbalances_startbyteidx+i*num_balance_bytes:postbalances_startbyteidx+i*num_balance_bytes+num_balance_bytes], byteorder="little"))
      #print(int.from_bytes(memory[balances_startbyteidx+i*num_balance_bytes:balances_startbyteidx+i*num_balance_bytes+num_balance_bytes], byteorder="little"))
    print()


  # 4) Merkleize pre and post root
  if debug:
    print()
    print("4) Merkleize pre and post root")
  print("4) Merkleize pre and post root")
  hash_block_byteidx = malloc(2*num_hashblock_bytes)
  init_merkleization_and_merkleize(hash_block_byteidx)

  return None,None
  """
  # 5) check if computed_old_root equas old_root
  if debug:
    print()
    print("5) check if computed_old_root equas old_root")
  if computed_old_root == arg_state_root:
    state_root = new_root

  return computed_old_root, new_root
  """











####################################
# code before here is the contract #
#  code below here is for testing  #
####################################





########################
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




# helper to print stuff

print_idx = 0

def print_node(node,indent):
  global print_idx
  print(" "*indent,print_idx,"node:",node)
  print(" "*indent,print_idx,"node_type:",node.node_type)
  print(" "*indent,print_idx,"edge_label_len:",node.edge_label_len,"edge_label:",node.edge_label.hex(),"edge_label_len_total:",node.edge_label_len_total)
  print(" "*indent,print_idx,"parent",node.parent)
  print(" "*indent,print_idx,"lefthash_idx",node.lefthash_idx)
  print(" "*indent,print_idx,"righthash_idx",node.righthash_idx)
  print(" "*indent,print_idx,"left",node.left)
  print(" "*indent,print_idx,"right",node.right)
  if node.leaf_address_arr:
    print(" "*indent,print_idx,"leaf_address",node.leaf_address_arr[node.leaf_address_byteidx:node.leaf_address_byteidx+num_address_bytes].hex())
    print(" "*indent,print_idx,"leaf_address_byteidx",node.leaf_address_byteidx)
  print(" "*indent,print_idx,"leaf_balance_byteidx",node.leaf_balance_byteidx)
  if node.leaf_balance_arr:
    print(" "*indent,print_idx,"leaf_balance",node.leaf_balance_arr[node.leaf_balance_byteidx:node.leaf_balance_byteidx+num_balance_bytes])

def print_subtree(node,depth,indent):
  global print_idx
  print_idx += 1
  print_node(node,indent)
  if node.left:
    print_subtree(node.left,depth+node.edge_label_len+1,indent+1)
  if node.right:
    print_subtree(node.right,depth+node.edge_label_len+1,indent+1)




def print_node2(node,indent):
  print("print_node2(",node,",",indent,")")
  print("\n" + " "*indent + str(indent) + " startbyteidx "             + str(node.startbyteidx) + \
        "\n" + " "*indent + str(indent) + " parent_byteidx "           + str(node.parent_byteidx.cast('I')[0]) + \
        "\n" + " "*indent + str(indent) + " left_or_address_byteidx "  + str(node.left_or_address_byteidx.cast('I')[0]) + \
        "\n" + " "*indent + str(indent) + " right_or_balance_byteidx " + str(node.right_or_balance_byteidx.cast('I')[0]) + \
        "\n" + " "*indent + str(indent) + " node_type "                + str(node.node_type[0]) + \
        "\n" + " "*indent + str(indent) + " edge_label_len "           + str(node.edge_label_len[0]) + \
        "\n" + " "*indent + str(indent) + " edge_label_len_total "     + str(node.edge_label_len_total[0]) + \
        "\n" + " "*indent + str(indent) + " edge_label "               + node.edge_label[:].hex() )
  if node.node_type[0]==0:
    print(       " "*indent + str(indent) + " address " + memory[node.left_or_address_byteidx.cast('I')[0]:node.left_or_address_byteidx.cast('I')[0]+num_address_bytes].hex())
    print(       " "*indent + str(indent) + " balance " + memory[node.right_or_balance_byteidx.cast('I')[0]:node.right_or_balance_byteidx.cast('I')[0]+num_balance_bytes].hex())
  if node.node_type[0]==1:
    print(       " "*indent + str(indent) + " left hash " + memory[node.left_or_address_byteidx.cast('I')[0]:node.left_or_address_byteidx.cast('I')[0]+num_hash_bytes].hex())
  if node.node_type[0]==2:
    print(       " "*indent + str(indent) + " right hash " + memory[node.right_or_balance_byteidx.cast('I')[0]:node.right_or_balance_byteidx.cast('I')[0]+num_hash_bytes].hex())




def print_subtree2(node_byteidx,depth,indent):
  global print_idx
  if debug: print("print_subtree2(",node_byteidx,",",depth,",",indent,")")
  print_idx += 1
  node = Tree_node(node_byteidx)
  depth += node.edge_label_len[0]+1
  print_node2(node,indent)
  if node.node_type[0] in {2,3}:  # recurse left
    print_subtree2(node.left_or_address_byteidx.cast('I')[0],depth,indent+1)
  if node.node_type[0] in {1,3}:  # recurse right
    print_subtree2(node.right_or_balance_byteidx.cast('I')[0],depth,indent+1)




def test_handwritten1():
  global num_address_bits
  global num_balance_bits
  global num_hash_bits
  def encode_chunk(chunk):
    chunk_encoded = len(chunk).to_bytes(2, byteorder='little') + chunk
    #print("encoding chunk:",chunk, "to", chunk_encoded)
    return chunk_encoded
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
  """
  # node labels
  node_labels = bin2bytes('11''10''00''10''00''11''00''00''01''00')
  # edge label lengths
  edge_label_lengths = bytearray([1,num_address_bits-5,num_address_bits-3,1,num_address_bits-5])
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
  # balances 
  balances = \
          (2).to_bytes(num_balance_bytes,'little') + \
          (5).to_bytes(num_balance_bytes,'little') + \
          (7).to_bytes(num_balance_bytes,'little')
  # transactions: sender idx, receiver idx, signature, message (receiver address, value)
  #   0010.. sends 1 to 1111..    1010.. sends 3 to 0000.. 
  transactions = \
      bytearray([0,2]) + bin2bytes('0'.ljust(num_signature_bits,'0') + '1111'.ljust(num_address_bits,'0')) + int2bytes(1,num_balance_bytes) + \
      bytearray([1,3]) + bin2bytes('0'.ljust(num_signature_bits,'0') + '0000'.ljust(num_address_bits,'0')) + int2bytes(3,num_balance_bytes)
  calldata = encode_chunk(node_labels) + \
             encode_chunk(edge_label_lengths) + \
             encode_chunk(edge_labels) + \
             encode_chunk(modified_subtree_idxs) + \
             encode_chunk(hashes) + \
             encode_chunk(addresses) + \
             encode_chunk(balances) + \
             encode_chunk(transactions)
  calldata = bytearray(calldata)

  state_root = bytearray([0])

  old_root,new_root = main(calldata,state_root)
  if debug:
    print()
    print()
    #print("final pre_hash:", pre_hash)
    #print("final post_hash:", post_hash)


def test_insert_leaves():
  global print_idx
  balance = bytearray([0]*num_balance_bytes)
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
    print("inserting address",address.hex(),"balance",balance)
    neighbor,err = find_account_or_neighbor(tree,address,0)
    if err == "":
      print("tree was empty")
      tree = insert_leaf(neighbor,address,balance=balance)
    elif err=="neighbor":
      print("found neighbor",neighbor,"must insert leaf")
      # must insert next to neighbor
      insert_leaf(neighbor,address,balance=balance)
    elif err=="account":
      print("this account is already present")
    while tree.parent:
      tree=tree.parent
    print("done inserting address",address,"balance",balance)
    # print tree
    print_idx = 0
    print_subtree(tree,0,0)



def test_generator(num_accounts_in_witness, num_accounts_in_state):
  global num_address_bits
  global num_balance_bits
  global num_hash_bits
  global print_idx

  # generate addresses and insert into tree
  tree = None
  import random
  for i in range(num_accounts_in_witness):
    address = bin2bytes(bin(random.randint(0,2**num_address_bits-1))[2:].zfill(num_address_bits))
    balance = bytearray([100]+[0]*(num_balance_bytes-1)) # random.randint(0, 2**num_balance_bits-1)
    print()
    print("inserting address",address.hex(),"balance",balance)
    neighbor,err = find_account_or_neighbor(tree,address,0)
    if err == "":
      print("tree was empty")
      tree = insert_leaf(neighbor,address,balance=balance)
    elif err=="neighbor":
      print("found neighbor",neighbor,"must insert leaf")
      # must insert next to neighbor
      insert_leaf(neighbor,address,balance=balance)
    elif err=="account":
      print("this account is already present")
    while tree.parent:
      tree=tree.parent
    print("done inserting address",address,"balance",balance)
    # print tree
    print_idx = 0
    print_subtree(tree,0,0)




if __name__ == "__main__":
  test_handwritten1()

  num_accounts_in_witness = 3
  num_accounts_in_state = 100
  #test_generator(num_accounts_in_witness, num_accounts_in_state)

  #test_insert_leaves()
