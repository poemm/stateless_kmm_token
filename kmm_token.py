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

memory = bytearray([0]*(2**20))
postbalances_idx = 0
postbalances_byteidx = 0
postbalances_startbyteidx = 0
modified_subtrees_idx = []
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
node_labels_startidx = 0
node_labels_bytelen = 0
node_labels_idx = 0

edge_label_lengths_startidx = 0
edge_label_lengths_bytelen = 0
edge_label_lengths_idx = 0

edge_labels_startidx = 0
edge_labels_bytelen = 0
edge_labels_idx = 0

hashes_startidx = 0
hashes_bytelen = 0
hashes_idx = 0

modified_subtree_idxs_startidx = 0
modified_subtree_idxs_bytelen = 0
modified_subtree_idxs_byteidx = 0

addresses_startbyteidx = 0
addresses_bytelen = 0
addresses_idx = 0
addresses_byteidx = 0

balances_startbyteidx = 0
balances_bytelen = 0
balances_idx = 0

transactions_startidx = 0
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

memory_byteidx = 0
def malloc(num_bytes):
  global memory
  global memory_byteidx
  print("malloc(",num_bytes,")")
  idx = memory_byteidx
  memory_byteidx += num_bytes
  return idx

def memcpy(dst_idx, src_idx, num_bytes):
  print("memcpy(",dst_idx,",",src_idx,",",num_bytes,")")
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
  global node_labels_startidx
  global node_labels_bytelen
  global edge_label_lengths_startidx
  global edge_label_lengths_bytelen
  global edge_labels_startidx
  global edge_labels_bytelen
  global hashes_startidx
  global hashes_bytelen
  global modified_subtree_idxs_startidx
  global modified_subtree_idxs_bytelen
  global addresses_startbyteidx
  global addresses_bytelen
  global balances_startbyteidx
  global balances_bytelen
  global transactions_startidx
  global transactions_bytelen
  global transactions_idx
  global memory
  # helper func
  def get_chunk(memidx):
    len_ = int.from_bytes(memory[memidx:memidx+2], byteorder="little")
    return memidx+2+len_, memidx+2, len_
  # parse
  memory_idx, node_labels_startidx, node_labels_bytelen                = get_chunk(memory_idx)
  memory_idx, edge_label_lengths_startidx, edge_label_lengths_bytelen  = get_chunk(memory_idx)
  memory_idx, edge_labels_startidx, edge_labels_bytelen                = get_chunk(memory_idx)
  memory_idx, modified_subtree_idxs_startidx, modified_subtree_idxs_bytelen = get_chunk(memory_idx)
  memory_idx, hashes_startidx, hashes_bytelen                          = get_chunk(memory_idx)
  memory_idx, addresses_startbyteidx, addresses_bytelen                    = get_chunk(memory_idx)
  memory_idx, balances_startbyteidx, balances_bytelen                      = get_chunk(memory_idx)
  memory_idx, transactions_startidx, transactions_bytelen              = get_chunk(memory_idx)







   


# 1) copy pre-balances to post-balances








# 2) build each modified subtree

# some getters
def get_next_node_label():
  # this is used to build subtree and to merkleize pre&post
  global node_labels_idx
  global node_labels_startidx
  #print("get_next_node_label()",node_labels_startidx,node_labels_idx)
  # get byte and bit
  byteidx = node_labels_idx // 4
  bitidx =  2 * (node_labels_idx % 4)
  # increment for next time
  node_labels_idx += 1
  # get two bits
  byte = memory[node_labels_startidx+byteidx]
  byte = (byte << bitidx) % 256
  byte >>= 6
  return byte

def get_next_edge_label_length():
  # this is used to build subtree and to merkleize pre&post
  global edge_label_lengths_idx
  global edge_label_lengths_startidx
  #print("get_next_edge_label_length()",edge_label_lengths_startidx,edge_label_lengths_idx)
  len_ = memory[edge_label_lengths_startidx+edge_label_lengths_idx]
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
  global modified_subtree_idxs_startidx
  global modified_subtree_idxs_bytelen
  global modified_subtree_idxs_byteidx
  global next_modified_subtree_node_label_idx
  if modified_subtree_idxs_byteidx-modified_subtree_idxs_startidx == modified_subtree_idxs_bytelen:
    next_modified_subtree_node_label_idx = 0
  else:
    next_modified_subtree_node_label_idx = int.from_bytes(memory[modified_subtree_idxs_byteidx:modified_subtree_idxs_byteidx+2], byteorder="little")
    modified_subtree_idxs_byteidx += 11
  return next_modified_subtree_node_label_idx

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
  global hashes_startidx
  hash_idx = hashes_idx
  hash_byteidx = hashes_startidx + hash_idx*num_hash_bytes
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
# instantiated in build_tree_from_node_labels(), build_modified_subtrees(), and insert_leaf()
num_treenode_bytes = 15+num_address_bytes
class Tree_node():
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

    """
    # this may be helful in handling these
    self.parent_byteidx_uint32ptr           = self.parent_byteidx.cast("I")
    self.left_or_address_byteidx_uint32ptr  = self.left_byteidx.cast("I")
    self.right_or_balance_byteidx_uint32ptr = self.right_byteidx.cast("I")
    self.node_type_uint8ptr                 = self.node_type.cast("B")
    self.edge_label_len_uint8ptr            = self.edge_label_len.cast("B")
    self.edge_label_len_total_uint8ptr      = self.edge_label_len_total.cast("B")
    self.edge_label_uint8ptr                = self.edge_label.cast("B")
    """

  """
  def unpack(self):
    self.parent_byteidx = self.mv[self.startbyteidx:self.startbyteidx+4].cast("I")
    self.left_or_address_byteidx = self.mv[self.startbyteidx+4:self.startbyteidx+8].cast("I")
    self.right_or_balance_byteidx = self.mv[self.startbyteidx+8:self.startbyteidx+12].cast("I")

  def pack(self):
    self.mv[self.startbyteidx:self.startbyteidx+4] = self.parent_byteidx
    self.mv[self.startbyteidx+4:self.startbyteidx+8] = self.left_or_address_byteidx
    self.mv[self.startbyteidx+8:self.startbyteidx+12] = self.right_or_balance_byteidx
  """


debug_build_idx = 0
def build_tree_from_node_labels(edge_label_len_total, node):
  global num_address_bits
  global addresses_byteidx
  global num_address_bytes
  global postbalances
  if debug:
    global debug_build_idx
    debug_build_idx+=1
    print("  ",debug_build_idx,"build_tree_from_node_labels(",edge_label_len_total,")")
  # get node label
  node_label = get_next_node_label()
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
      print("there is an edge label, get it")
      node.edge_label_len[0] = get_next_edge_label_length()
      edge_label_len_total += node.edge_label_len[0]
      node.edge_label_len_total[0] = edge_label_len_total
      print("edge_label_len, edge_label_len_total",node.edge_label_len[0],node.edge_label_len_total[0])
      print("addresses_byteidx",addresses_byteidx)

      get_bits_big_endian(node.edge_label, memory, addresses_byteidx+edge_label_len_total, node.edge_label_len[0])
      # either leaf or not leaf
      if debug: print("if leaf then true: ",node.edge_label_len_total[0] == num_address_bits-1, node.edge_label_len_total[0], num_address_bits-1)
      if node.edge_label_len_total[0] == num_address_bits-1:
        if debug: print(debug_build_idx,"build_tree_from_node_labels(",edge_label_len_total,")","found leaf")
        node.left_or_address_byteidx.cast('I')[0] = get_next_address_byteidx()
        node.right_or_balance_byteidx.cast('I')[0] = get_next_postbalance_byteidx()
        node.node_type[0] = 0b00
        return
      else:
        # not a leaf, get next node label and process it below
        node_label = get_next_node_label()
        if debug: print(debug_build_idx,"build_tree_from_node_labels(",edge_label_len_total,")","node_label after 00",node_label)
  # this is an internal node, we already got the edge label if there was one
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
def build_modified_subtrees():
  global num_modified_subtrees
  modified_subtrees = [Tree_node(malloc(num_treenode_bytes))]*num_modified_subtrees
  global modified_subtree_idxs_bytelen
  global node_labels_idx
  global edge_label_lengths_idx
  global edge_labels_idx
  global hashes_idx
  global addresses_byteidx
  global postbalances_idx
  modified_subtree_idxs_byteidx = modified_subtree_idxs_startidx
  for i in range(num_modified_subtrees):
    # first get all relevant idxs
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
    # build subtree
    build_tree_from_node_labels(edge_label_len_total, modified_subtrees[i])
    edge_label_startbitidx = 8*(addresses_startbyteidx+addresses_idx*num_address_bytes)
    #edge_label_endbitidx = edge_label_startbitidx + edge_label_len_total-1
    modified_subtrees[i].edge_label_len_total[0] = edge_label_len_total 
    get_bits_big_endian(modified_subtrees[i].edge_label,memory,edge_label_startbitidx,edge_label_len_total)
    #modified_subtrees[i].edge_label[:] = edge_label + bytearray([0]*(num_address_bytes-len(edge_label)))
    #print("modified_subtrees[",i,"] info:",modified_subtrees[i].edge_label,addresses_startbyteidx+addresses_idx*num_address_bytes,addresses_startbyteidx+addresses_idx*num_address_bytes+edge_label_len_total-1)
    #modified_subtrees[i].edge_label_len = edge_label_len_total
  return modified_subtrees



  







# 3) process transactions 

def find_account_or_neighbor(node,address_startbyteidx):
  print("find_account_or_neighbor(",node,address_arr.hex(),address_startbyteidx,")")
  if node==None:
    return None, ""
  depth = node.edge_label_len_total
  #if node.leaf_balance_arr != None: # already at leaf
  if node.node_type == 0b00: # leaf
    leaf_address = memory[node.leaf_address_byteidx:node.leaf_address_byteidx+num_address_bytes]
    if leaf_address == memory[address_startbyteidx:address_startbyteidx+num_address_bytes]:
      #print("found account")
      return node, "account"
    else:
      #print("found neighbor")
      return node, "neighbor"
  if node.edge_label_len>0:
    print("have edge label")
    corresponding_bits = get_bits_big_endian(memory[address_startbyteidx:address_startbyteidx+num_address_bytes],depth-node.edge_label_len,depth)
    print(node.edge_label,corresponding_bits)
    if node.edge_label != corresponding_bits:
      #print("found neighbor")
      return node, "neighbor" # leaf not present, must insert
  bit = get_bits_big_endian(memory[address_startbyteidx:address_startbyteidx+num_address_bytes],depth+1,depth+1)
  print("bit",bit)
  if bit:
    print("recurse right",bit)
    return find_account_or_neighbor(node.right, address_startbyteidx)
  else:
    print("recurse left",bit)
    return find_account_or_neighbor(node.left, address_startbyteidx)


def insert_leaf(neighbor,address,balance=0):
  print("insert_leaf(",neighbor,",",address.hex(),")")
  # if tree is empty, insert this address and balance and return
  if neighbor == None:
    new_leaf = Tree_node()
    new_leaf.node_type = 0b00
    new_leaf.leaf_address_arr = address
    new_leaf.leaf_address_byteidx = 0
    new_leaf.leaf_balance_arr = bytearray([0]*num_balance_bytes)
    new_leaf.leaf_balance_byteidx = 0
    new_leaf.edge_label_len = num_address_bits - 1
    new_leaf.edge_label_len_total = num_address_bits - 1
    new_leaf.edge_label = address[0:num_address_bytes]
    return new_leaf
  # find the leaf, possibly inserting it
  # get bit where address and edge_label diverge
  #print("neighbor.edge_label_len",neighbor.edge_label_len)
  #print_node(neighbor,10)
  i=0
  while i < neighbor.edge_label_len:
    print("i",i)
    bit_idx = neighbor.edge_label_len_total-neighbor.edge_label_len+i
    addybit = get_bits_big_endian(address,bit_idx,bit_idx)
    edge_label_bit = get_bits_big_endian(neighbor.edge_label,i,i)
    print(addybit,edge_label_bit)
    if addybit != edge_label_bit:
      break
    i+=1
  print("final i",i)
  # insert node
  new_interior_node = Tree_node()
  new_interior_node.node_type = 0b11
  new_leaf = Tree_node()
  new_leaf.node_type = 0b00
  new_leaf.leaf_address_arr = address
  new_leaf.leaf_address_byteidx = 0
  new_leaf.leaf_balance_arr = bytearray([0]*num_balance_bytes)
  new_leaf.leaf_balance_byteidx = 0
  # first take care of edge labels and lengths
  new_interior_node.edge_label_len = i
  new_interior_node.edge_label_len_total = neighbor.edge_label_len_total - neighbor.edge_label_len + i
  print("new_interior_node.edge_label_len_total",new_interior_node.edge_label_len_total)
  if new_interior_node.edge_label_len:
    print("ok1")
    startidx = neighbor.edge_label_len_total-neighbor.edge_label_len
    endidx = startidx+new_interior_node.edge_label_len-1
    new_interior_node.edge_label = get_bits_big_endian(address,startidx,endidx)
  else:
    print("ok2")
    new_interior_node.edge_label = bytearray([])
  print("ok3")
  new_leaf.edge_label_len = num_address_bits - new_interior_node.edge_label_len_total-1
  new_leaf.edge_label_len_total = num_address_bits-1
  new_leaf.edge_label = get_bits_big_endian(address,new_interior_node.edge_label_len_total,num_address_bits-1)
  neighbor.edge_label_len -= i
  if neighbor.edge_label_len==0:
    print("ok4")
    neighbor.edge_label = bytearray([])
  else:
    print("ok5")
    #neighbor.edge_label = get_bits_big_endian(neighbor.edge_label,i+1,i+1+neighbor.edge_label_len)
    startidx = neighbor.edge_label_len_total-neighbor.edge_label_len+i-1
    endidx = neighbor.edge_label_len_total
    neighbor.edge_label = get_bits_big_endian(neighbor.edge_label,startidx,endidx)
  # adjust parents and children
  new_leaf.parent = new_interior_node
  new_interior_node.parent = neighbor.parent
  if neighbor.parent:
    if neighbor.parent.left == neighbor:
      neighbor.parent.left = new_interior_node
    else:
      neighbor.parent.right = new_interior_node
  neighbor.parent = new_interior_node
  # two cases: diverge left or right
  #print("ok",addybit,new_interior_node)
  if addybit==bytearray(b'\x00'): # diverge right
    new_interior_node.right = neighbor
    new_interior_node.left = new_leaf
  else: # diverge left
    new_interior_node.left = neighbor
    new_interior_node.right = new_leaf
  return new_leaf


def delete_node(parent,side):
  pass

def process_transactions():
  print()
  print()
  print("process_transactions()")
  global transactions_startidx
  global transactions_bytelen
  global memory
  global num_modified_subtrees
  num_balances = balances_bytelen//num_balance_bytes
  txs_idx = transactions_startidx
  txs_end_idx = transactions_startidx+transactions_bytelen
  while txs_idx < txs_end_idx:
    print()
    print("transaction",txs_idx)
    # parse tx
    from_idx = int.from_bytes(memory[txs_idx:txs_idx+1],"little")
    to_idx = int.from_bytes(memory[txs_idx+1:txs_idx+2],"little")
    txs_idx += 2
    signature = memory[txs_idx:txs_idx+num_signature_bytes]
    txs_idx += num_signature_bytes
    to_address_idx = txs_idx
    txs_idx += num_address_bytes
    value = int.from_bytes(memory[txs_idx:txs_idx+num_balance_bytes],"little")
    txs_idx += num_balance_bytes
    # get accounts
    # first from address
    from_address_array_idx = addresses_startbyteidx + from_idx*num_address_bytes
    # next from balance
    if from_idx < num_balances:
      from_balance_array = postbalances
      from_balance_array_idx = from_idx*num_balance_bytes
      #from_balance_array = postbalances
      #from_balance_array_idx = from_idx*num_balance_bytes
    elif from_idx < num_balances + num_modified_subtrees:
      node,err = find_account_or_neighbor(modified_subtrees[from_idx-num_orignal_accounts],from_address_array_idx)
      if err=="neighbor": return -1 # error, must be present, otherwise zero balance
      from_balance_array = node.leaf_balance_arr
      from_balance_array_idx = node.leaf_balance_byteidx
    else:
      return -1 # error
    # similarly for to address and balance, note we already have to address from signature message
    if to_idx < num_balances:
      to_balance_array = postbalances
      to_balance_array_idx = to_idx*num_balance_bytes
    elif to_idx < num_balances + num_modified_subtrees:
      # traverse tree until leaf, possibly inserting a new leaf
      print("to_idx,num_orignal_accounts",to_idx,num_original_accounts)
      node,err = find_account_or_neighbor(modified_subtrees[to_idx-num_original_accounts],to_address_idx)
      # if not a leaf, must insert leaf
      if err!="account":
        node = insert_leaf(node,to_address_idx)
      to_balance_array = node.leaf_balance_arr
      to_balance_array_idx = node.leaf_balance_byteidx
    else:
      return -1 # error
    # apply balance change
    print("to_balance bytes",to_balance_array[to_balance_array_idx:to_balance_array_idx+num_balance_bytes])
    print("from_balance bytes",from_balance_array[from_balance_array_idx:from_balance_array_idx+num_balance_bytes])
    from_balance = int.from_bytes(from_balance_array[from_balance_array_idx:from_balance_array_idx+num_balance_bytes],"little")
    to_balance = int.from_bytes(to_balance_array[to_balance_array_idx:to_balance_array_idx+num_balance_bytes],"little")
    if from_balance<value:
      return -1 # error
    from_balance -= value
    to_balance += value
    # if from_balance==0: delete_node()
    print("old and new balance")
    print(to_balance_array,to_balance_array_idx)
    to_balance_array[to_balance_array_idx:to_balance_array_idx+num_balance_bytes] = to_balance.to_bytes(num_balance_bytes, byteorder='little')
    print(to_balance_array[to_balance_array_idx:to_balance_array_idx+num_balance_bytes])
    print(to_balance.to_bytes(num_balance_bytes, byteorder='little'))
    from_balance_array[from_balance_array_idx:from_balance_array_idx+num_balance_bytes] = from_balance.to_bytes(num_balance_bytes, byteorder='little')
    print("to_balance bytes",to_balance_array[to_balance_array_idx:to_balance_array_idx+num_balance_bytes])
    print("from_balance bytes",from_balance_array[from_balance_array_idx:from_balance_array_idx+num_balance_bytes])
  print("done with process_transactions()")
  print()
  print()








# 4) Merkleize pre and post root

def hash_(bytes_):
  return bytes_

def merkleize_modifiable_subtree(node,recursion_depth=0):
  print(recursion_depth," "*recursion_depth+"merkleize_modifiable_subtree(",node,recursion_depth,")")
  #print(node.leaf_balance_arr)
  if node.node_type==0b00: # leaf
    print(recursion_depth," "*recursion_depth+"leaf")
    #print(recursion_depth," "*recursion_depth+"node.leaf_address_arr==memory",node.leaf_address_arr==memory,"node.leaf_address_byteidx",node.leaf_address_byteidx)
    leaf_address = node.leaf_address_arr[node.leaf_address_byteidx:node.leaf_address_byteidx+num_address_bytes]
    leaf_balance = node.leaf_balance_arr[node.leaf_balance_byteidx:node.leaf_balance_byteidx+num_balance_bytes]
    #print(recursion_depth," "*recursion_depth+"leaf_address,leaf_balance",leaf_address,leaf_balance)
    return hash_(leaf_address+leaf_balance+bytearray([node.edge_label_len]))
  else:
    print(recursion_depth," "*recursion_depth+"not leaf, must recurse")
    # left hash
    if node.node_type == 0b01:
      print(recursion_depth," "*recursion_depth+"left hash available",node.lefthash_idx)
      left_hash = memory[hashes_startidx+node.lefthash_idx*num_hash_bytes:hashes_startidx+node.lefthash_idx*num_hash_bytes+num_hash_bytes]
      right_hash = merkleize_modifiable_subtree(node.right,recursion_depth=recursion_depth+1)
    elif node.node_type == 0b10:
      left_hash = merkleize_modifiable_subtree(node.left,recursion_depth=recursion_depth+1)
      right_hash = memory[hashes_startidx+node.righthash_idx*num_hash_bytes:hashes_startidx+node.righthash_idx*num_hash_bytes+num_hash_bytes]
    elif node.node_type == 0b11:
      left_hash = merkleize_modifiable_subtree(node.left,recursion_depth=recursion_depth+1)
      right_hash = merkleize_modifiable_subtree(node.right,recursion_depth=recursion_depth+1)
    print(recursion_depth," "*recursion_depth+"right_hash",right_hash,"left_hash",left_hash)
    # edge label and return hash
    return hash_(left_hash+right_hash+bytearray([node.edge_label_len]))


modifiable_subtree_idx = 0
def merkleize_pre_and_post(depth,post_flag,recursion_depth):
  print(recursion_depth," "*recursion_depth+"merkleize_pre_and_post(",depth,post_flag,recursion_depth,")")
  global memory
  global modifiable_subtree_idx
  global node_labels_idx
  global account_idx
  edge_label_len = 0
  #node_labels_idx += 1
  post_hash = None
  #print(recursion_depth," "*recursion_depth+"node_labels_idx",node_labels_idx,"next_modifiable_subtree_node_label_idx",next_modified_subtree_node_label_idx)
  if node_labels_idx == next_modified_subtree_node_label_idx:
    post_flag = False
    node = modified_subtrees[modifiable_subtree_idx]
    modifiable_subtree_idx+=1
    get_next_modified_subtree_node_label_idx()
    print(recursion_depth," "*recursion_depth+"merklizing modifiable_subtree")
    print()
    post_hash = merkleize_modifiable_subtree(node)
    print()
    print(recursion_depth," "*recursion_depth+"returned from merkleize_modifiable_subtree with hash",post_hash)
  node_label = get_next_node_label()
  #print(recursion_depth," "*recursion_depth+"node_label ",node_label)
  if node_label == 0b00:
    print(recursion_depth," "*recursion_depth+"node_label == 0b00")
    #print(recursion_depth," "*recursion_depth+"depth",depth,"num_address_bis",num_address_bits)
    if depth==num_address_bits-1: # leaf with no edge label, this is rare
      address = memory[addresses_startbyteidx+account_idx*num_address_bytes:addresses_startbyteidx+(account_idx+1)*num_address_bytes]
      pre_balance = memory[balances_startbyteidx+account_idx*num_balance_bytes:balances_startbyteidx+(account_idx+1)*num_balance_bytes]
      pre_hash = hash_(address+pre_balance)
      if post_hash==None:
        post_balance = postbalances[account_idx*num_balance_bytes:account_idx*num_balance_bytes+num_balance_bytes]
        post_hash = hash_(address+post_balance+bytearray([0]))
      account_idx = get_next_account_idx()
      print(recursion_depth," "*recursion_depth+"1pre_hash:", pre_hash)
      print(recursion_depth," "*recursion_depth+"post_hash:", post_hash)
      print()
      return pre_hash,post_hash
    else: 
      edge_label_len = get_next_edge_label_length()
      print(recursion_depth," "*recursion_depth+"edge_label_len",edge_label_len)
      depth += edge_label_len
      #print(recursion_depth," "*recursion_depth+"    edge_label_len",edge_label_len)
      #print(recursion_depth," "*recursion_depth+depth,num_address_bits-1)
      if depth==num_address_bits-1: # a leaf with an edge label
        address = memory[addresses_startbyteidx+account_idx*num_address_bytes:addresses_startbyteidx+(account_idx+1)*num_address_bytes]
        pre_balance = memory[balances_startbyteidx+account_idx*num_balance_bytes:balances_startbyteidx+(account_idx+1)*num_balance_bytes]
        pre_hash = hash_(address+pre_balance+bytearray([edge_label_len]))
        #print(recursion_depth," "*recursion_depth+"address, pre_balance, edge_label_len",address,pre_balance,edge_label_len)
        if post_hash==None:
          post_balance = postbalances[account_idx*num_balance_bytes:account_idx*num_balance_bytes+num_balance_bytes]
          post_hash = hash_(address+post_balance+bytearray([edge_label_len]))
        account_idx = get_next_account_idx()
        print(recursion_depth," "*recursion_depth+"2pre_hash:", pre_hash)
        print(recursion_depth," "*recursion_depth+"post_hash:", post_hash)
        print()
        return pre_hash,post_hash
      else: # not a leaf, get next node label and process it below
        node_label = get_next_node_label()
    #print(recursion_depth," "*recursion_depth+"node_label after 00",node_label)
  if node_label == 0b01:
    print(recursion_depth," "*recursion_depth+"node_label == 0b01")
    #print(recursion_depth," "*recursion_depth+"ok 01")
    pre_hash_right,post_hash_right = merkleize_pre_and_post(depth+1,post_flag,recursion_depth+1)
    hash_left_byte = get_next_hash_byteidx()
    hash_left = memory[hash_left_byteidx:hash_left_byteidx+num_hash_bytes]
    pre_hash = hash_(hash_left+pre_hash_right+bytearray([edge_label_len])) 
    if post_hash==None:
      post_hash = hash_(hash_left+post_hash_right+bytearray([edge_label_len])) 
    print(recursion_depth," "*recursion_depth+"3pre_hash:", pre_hash)
    print(recursion_depth," "*recursion_depth+"post_hash:", post_hash)
    print()
    return pre_hash, post_hash
  elif node_label == 0b10:
    print(recursion_depth," "*recursion_depth+"node_label == 0b10")
    #print(recursion_depth," "*recursion_depth+"ok 10")
    pre_hash_left,post_hash_left = merkleize_pre_and_post(depth+1,post_flag,recursion_depth+1)
    hash_right_byteidx = get_next_hash_byteidx()
    hash_right = memory[hash_right_byteidx:hash_right_byteidx+num_hash_bytes]
    #print(recursion_depth," "*recursion_depth+"4hashes_startidx, hash_right_byteidx", hashes_startidx,hash_right_byteidx)
    #print(recursion_depth," "*recursion_depth+"4hash_right",hash_right)
    #print(recursion_depth," "*recursion_depth+"4hash_right_byteidx",hash_right_byteidx)
    #print(recursion_depth," "*recursion_depth+"4hash_right",hash_right)
    #print(recursion_depth," "*recursion_depth+"4edge_label_len",edge_label_len)
    pre_hash = hash_(pre_hash_left+hash_right+bytearray([edge_label_len])) 
    print(recursion_depth," "*recursion_depth+"4post_hash",post_hash)
    if post_hash==None:
      post_hash = hash_(post_hash_left+hash_right+bytearray([edge_label_len])) 
    print(recursion_depth," "*recursion_depth+"4pre_hash:", pre_hash)
    print(recursion_depth," "*recursion_depth+"4post_hash",post_hash)
    print()
    return pre_hash, post_hash
  elif node_label == 0b11:
    print(recursion_depth," "*recursion_depth+"node_label == 0b11")
    #print(recursion_depth," "*recursion_depth+"ok 11")
    pre_hash_left,post_hash_left = merkleize_pre_and_post(depth+1,post_flag,recursion_depth+1)
    pre_hash_right,post_hash_right = merkleize_pre_and_post(depth+1,post_flag,recursion_depth+1)
    pre_hash = hash_(pre_hash_left+pre_hash_right+bytearray([edge_label_len])) 
    if post_hash==None:
      post_hash = hash_(post_hash_left+post_hash_right+bytearray([edge_label_len])) 
    print(recursion_depth," "*recursion_depth+"5pre_hash:", pre_hash)
    print(recursion_depth," "*recursion_depth+"post_hash:", post_hash)
    print()
    return pre_hash, post_hash
  return None, None
  



def init_merkleization_and_merkleize():
  global node_labels_idx
  global edge_label_lengths_startidx
  global edge_labels_startidx
  global edge_label_lengths_idx
  global hashes_idx
  global modified_subtree_idxs_startidx
  global addresses_startbyteidx
  global balances_startbyteidx
  global transactions_startidx
  node_labels_idx = 0
  edge_label_lengths_idx = 0
  edge_labels_idx = edge_labels_startidx
  hashes_idx = 0
  addresses_byteidx = addresses_startbyteidx
  balances_idx = balances_startbyteidx
  transactions_idx = transactions_startidx
  # node label
  global modified_subtree_idxs_byteidx
  global next_modified_subtree_node_label_idx
  modified_subtree_idxs_byteidx = modified_subtree_idxs_startidx
  get_next_modified_subtree_node_label_idx()
  # other globals
  global modifiable_subtree_idx
  modifiable_subtree_idx = 0
  global account_idx
  account_idx = 0
  # finally, compute new and old hashes
  pre_hash, post_hash = merkleize_pre_and_post(0,True,0)
  return pre_hash, post_hash










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
    print("node_labels idxs",node_labels_startidx, node_labels_bytelen)
    print("edge_label_lengths idx",edge_label_lengths_startidx, edge_label_lengths_bytelen)
    print("edge_labels idxs",edge_labels_startidx, edge_labels_bytelen)
    print("modified_subtrees idxs",modified_subtree_idxs_startidx, modified_subtree_idxs_bytelen)
    print("hashes idxs",hashes_startidx, hashes_bytelen)
    print("addresses idxs",addresses_startbyteidx, addresses_bytelen)
    print("balances idxs",balances_startbyteidx, balances_bytelen)
    print("transactions idxs",transactions_startidx, transactions_bytelen)



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
  modified_subtrees = build_modified_subtrees()
  # print them
  if debug:
    print()
    print("printing subtrees")
    for ms in modified_subtrees:
      print_subtree2(ms.startbyteidx,0,0)


  return None,None


  """
  # 3) process transactions 
  if debug:
    print()
    print("3) process transactions")
  process_transactions()
  # print subtrees
  if debug:
    global print_idx
    print_idx = 0
    for ms in modified_subtrees:
      print_subtree(ms,0,0)
    # print prebalances
    print()
    print("prebalances")
    for i in range(len(postbalances)//num_balance_bytes):
      print(int.from_bytes(memory[balances_startbyteidx+i*num_balance_bytes:balances_startbyteidx+i*num_balance_bytes+num_balance_bytes], byteorder="little"))
    print()
    # print postbalances
    print()
    print("postbalances")
    for i in range(len(postbalances)//num_balance_bytes):
      print(int.from_bytes(postbalances[i*num_balance_bytes:i*num_balance_bytes+num_balance_bytes], byteorder="little"))
    print()


  # 4) Merkleize pre and post root
  if debug:
    print()
    print("4) Merkleize pre and post root")
  computed_old_root,new_root = init_merkleization_and_merkleize()

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
  # modified_subtree_idxs - node label idx, edge label lengths idx, edge labels idx, hashes idx, accounts idx, depth
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
