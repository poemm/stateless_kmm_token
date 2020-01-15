# Stateless KMM (Katajainen, Makinen, Merkle) Token

THIS IS BEING OVERHAULED.

## The Code

`kmm_token.py` is for prototyping, it is more C-like than Pythonic. `kmm_token.c` is for performance and to compile to WebAssembly.


# Design and Implementation of a Stateless Merkle Token Contract

## ABSTRACT

Stateful blockchains are said to be unsustainable because of state growth. The stateless model solves this problem, but has its own problems with witness size. We design and implement a stateless token contract which stores only a Merkle state root on chain, and passes Merkle witnesses as calldata along with transactions. We aim to achieve theoretical minimums for witness size. We also optimize for speed for on-chain `Merkleize()`, `insert_leaf()`, `delete_leaf()`, and `update_leaf()`. And we provide infrastructure for off-chain witness generation.


## Introduction

We design and implement a stateless token contract for blockchains like Ethereum. Our contract (i) takes the witnesses and transactions from calldata, (ii) verifies account balances against the on-chain state hash, (iii) applies transactions as balance transfers, and (iv) Merkleizes the post-transfer balances and updates the state hash. Our two bottlenecks are calldata size and contract execution time, for which we dedicate great emphais in optimizing. This work is for tokens, but can easily be applied to any data stored statelessly.

Related work includes Vitalik Buterin et. al.'s [SSZ partials as Merkle proofs](https://github.com/ethereum/eth2.0-specs/pull/1186/), and Alexey Akhunov's [Merkle proofs for Eth 1.0](https://github.com/ledgerwatch/turbo-geth/blob/visual/docs/programmers_guide/guide.md), and ProtoLambda's [Remerkleable](https://github.com/protolambda/remerkleable).



## Binary Tree

**Definition.** [Knuth, 1997, pg 312]
A *binary tree* is a finite set of nodes that either is empty, or consists of a root and the elements of two disjoint binary trees called the left and right subtrees of the root.

**Definitions.**
The *root node* of tree is the distinguished node which was not part of any left or right subtree.

A *leaf node* of a binary tree has empty left and right subtrees.

An *internal node* is any node that is not a leaf nodes.

A *child node* of a node, is the root of a subtree of that node.

The *parent node* of a node, if it exists, is the node which has that node as a child.

An *edge* is a relationship between a node and its child, drawn as a line segment between them.



**Example.** Enumerate all binary trees up to three nodes. By convention, the root node is at the top and the leaves are at the bottom.
```
zero nodes:
(empty tree)

One node:
   x

Two nodes:
    x  x
   /    \
  x      x

Three nodes:
   x        x      x   x     x
  / \      /      /     \     \
 x   x    x      x       x     x
         /       \      /       \
        x         x    x         x
```


## Node Labels, Children Pattern Sequence

**Definition** A tree with *node labels* has a label at each node, where each label is an element from any set. (We use binary strings from the set of all binary strings.)

**Definition.** [Katajainen and Makinen, 1990]
A *children pattern sequence* is as follows: Label each node of binary tree `00` for leaf, `01` if it only has a right child, `10` if it only has a left child, and `11` if it has two children. Traverse in [depth-first pre-order](https://en.wikipedia.org/wiki/Tree_traversal#Pre-order_(NLR)) collecting the sequence of labels.

**Example.** Consider leaves with paths: `01`, `1100`, `1101`
```
     11
    /  \
   01  01
    \    \
    00   10
         /
        11
       /  \
      00   00

Children Pattern Sequence: 11 01 00 01 10 11 00 00
```

**Remark.** In the example, note that the tree can be recovered with just the Children Pattern Sequence.



## Edge Labels, Prefix Tree ("Trie"), Radix Tree, Paths

**Definition.** A tree with *edge labels* has a label on each edge. Where labels are binary strings.

**Definition.** A *prefix tree* ("trie") is a tree with edge labels, and each node has a unique label to each of its children.

**Definition** A *binary path* to a node of a binary tree: Consider a prefix binary tree with label `0` on each edge to a left child and `1` on each edge to a right child. Traverse from root to the node, append `0` if visit left child and `1` if visit right child, finish with a sequence of `0`'s and `1`'s.

**Definition.** An *edge label sequence* is as follows: Label each edge of binary tree `0` if it is to the left child and `1` if it is to the right child. Traverse in [depth-first pre-order](https://en.wikipedia.org/wiki/Tree_traversal#Pre-order_(NLR)) collecting the sequence of labels.

**Example.** A prefix tree with label `0` on left edges and `1` on right edges. Leaves have paths `01`, `1100`, and `1101`. Get the edge label sequence.
```
     x
   0/  \1
   x    x
    \1   \1
     x    x
        0/
        x
      0/  \1
      x    x

Edge Label Sequence: 0 1 1 1 0 0 1
```

**Definition.** A *radix tree* is a prefix tree with minumum number of nodes -- each node which is an only child is removed and its edge above and below become a single edge with their labels concatenated.

**Example.** The same tree as a radix tree.
```
      x
   01/ \110
    x   x
      0/ \1
      x   x

Edge Label Sequence: 01 110 0 1
```

**Example.** Same radix tree, but with edge labels for Child Pattern Sequence. Get the Children Pattern Sequence and the Edge Label Sequence.
```
     11
   01/ \110
    00  11
      0/ \1
      00  00

Children Pattern Sequence: 11 00 11 00 00
Edge Label sequence: 01 110 0 1
```

**Remark.** Note that the trees can be recovered from their Children Pattern Sequence and Edge Label sequence.



## Fixed Depth Tree, Fixed-length binary path tree

**Definition.**
The *depth* of the node in a tree is the number of edges between it and the root.
A *fixed depth tree* has all leaves at the same depth.

**Example.** Consider fixed depth binary tree of depth 3, and paths to leaves: `010`, `110`, `111`.
```
     x
    /  \
   x    x
  / \    \
 x   x    x 
 \    \    \
  x    x    x 

Corresponding radix tree using label 0 for left child and 1 for right child:
     x 
   0/  \111
   x    x 
01/\11   
 x  x     
Edge label sequence: 0 01 11 111

Corresponding node labels for Children Pattern Sequence.
     11 
    /  \
   11   00 
  /\     
 00 00    

Node label sequence: 11 11 00 00 00
```

**Definition.** A *fixed-length binary-path radix tree* is a radix tree with each binary path to each leaf having the same length. (It is in bijection to fixed depth trees.)



## Linked Parent-Child tree representation

**Definition.** A *linked parent-child* is a representation of a tree in computer memory where each parent node is a data structure with memory pointers to each of its children. If a child is not present, its memory location is 0, and no node may be at memory location 0.

```
     a
    /  \
   b    c
  / \    \
 d   e    f 
 \    \   / \
  g    h  i  j 

Representation:
node a:
  left child: memory location of b
  right child: memory location of c
node b:
  left child: memory location of d
  right child: memory location of e
node c:
  left child: 0
  right child: memory location of f
node d: 
  left child: 0
  right child: memory location of g
node e:
  left child: 0
  right child: memory location of h
node f:
  left child: memory location of i
  right child: memory location of j
node g:
  left child: 0
  right child: 0
node h:
  left child: 0
  right child: 0
node i:
  left child: 0
  right child: 0
node j:
  left child: 0
  right child: 0
```

**Remark.** This encoding is known for fast insert and delete operations.





## Merkle tree, Merkle witness encoding

**Definition.** A *Merkle tree* is a tree with a hash at each node. The hash is computed by taking the concatenation of it's child hashes possibly interspersed with other data, with the special case that the hash of a leaf is the hash of the concatenation of the binary path and the value at the leaf, possibly interspersed with other data.

**Definition.** A *KMM witness* of a set of leaves in a fixed-length-binary-path radix tree is an encoding of a tree with possibly some omitted subtrees replaced by their Merkle hashes. And some optimizations that follow. Omit the first bit of each edge label, put a `00` label before each node with a an edge to its parent with label length greater than 1, except for leaves because you can determine if they are leaves based on the prefix length at that point in the traversal. A node with a hash on left has label `01` and right `10`.

**Example.** Consider the tree in the above example. A KMM witness for leaves at paths `011` `110` is as follows.
```

     11
    /  \1
   01  0010
  /\1   /\ 
 h1 00 00 h2  


Leaf path sequence: 011 110
Node Label sequence: 11 01 00 0010 00
Edge Label sequence: 1 1
Edge Label length sequence minus one: 1 1
hash sequence: h1 h2
```

**Remark.** We only need one of Leaf path sequence or Edge Label sequence, because we can recover the other one if needed.

**Remark.** This encoding is space-efficient. And convenient for Merkleization, which is a single traversal.




## Fixed-Depth Binary Tree To Represent Token Accounts

**Remark.** Notice that for a fixed-depth binary tree, the path to each leaf corresponds to a unique fixed-length binary string. So each leaf can correspond to a 256-bit token address, since an address is a fixed-length binary sequence. The balance can also be stored at the leaf, and all accounts can be represented as such a binary tree.



## Binary Encoding of Merkle Witness


## Algorithm: Address(es) Recovery.


## Algorithm: Merkleizing


## Token Transactions


## The Full Token Contract


## Merkle Proof Sizes


## Contract Execution Speed


## Attacks


## References

[Knuth, 1997] Knuth, Art of Computer Programming, Volume 1, 3rd ed.

[Katajainen and Makinen, 1990] Katajainen, Makinen. Tree Compression and Optimizatin With Applications, 1990. 


