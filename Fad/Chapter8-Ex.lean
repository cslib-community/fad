import Fad.Chapter8

namespace Chapter8

/-!
# Exercises
-/

/-!
## Exercise 8.1
Consider the recurrence `H(1) = 0` and `H(n) = 1 + H(⌈n/2⌉)`. Prove by
induction that `H(n) = ⌈log n⌉`.
-/

-- TODO

/-!
## Exercise 8.2
Prove that the bottom-up algorithm
  `mktree = unwrap · until single (pairWith Node) · map Leaf`
of Section 8.1 produces a tree of minimum height.
-/

-- TODO

/-!
## Exercise 8.3
We claimed in Section 8.1 that minimising `lcost` also minimises `cost`.
Why is this true?
-/

-- TODO

/-!
## Exercise 8.4
Why is the claim `rollup · spine = id` not true for all possible lists
of trees?
-/

-- TODO

/-!
## Exercise 8.5
The (context-free) fusion rule for `foldrn` asserts that
  `foldrn f₂ g₂ xs ← M (foldrn f₁ g₁ xs)`
for all finite lists `xs`, provided
  `g₂ x ← M (g₁ x)`
  `f₂ x (M y) ← M (f₁ x y)`
Prove this result.
-/

-- TODO

/-!
## Exercise 8.6
Specialise the final greedy algorithm of Section 8.1 as suggested to
build a minimum-height tree.
-/

-- TODO

/-!
## Exercise 8.7
The function `splits : [a] → [([a], [a])]` splits a list `xs` into all
pairs of lists `(ys, zs)` such that `xs = ys ++ zs`. The function `splitsn` is
similar, except that it splits a list into pairs of nonempty lists. Give
recursive definitions of `splits` and `splitsn`.
-/

def splits : List α → List (List α × List α)
| []       => []
| x :: xs  =>
  ([], x :: xs) :: (splits xs).map (fun (ys, zs) => (x :: ys, zs))

def splitsn : List α → List (List α × List α)
| []       => []
| [_]      => []
| x :: xs  =>
  ([x], xs) :: (splitsn xs).map (fun (ys, zs) => (x :: ys, zs))


/-!
## Exercise 8.8
Using `splitsn`, give a recursive definition of the function `mktrees`
of Section 8.1. Write down a recurrence relation for the function `T(n)` that
counts the number of trees with `n` leaves. It can be shown that
  `T(n) = (1/n) × C(2n − 2, n − 1)`
These values are called the Catalan numbers.
-/

-- TODO

/-!
## Exercise 8.9
Here is another way of defining the function `mktrees` of Section 8.1,
one similar to that used in Huffman coding:
  `mktrees : [a] → [Tree a]`
  `mktrees = map unwrap · until (all single) (concatMap combine) ·`
  `            wrap · map Leaf`
  `combine : Forest a → [Forest a]`
  `combine xs = [ys ++ [Node x y] ++ zs | (ys, x : y : zs) ← splits xs]`
The function `combine` combines two adjacent trees in a forest in all possible
ways. The process is repeated until only singleton forests remain, forests that
consist of just one tree. Finally the trees are extracted to give a list of
trees. This method may generate the same tree more than once, but all possible
trees are nevertheless produced. Write down the associated greedy algorithm for
this version of `mktrees` (no justification is required).
-/

-- TODO

/-!
## Exercise 8.10
In Huffman coding, why does the second, recursive definition of `cost`
follow from the first?
-/

-- TODO

/-!
## Exercise 8.11
Define the function `insert` used in Huffman's algorithm.
-/

-- see Chapter8.lean (`S2.insert`).

/-!
## Exercise 8.12
Give the two ways that the tree
  `[Node (Node (Leaf 3) (Leaf 8)) (Node (Leaf 5) (Leaf 9))]`
can be generated from `[Leaf 3, Leaf 5, Leaf 8, Leaf 9]`.
-/

-- TODO

/-!
## Exercise 8.13
The number of trees generated in the specification of Huffman's
algorithm is given for `n ≥ 2` by
  `C(n, 2) × C(n − 1, 2) × ... × C(2, 2)`
Show that this number equals
  `n! (n − 1)! / 2ⁿ⁻¹`
-/

-- TODO

/-!
## Exercise 8.14
Define `MCC k xs = MinWith cost (apply k fstep [xs])`. Show that
  `apply k gstep xs ← MCC k xs`
provided `MCC k (gstep xs) ← MCC (k + 1) xs`.
-/

-- TODO

/-!
## Exercise 8.15
Define the function `singleSL : SymList a → Bool` for determining
whether a symmetric list is a singleton.
-/

-- see Chapter3.lean (`SymList.singleSL`)

/-!
## Exercise 8.16
Define `addListQ` in terms of `insertQ`.
-/

-- see Chapter8.lean (`PriorityQueue.addListQ`).

/-!
## Exercise 8.17
Define `mergeOn`.
-/

-- see Chapter8.lean (`PriorityQueue.mergeOnSnd`).

/-!
## Exercise 8.18
Show that, for the trees considered in Section 8.3, a tree of size `n`
has rank at most `⌊log (n + 1)⌋`.
-/

-- TODO

/-!
## Exercise 8.19
Define `emptyQ` and `nullQ`.
-/

-- see Chapter8.lean (`PriorityQueue.emptyQ` e `nullQ`).

end Chapter8
