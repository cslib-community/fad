import Fad.Chapter6

namespace Chapter6

/-!
# Exercises
-/

/-!
## Exercise 6.1
Does it make sense to define the `k`th smallest element of an arbitrary
list as an element with exactly `k − 1` elements smaller than it?
-/

-- TODO

/-!
## Exercise 6.2
Define combinators `cross` and `pair` so that
  `pair (foldr f₁ e₁, foldr f₂ e₂) = foldr (cross · pair (f₁, f₂)) (e₁, e₂)`
-/

-- TODO

/-!
## Exercise 6.3
Describe two lists of length `n` for which the second definition of
`minmax` uses `n − 1` and `2n − 2` comparisons, respectively.
-/

-- TODO

/-!
## Exercise 6.4
Show that in the divide-and-conquer algorithm for `minmax` the
comparison count `C(n)` satisfies `C(n) = 3n/2 − 2` when `n` is a positive power
of two.
-/

-- TODO

/-!
## Exercise 6.5
Show that `D(n) = 2 (n − 1)` in the bottom-up algorithm for `minmax`.
-/

-- TODO

/-!
## Exercise 6.6
Suppose a set is given by a balanced binary search tree.
Asymptotically, how long does it take to find the minimum and maximum
elements?
-/

-- TODO

/-!
## Exercise 6.7
Consider a particularly brutal tennis tournament with the twist that the
tournament has to determine both the best and the worst player. Initially all
`n` players are potential champions or potential losers, and the overlap between
the two groups is `n`. The best we can do is to play a match between two players
in the overlap, placing the winner in a potential champion category, and the
loser in a potential loser category. Assuming `n` is even, it follows that after
`n/2` matches the overlap is reduced to zero. How would you complete the
tournament and how many matches are there?
-/

-- TODO

/-!
## Exercise 6.8
Show that `n + ⌈log n⌉ − 2` matches are sufficient to determine the best
and second-best players in a tennis tournament involving `n` players.
-/

-- TODO

/-!
## Exercise 6.9
Are there any other ways apart from setting `pivot [x] = x` to ensure
the definition of the linear-time algorithm for `select` is well-founded?
-/

-- TODO

/-!
## Exercise 6.10
Use the rules of floors and ceilings to show that
  `3 ⌊(⌈n/5⌉ + 1)/2⌋ − 1 ≥ 3n/10`
No case analysis is allowed.
-/

-- TODO

/-!
## Exercise 6.11
Instead of grouping elements into blocks of 5, suppose we group into
blocks of 3. Does this lead to a linear-time algorithm for `select`? How about
grouping into blocks of 7?
-/

-- TODO

/-!
## Exercise 6.12
Counting only comparisons between list elements, how many comparisons
are required to compute `select 4 [1..7]` when `pivot` chooses the first element
of a list, and when `pivot` is as defined in the linear-time version of
`select`? For the second question you can assume that sorting `n` elements for
`3 ≤ n ≤ 5` requires 3 comparisons for `n = 3`, 5 comparisons for `n = 4`, and 7
comparisons for `n = 5`.
-/

-- TODO

/-!
## Exercise 6.13
Is `≪=` a transitive relation, that is, does `xs ≪= ys` and `ys ≪= zs`
imply `xs ≪= zs`?
-/

-- TODO

/-!
## Exercise 6.14
Suppose `xs ++ ys` and `us ++ vs` are both sorted. Prove that `xs ≪= vs`
or `us ≪= ys`.
-/

-- TODO

/-!
## Exercise 6.15
Assuming arrays are indexed from 0, write down a definition of
  `select : Ord a ⇒ Nat → Array Nat a → Array Nat a → a`
-/

-- TODO

end Chapter6
