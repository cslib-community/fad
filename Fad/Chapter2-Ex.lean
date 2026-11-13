import Fad.Chapter2
import Fad.Chapter1

namespace Chapter2
open Chapter1

/-!
# Exercises
-/


/-!
## Exercise 2.1
Is the assertion `f(n) = O(1)` the same as the assertion `f(n) = Θ(1)`?
-/

-- TODO

/-!
## Exercise 2.2
Are the following two assertions true?
  `O(f(n) × g(n)) = f(n) × O(g(n))`
  `O(f(n) + g(n)) = f(n) + O(g(n))`
-/

-- TODO

/-!
## Exercise 2.3
Prove formally that `(n + 1)² = Θ(n²)` by exhibiting the necessary
constants.
-/

-- TODO

/-!
## Exercise 2.4
What are the exact values of the sums `∑_{k=1}^{n} k` and
`∑_{k=1}^{n} k²`?
-/

-- TODO

/-!
## Exercise 2.5
Some of the following are correct and some are wrong. Which are which?
  `2n² + 3n = Θ(n²)`
  `2n² + 3n = O(n³)`
  `n log n = O(n √n)`
  `n + √n = O(√n log n)`
  `∑_{k=1}^{n} 1/k = Θ(log n)`
  `2^(log n) = O(n)`
  `log (n!) = Θ(n log n)`
-/

-- TODO

/-!
## Exercise 2.6
Sums of the form `∑_{k=0}^{n} k xᵏ` for various `x` come up surprisingly
often in the analysis of running times. One way of finding the solution is to
start with the simpler geometric series
  `∑_{k=0}^{n} xᵏ = (1 − xⁿ⁺¹) / (1 − x)`
which is valid provided `x ≠ 1`, and to differentiate both sides with respect to
`x`. Using the fact that the derivative of a sum is the sum of its derivatives,
carry out this differentiation and hence estimate the sums
`∑_{k=0}^{n} k 2ᵏ` and `∑_{k=0}^{n} k / 2ᵏ`.
-/

-- TODO

/-!
## Exercise 2.7
Using `Θ` notation, estimate the sum `∑_{k=1}^{n} k log k`.
-/

-- TODO

/-!
## Exercise 2.8
Solve the recurrence relation
  `T(0, n) = Θ(n²)`
  `T(m, n) = T(m − 1, n) + Θ(m)`
-/

-- TODO

/-!
## Exercise 2.9
Use the fusion law of `foldr` to simplify `head · concat₁`. Can the
fusion law of `foldl` be used to simplify `head · concat₂`?
-/

def op1 {a : Type} : (List a) → a → a
| [], y => y
| (x::_), _ => x

example {xss : List (List α)} {e : α} (h : (concat₁ xss) ≠ [])
  : List.head (concat₁ xss) h = foldr op1 e xss:= by
    induction xss with
    | nil => contradiction
    | cons xs xss ih =>
      cases xs with
      | nil => simp [concat₁, List.head, foldr, op1]; exact ih h
      | cons x xs => simp [concat₁, List.head, foldr, op1]

/-!
## Exercise 2.10
Analyse the running time of `perms₃`, where
  `perms₃ [] = [[]]`
  `perms₃ xs = concatMap subperms xs`
  `  where subperms x = map (x:) (perms₃ (remove x xs))`
-/

-- TODO

/-!
## Exercise 2.11
Do `perms₁`, `perms₂`, and `perms₃` all return the same first list? If
so, what is it?
-/

-- TODO

/-!
## Exercise 2.12
Can the trick of using an accumulating function work with `inits`?
-/

def inits (as : List a) : List (List a) :=
  let rec help (f : List a → List a) : List a → List (List a)
  | []      => (f []) :: []
  | x :: xs =>
    (f []) :: help (f ∘ List.cons x) xs
  help id as


/-!
## Exercise 2.13
Suppose you are given a list of `n` digits and you want to find the
position, reading from left to right, of the first digit `d` for which `d ≥ 5`.
If no such digit occurs, then the result is some negative position, say `−1`.
In the best case the algorithm examines one digit and in the worst case all `n`
digits. Assuming that every sequence of `n` digits is equally likely, what is
the average number of digits that have to be examined?
-/

-- TODO

/-!
## Exercise 2.14
Using the function `iterate`, give a one-line definition of the function
`tails₁` that returns the nonempty suffixes of a list.
-/

def tails1 (xs : List α) : List (List α) :=
  List.takeWhile (¬ ·.isEmpty) (iterate xs.length List.tail xs)


/-!
## Exercise 2.15
Consider the problem of maintaining a dynamic array. Apart from
inspecting and updating the elements, suppose that new elements can be added to
the array but only at the front. At some point the array, which is of a fixed
given size, can become full. To solve this problem, a new array of double the
size of the old one can be allocated and all the existing elements copied into
the upper half of the new array, leaving space for further additions in the
bottom half. Then we can carry on until the new array becomes full, in which
case the process is repeated. Show that, in a sequence of add operations, each
addition has an amortised cost of `O(1)`.
-/

-- TODO

end Chapter2
