import Fad.Chapter1
import Fad.Chapter12

namespace Chapter12
open Chapter1 (concatMap)

/-!
# Exercises
-/

/-!
## Exercise 12.1
How many partitions of a list of length `n > 0` are there?
-/

/- A definição recursiva de `parts` provavelmente teria uma prova mais simples
   mas não consigo usar na prova por ser `partial`. -/

example : ∀ xs : List Nat, (parts₁ xs).length = 2^(xs.length - 1) := by
 intro xs
 induction xs with
 | nil => simp [parts₁]
 | cons x xs ih =>
   sorry


/-!
## Exercise 12.2
Why is the clause `parts [] = [[]]` necessary in the first definition of
`parts`?
-/

/- Como parts é partial, não consigo expandir em uma prova. E `parts₁`
   obviamente não é a primeira definição de `parts` tratada no exercício. -/

example : parts₁ [1,2] = [[[1], [2]], [[1, 2]]] := by
  unfold parts₁
  rw [List.foldr]; rw [Function.comp]
  rw [List.foldr]; rw [Function.comp]
  simp [concatMap, Chapter1.concat₁]
  sorry
  /- simp [List.foldr]
  simp [cons]
  simp [cons]
  simp [glue] -/


/-!
## Exercise 12.3
Give another definition of `parts` in terms of `foldr`, one that at each step
does all the `cons` operations before the `glue` operations.
-/

def parts₃ {α : Type} : List α → List (Partition α) :=
  let step (x : α) : List (Partition α) → List (Partition α)
   | [[]] => [[[x]]]
   | ps => ps.map (cons x) ++ ps.map (glue x)
  List.foldr step [[]]

-- #eval parts₃ [1,2,3]


/-!
## Exercise 12.4
Give the details of the proof that
  `filter (all ok) · parts = foldr (concatMap · okextendl) [[]]`
provided `ok` is suffix-closed. (Hint: it is probably best to express the fusion
condition in terms of list comprehensions.)
-/

section
open List (filter all head!)

def ok (xs : List Nat) : Bool :=  xs.all (· > 0)

def okextendl (x : Nat) : Partition Nat → List (Partition Nat) :=
 filter (ok ∘ head!) ∘ extendl x

variable (h : ∀ x ps, filter (flip all ok) (concatMap (extendl x) ps) =
              concatMap (okextendl x) (filter (flip all ok) ps))

example
  : List.filter (flip List.all ok) ∘ parts₁ = List.foldr (concatMap ∘ okextendl) [[]] := by
  funext xs
  unfold parts₁
  simp [Function.comp]
  induction xs with
  | nil =>
    simp [List.foldr, flip]
  | cons a as ih =>
    have h1 := h a
    sorry

end

/-!
## Exercise 12.5
Which of the following predicates on nonempty sequences of positive numbers are
prefix-closed and which are suffix-closed?
  `leftmin xs = all (head xs ≤) xs`
  `rightmax xs = all (≤ last xs) xs`
  `ordered xs = and (zipWith (≤) xs (tail xs))`
  `nomatch xs = and (zipWith (≠) xs [0 ..])`
Do each of these predicates hold for singleton lists?
-/

section
open List (range head! tail zipWith and)

def leftmin  (xs : List Nat) := xs.all (head! xs ≤ ·)
def rightmax (xs : List Nat) := xs.all (· ≤ last xs)
def ordered  (xs : List Nat) := and $ zipWith (· ≤ ·) xs (tail xs)
def nmatch   (xs : List Nat) := and $ zipWith (· ≠ ·) xs (range xs.length)

def suffixClosed (p : List Nat → Bool) : Prop :=
    ∀ xs ys, p (xs ++ ys) → p ys

def prefixClosed (p : List Nat → Bool) : Prop :=
    ∀ xs ys, p (xs ++ ys) → p xs

example : suffixClosed leftmin := by
   unfold suffixClosed
   intro xs ys
   unfold leftmin; simp
   intro h
   sorry

end


/-!
## Exercise 12.6
Suppose that `n ≤ 0 ≤ m`. Show that
  `(∃ r : 0 ≤ r + n ≤ C ∧ 0 ≤ r + m ≤ C) ⇔ m ≤ C + n`
-/

-- TODO

/-!
## Exercise 12.7
Show that the predicate `safe` in the bank accounts problem is both
prefix-closed and suffix-closed.
-/

-- TODO

/-!
## Exercise 12.8
Suppose `C = 10`. What is the value of `msp [2, 4, 50, 3]` when `msp` is the
greedy algorithm for the bank accounts problem and when `msp` is defined by the
original specification?
-/

-- TODO

/-!
## Exercise 12.9
The function `add` in the bank accounts problem does not take constant time
because the safety test can take linear time. But we can represent a partition
`p` by a triple
  `(p, minimum (sums (head p)), maximum (sums (head p)))`
where `sums = scanl (+) 0`. Write down a new definition of `msp` that does take
linear time.
-/

-- TODO

/-!
## Exercise 12.10
The function `msp` returns a partition, not the transfers that have to be made
to keep the current account in balance. Show how to define
  `transfers : Partition Int → List Int`
by computing a pair `(n, r)` of nonnegative numbers for each segment, where `n`
is the minimum that has to be in the current account to ensure the segment is
safe and `r` is the residue after the transactions in the segment.
-/

-- TODO

/-!
## Exercise 12.11
Consider the thinning algorithm for the bank accounts problem. Suppose that at
some point in the computation there are two partitions of the form
`[y] : ys : p` and `(y : ys) : p`. This could happen as early as the second
step, producing the partitions `[[y], [z]]` and `[[y, z]]`. Show that adding in
a new element `x` and thinning the result will produce either a single
partition, or two partitions of the above form.
-/

-- TODO

/-!
## Exercise 12.12
How can Zakia address the suspicious feature of the given solution to the bank
accounts problem, namely that transfers can occur before they are absolutely
necessary?
-/

-- TODO

/-!
## Exercise 12.13
The function `runs` used in Mergesort is specified by
  `runs : Ord a ⇒ [a] → Partition a`
  `runs ← MinWith length · filter (all ordered) · parts`
Without looking back to the section on Mergesort, write down a greedy algorithm
for computing `runs`. Why does the greedy algorithm work?
-/

-- TODO

/-!
## Exercise 12.14
Show that the greedy condition fails when the cost of a paragraph is simply the
number of lines.
-/

-- TODO

/-!
## Exercise 12.15
The greedy algorithm for the paragraph problem can be made more efficient in
two steps. This exercise deals with the first step and the following exercise
with the second step. Consider the function `help` specified by
  `p ++ help l ws = foldl add (p ++ [l]) ws`
Prove that
  `greedy (w : ws) = help [w] ws`
    `where help l []       = [l]`
          `help l (w : ws) = if width l' ≤ maxWidth`
                            `then help l' ws else l : help [w] ws`
                            `where l' = l ++ [w]`
-/

-- TODO

/-!
## Exercise 12.16
For the second step, memoise `width` and eliminate the concatenation with the
help of an accumulating function parameter.
-/

-- TODO

/-!
## Exercise 12.17
In the thinning version of the paragraph problem, can we replace `filter` by
`takeWhile`?
-/

-- TODO

/-!
## Exercise 12.18
Show that the cost functions described in the text for the paragraph problem
are all admissible.
-/

-- TODO

/-!
## Exercise 12.19
With some admissible cost functions, the thinning algorithm may select a
paragraph with minimum cost but whose length is not as short as possible. How
can this deficiency be overcome?
-/

-- TODO

/-!
## Exercise 12.20
The refinement
  `snoc w · MinWith cost ← MinWith cost · map (snoc w)`
follows from the condition
  `cost p₁ ≤ cost p₂ ⇒ cost (snoc w p₁) ≤ cost (snoc w p₂)`
Does this condition hold for `cost₃`?
-/

-- TODO

/-!
## Exercise 12.21
Suppose we had gone for a right-to-left thinning algorithm for the paragraph
problem, using a definition of `parts` based on `foldr`. This time a cost
function is admissible if
  `cost (glue w p₁) ≤ cost (glue w p₂) ∧ cost (cons w p₁) ≤ cost (cons w p₂)`
provided that
  `cost p₁ ≤ cost p₂ ∧ width (head p₁) = width (head p₂)`
As can be checked, all five cost functions introduced in the text are admissible
in this sense. Write down the associated thinning algorithm. Give an example to
show that the two different thinning algorithms produce different results for
`cost₃`.
-/

-- TODO

/-!
## Exercise 12.22
The final exercise is to make the thinning algorithm for the paragraph problem
more efficient. Setting `rmr = reverse · map reverse`, we can represent a
paragraph `p` by a triple
  `(rmr p, cost p, width (last p))`
The last two components memoise `cost` and `width`, while the first component
means that `snoc` and `bind` can be implemented in terms of `cons` and `glue`.
More precisely, we have
  `snoc w · rmr = rmr · cons w`
  `bind w · rmr = rmr · glue w`
Write down the resulting algorithm, assuming the cost function is `cost₃`.
-/

-- TODO

end Chapter12
