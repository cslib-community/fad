import Fad.Chapter4
import Fad.Chapter3
import Mathlib
namespace Chapter4

/-!
# Exercises
-/


/-!
## Exercise 4.1

The *rule of floors* states that for integers $n$ and real numbers $r$ we have
$n ≤ ⌊r⌋ ↔ n ≤ r$ (Mathlib `Int.le_floor`). This useful rule will appear in a
number of problems. Using just the rule of floors (no case analysis) prove that
for integers $a$ and $b$ we have $a < (a+b)/2 < b$ if and only if $a + 1 < b$.

The dual *rule of ceilings* states that for integers $n$ and real numbers $r$ we
have $⌈r⌉ ≤ n ↔ r ≤ n$ (Mathlib `Int.ceil_le`). Using this rule prove that if
$h$ is an integer such that $n < 2^h$, then $⌈log (n + 1)⌉ ≤ h$.
-/

theorem floor_ineq (a b : ℤ)
  : (a < (a + b) / 2 ∧ (a + b) / 2 < b) ↔ a + 1 < b := by
  -- a divisão inteira (a+b)/2 é ⌊(a+b)/2⌋ sobre ℝ
  have hdiv : (a + b) / 2 = ⌊(a + b : ℝ) / 2⌋ := by
    rw [show ((a + b : ℝ) / 2) = ((((a + b : ℤ) : ℚ) / ((2 : ℕ) : ℚ) : ℚ) : ℝ) by
      push_cast; ring]
    rw [Rat.floor_cast, Rat.floor_intCast_div_natCast]
    norm_num
  have floor_lt : ∀ (x : ℤ) (r : ℝ), ⌊r⌋ < x ↔ r < x :=
    fun x r => by rw [← not_le, ← not_le, Int.le_floor]
  -- reescreve (a < ·) como (a+1 ≤ ·) e retira os dois pisos pela regra dos pisos
  rw [hdiv, Int.lt_iff_add_one_le, Int.le_floor, floor_lt]
  push_cast
  constructor
  · rintro ⟨e1, e2⟩
    exact_mod_cast show (a : ℝ) + 1 < b by linarith
  · intro hab
    have : (a : ℝ) + 2 ≤ b := by exact_mod_cast (by omega : a + 2 ≤ b)
    exact ⟨by linarith, by linarith⟩


theorem ceil_ineq (n h : ℕ) (hlt : n < 2 ^ h)
  : ⌈Real.logb 2 (n + 1)⌉ ≤ h := by
  have hle : (n : ℝ) + 1 ≤ 2 ^ h := by exact_mod_cast hlt
  have hpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine Int.ceil_le.mpr ?_
  rw [Real.logb, div_le_iff₀ hpos]
  rw [show ((h : ℤ) : ℝ) = (h : ℝ) by norm_cast, ← Real.log_pow]
  exact Real.log_le_log (by positivity) hle


/-!
## Exercise 4.2
Look again at the expression
  `head ([x | x ← [a+1..m], t ≤ f x] ++ [x | x ← [m+1..b], t ≤ f x])`
where `a < m < b` and `f a < t ≤ f b`. If nothing else is assumed about `f`,
then we cannot assert that the first list is empty if `f m < t`. Nevertheless,
the definition of `smallest (a, b)` returns some value. What is it?
-/

/-
We have smallest (a,b) = x such that f x < t ≤ f (x + 1)
But for t = 1024 and f x = x^2 below f x = t and f (x + 1) > t

#eval D1.smallest (fun x => dbg_trace "fun {x}"; x * x) 1024 (0, 1024)
#eval (fun x => dbg_trace "fun {x}"; x * x) 32
#eval (fun x => dbg_trace "fun {x}"; x * x) 33
-/

/-!
## Exercise 4.3
Recall that the exact number `T(n)` of evaluations of `f` required in the
worst case of evaluating `smallest (a, b) f t`, where `n = b − a + 1` is the
number of integers in the interval, satisfies `T(2) = 0` and
  `T(n) = T(⌈(n + 1)/2⌉) + 1`
for `n > 2`. Use the rule of ceilings to show that `T(n) = ⌈log (n − 1)⌉`.
-/

/-

Vamos provar por indução que

T(x) = ⌈log(n-1)⌉.

Para o caso base (n=2)

T(2) = ⌈log(2-1)⌉ = ⌈log(1)⌉ = ⌈0⌉ = 0.

Supondo valido para k < n, vamos provar para n. Como ⌈(n+1)/2⌉ < n,
vale a hipotese de indução, então temos que provar que:

T(n) = ⌈log(⌈(n+1)/2⌉ -1)⌉ + 1 = ⌈log(n-1)⌉.

Podemos mostrar por desigualdade indireta, mostrando que o lado
esquerdo é menor que k se e somente o lado direito é menor que k, para
qualquer k natural.  Pelo lado direito temos que ⌈log(n-1)⌉ <= k <=>
n-1 <= 2^k.  Pelo lado esquerdo:

    ⌈log(⌈(n+1)/2⌉ -1)⌉ + 1 <= k <=> ⌈log(⌈(n+1)/2⌉ -1)⌉ <= k-1,
                                 <=> log(⌈(n+1)/2⌉ -1) <= k-1,
                                 <=> ⌈(n+1)/2⌉ -1 <= 2^(k-1),
                                 <=> ⌈(n+1)/2⌉ <= 2^(k-1) + 1,
                                 <=> (n+1)/2 <= 2^(k-1) + 1,
                                 <=> n+1 <= 2^k + 2,
                                 <=> n-1 <= 2^k.

O que completa a prova, uma vez que ambos os lados chegam na mesma
proposição.

-/


/-!
## Exercise 4.4
Following on from the previous question, given that `f a < t ≤ f b`,
show that any algorithm for computing `smallest (a, b) f t` requires
`⌈log (n − 1)⌉` comparison tests of the form `t ≤ f x`.
-/

-- see the book

/-!
## Exercise 4.5
What are the positions of 472 in the grid of Figure 4.1?
-/

-- Indexing the coordinates from zero, the positions are
-- (0, 9), (5, 6), (7, 5), (9, 0)

/-!
## Exercise 4.6
With `f (x, y) = x³ + y³`, what is the result of saddleback search for
`t = 1729`? Does the final algorithm return the same result?
-/

-- #eval D2.search₁ (λ (x, y) => x ^ 3 + y ^ 3) 1729


/-!
## Exercise 4.7
To obtain a linear-time definition of `flatten` we can use an
accumulating parameter. There is more than one way of doing so, but a simple
method is to introduce `flatcat` defined by
  `flatcat : Tree a → [a] → [a]`
  `flatcat t xs = flatten t ++ xs`
We have `flatten t = flatcat t []`, so it remains to produce a recursive
definition of `flatcat` that does not use `flatten` or any `++` operations.
Give details of the synthesis.
-/

namespace BST1

def flatcat : (t : Tree a) → (xs: List a) → List a
| .null, xs => xs
| .node l x r, xs => flatcat l (x :: flatcat r xs)

def Tree.flatten₁ (t : Tree a) : List a :=
 flatcat t []

theorem flatten_eq_helper_accum (t : Tree a) (xs: List a)
  : t.flatten ++ xs = flatcat t xs := by
  induction t generalizing xs with
  | null => rfl
  | node l x r ihl ihr =>
    rw [flatcat, ←ihr]
    rw [←ihl (x :: (r.flatten ++ xs))]
    rw [List.append_cons]
    rw [← List.append_assoc]
    rw [Tree.flatten]

example (t: Tree a) : t.flatten = t.flatten₁ := by
  induction t with
  | null => exact rfl
  | node l x r ihl ihr =>
    rw [Tree.flatten₁]
    simp [← flatten_eq_helper_accum]

end BST1

/-!
## Exercise 4.8
Prove by structural induction that
  `height t ≤ size t < 2^(height t)`
for all binary trees `t`.
-/

namespace BST1

theorem tree_size_bounds {α : Type} (t : Tree α)
  : t.height ≤ t.size ∧ t.size < 2 ^ t.height := by
  induction t with
  | null => simp [Tree.height, Tree.size]
  | node t₁ x t₂ ihl ihr =>
    constructor
    · simp [Tree.height, Tree.size]
      omega
    · simp [Tree.height, Tree.size, pow_add, pow_one]
      have hl : t₁.size < 2 ^ max t₁.height t₂.height :=
        lt_of_lt_of_le ihl.2
          (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
      have hr : t₂.size < 2 ^ max t₁.height t₂.height :=
        lt_of_lt_of_le ihr.2
          (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
      omega

end BST1


/-!
## Exercise 4.9
The definition
  `partition p xs = (filter p xs, filter (not · p) xs)`
involves two traversals of its second argument. Give a definition of
`partition` that makes only one traversal of the input.
-/

def partition {α : Type} (p : α → Bool) : List α → List α × List α :=
  let op (x : α) (r : List α × List α) :=
   if p x then (x :: r.1, r.2) else (r.1, x :: r.2)
  List.foldr op ([], [])


/-!
## Exercise 4.10
Another way to build a binary tree for a list containing duplicates is
to build a tree of type `Tree [a]` in which node labels are lists of equal
values. Show how to build such a tree.
-/

namespace BST2

def partition3 [LT a] [DecidableRel (α := a) (· < ·)]
 [DecidableRel (α := a) (· = ·)]
 (y : a) (xs : List a) : (List a × List a × List a) :=
 let op x acc :=
   let (us, vs, ws) := acc
     if      x < y then (x :: us, vs, ws)
     else if x = y then (us, x :: vs, ws)
     else (us, vs, x :: ws)
 xs.foldr op ([], [], [])

partial def mkTree₃ : (xs : List Nat) → Tree (List Nat)
| [] => .null
| (x :: xs) =>
   match partition3 x (x :: xs) with
   | (us, vs, ws) => node (mkTree₃ us) vs (mkTree₃ ws)


end BST2

/-!
## Exercise 4.11
Consider the recurrences
  `B(n + 1) = 2 B(n/2) + Θ(n)`
  `W(n + 1) = W(n) + Θ(n)`
for the best and worst cases for building a binary search tree by partitioning
the input. Prove that `B(n) = Θ(n log n)` and `W(n) = Θ(n²)`.
-/

-- TODO

/-!
## Exercise 4.12
Show that `log (n!) = Ω(n log n)` without using Stirling's
approximation.
-/

-- TODO

/-!
## Exercise 4.13
For the (second) definition of `combine` we have
  `flatten (combine t₁ t₂) = flatten t₁ ++ flatten t₂`
Anticipating the following chapter, give a definition of `merge` for which
  `flatten (union t₁ t₂) = merge (flatten t₁) (flatten t₂)`
-/

namespace DSet

def merge [LT a] [DecidableEq a] [DecidableRel (α := a) (· < ·)]
  : List a → List a → List a
  | [], ys => ys
  | xs, [] => xs
  | (x :: xs), (y :: ys) =>
    if x < y then x :: merge xs (y :: ys)
    else if x = y then x :: merge xs ys
    else y :: merge (x :: xs) ys

end DSet


/-!
## Exercise 4.14
One method of defining `union` is to flatten one of the trees and then
insert the elements one by one into the other tree:
  `union : Ord a ⇒ Set a → Set a → Set a`
  `union t₁ t₂ = foldr insert t₁ (flatten t₂)`
Supposing the first tree has size `m` and the second tree has size `n`, how
long does `union` take?

Another method is to flatten both trees, merge the results to obtain a sorted
list, and then to build a tree from the sorted list:
  `union t₁ t₂ = build (merge (flatten t₁) (flatten t₂))`
We can build a tree from a sorted list in linear time if we bring in arrays.
Here is the first line of the definition:
  `build xs = from (0, n) (listArray (0, n − 1) xs) where n = length xs`
(recall from Chapter 3 that the expression `listArray (0, length xs − 1) xs`
converts a list of length `n` into an array whose indices run from `0` to
`n − 1`). Construct a definition of `from`. How long does this method of
defining `union` take?
-/

namespace DSet
open BST2 (Tree insert node)

def union₁ [LT a] [DecidableRel (α := a) (· < ·)]
  (t₁ t₂ : Set a) : Set a :=
  List.foldr insert t₁ (Tree.flatten t₂)

partial def frm [Inhabited a] (l r : Nat) (xa : Array a) : Set a :=
  if l = r then .null
  else
   let m := (l + r) / 2
   node (frm l m xa) xa[m]! (frm (m + 1) r xa)

def build [Inhabited a] [LT a] [DecidableRel (α := a) (· < ·)]
  (xs : List a) : Set a :=
  frm 0 xs.length xs.toArray

def union₂ [Inhabited a] [LT a] [DecidableEq a] [DecidableRel (α := a) (· < ·)]
  (t₁ t₂ : Set a) : Set a :=
  build $ merge (Tree.flatten t₁) (Tree.flatten t₂)

-- #eval union₂ (BST2.mkTree [1,2,3]) (BST2.mkTree [4,2,6]) |>.flatten

end DSet


/-!
## Exercise 4.15
Why is the use of `balance` justified in the definitions of `deleteMin`
and `combine`?
-/

-- TODO

/-!
## Exercise 4.16
Give the definition of `balanceL`.
-/

-- see Chapter4.lean


/-!
## Exercise 4.17
Suppose `pair f (x, y) = (f x, f y)`. Using `pair` give a one-line,
linear-time definition of `split x`.
-/

namespace DSet
open BST2

def pair {α β : Type} (f : α -> β) (p : α × α) : (β × β) := (f p.1, f p.2)

def split₁ {α : Type} [LT α] [LE α]
  [DecidableRel (α := α) (· < ·)]
  [DecidableRel (α := α) (· ≤ ·)]
  (x : α) : Set α → Set α × Set α :=
  pair mkTree ∘ List.partition (· ≤ x) ∘ Tree.flatten


end DSet

end Chapter4
