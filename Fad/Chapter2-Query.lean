import Cslib.Algorithms.Lean.Query.Bounds
import Mathlib.Tactic

/-!
# Chapter 2 complexity examples, in the *query model*

This module reimplements the running-time examples of `Fad.Chapter2`
(`append`, `concat₁`, `concat₂`) using the **query model** of CSLib
(`Cslib.Algorithms.Lean.Query`, PR leanprover/cslib#401) instead of the
`TimeM` monad, so the two styles can be compared directly.

The correspondence is:

| `TimeM` version (`Chapter2`)            | query-model version (here)              |
|-----------------------------------------|-----------------------------------------|
| cost is *carried* by the computation    | cost is *assigned* by an oracle+weight  |
| `✓ e` / `✓[c] e` ticks inline           | a query node is emitted; its cost comes |
|                                         | from a `weight`, not from the program   |
| `.time` reads the accumulated cost      | `.cost oracle weight` folds the tree    |
| one fixed cost model                    | the same program, many cost models      |

A program is a value of `FreeM Q α`: a *syntax tree* of queries `Q`.  Three
interpreters run it:

* `p.eval   oracle`         — the result, answering each query with `oracle`;
* `p.cost   oracle weight`  — the total cost, charging `weight` per query;
* `p.queriesOn oracle`      — the number of queries (= `cost` with unit weight).

Because the oracle/weight are supplied *after* the tree is built, the algorithm
cannot "peek" at costs — the anti-cheating guarantee for both bounds.

The complexity theorems (`concat₁_runtime`, `concat₂_runtime`) are the
query-model analogues of `Chapter2.concat₁''_time` and `Chapter2.concat₂'_time`;
compare the proofs.
-/

set_option autoImplicit false

open Cslib (FreeM)

namespace Chapter2Query

/-! ## `append`

The `TimeM` version (`Chapter2.append'`) prepends the head of `xs` one element
at a time, charging one tick per element:

```
def append' : List a → List a → TimeM Nat (List a)
  | [], ys       => pure ys
  | x :: xs, ys  => do ✓ return x :: (← append' xs ys)
```

Here each prepend is a *query* `AppendOp.step`; how much it costs is decided
later by a `weight`, not written into the algorithm. -/

inductive AppendOp (a : Type) : Type → Type where
  | step : a → List a → AppendOp a (List a)   -- prepend the head onto the tail

/-- The semantics of a `step`: it prepends. Fixed, independent of cost. -/
def appendOracle {a : Type} : {ι : Type} → AppendOp a ι → ι
  | _, .step x xs => x :: xs

/-- The natural cost model: each `step` costs one unit — matching the single
`✓` per element in `Chapter2.append'`. -/
def stepWeight {a : Type} : {ι : Type} → AppendOp a ι → Nat
  | _, .step _ _ => 1

/-- A *different* cost model for the *same* program: two units per prepend
(e.g. two memory writes). Impossible to express with `TimeM` without editing
the algorithm — the whole point of the query model. -/
def stepWeight2 {a : Type} : {ι : Type} → AppendOp a ι → Nat
  | _, .step _ _ => 2

@[simp] theorem appendOracle_step {a : Type} (x : a) (xs : List a) :
    appendOracle (AppendOp.step x xs) = x :: xs := rfl
@[simp] theorem stepWeight_step {a : Type} (x : a) (xs : List a) :
    stepWeight (AppendOp.step x xs) = 1 := rfl
@[simp] theorem stepWeight2_step {a : Type} (x : a) (xs : List a) :
    stepWeight2 (AppendOp.step x xs) = 2 := rfl

def append {a : Type} : List a → List a → FreeM (AppendOp a) (List a)
  | [],      ys => pure ys
  | x :: xs, ys => do
      let r ← append xs ys
      FreeM.lift (AppendOp.step x r)

/-- The program still computes the ordinary append (it does not cheat). -/
@[simp] theorem append_eval {a : Type} (xs ys : List a) :
    (append xs ys).eval appendOracle = xs ++ ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [append, ih]

/-- Number of queries is the length of the first list — `Θ(|xs|)`. -/
theorem append_queriesOn {a : Type} (xs ys : List a) :
    (append xs ys).queriesOn appendOracle = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [append, ih]

/-- The same program, measured under `stepWeight2`, costs twice as much — no
change to `append` itself, only the cost model. -/
theorem append_cost2 {a : Type} (xs ys : List a) :
    (append xs ys).cost appendOracle stepWeight2 = 2 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [append, ih]; omega


/-! ## `concat`

`Chapter2.concat₁''` folds append from the right, charging `xs.length` for each
append (`✓[xs.length]`). We model one append of a length-`k` list as a single
query whose *weight is `k`*. Here `queriesOn` (which counts nodes) is *not* the
right measure — a single append is one node but costs `k` — so we use `cost`
with the length-weight. -/

inductive ConcatOp (a : Type) : Type → Type where
  | app : List a → List a → ConcatOp a (List a)   -- xs ++ ys

def concatOracle {a : Type} : {ι : Type} → ConcatOp a ι → ι
  | _, .app xs ys => xs ++ ys

/-- Appending `xs ++ ys` costs `xs.length` (you walk the left list). -/
def concatWeight {a : Type} : {ι : Type} → ConcatOp a ι → Nat
  | _, .app xs _ => xs.length

@[simp] theorem concatOracle_app {a : Type} (xs ys : List a) :
    concatOracle (ConcatOp.app xs ys) = xs ++ ys := rfl
@[simp] theorem concatWeight_app {a : Type} (xs ys : List a) :
    concatWeight (ConcatOp.app xs ys) = xs.length := rfl

/-- Right fold — mirrors `Chapter2.concat₁''`. -/
def concat₁ {a : Type} : List (List a) → FreeM (ConcatOp a) (List a)
  | []        => pure []
  | xs :: xss => do
      let ys ← concat₁ xss
      FreeM.lift (ConcatOp.app xs ys)

/-- Left fold, cost-charging on the accumulator — mirrors `Chapter2.concat₂''`.
Each step appends the accumulator (which keeps growing) onto the next block, so
the accumulator length is what gets charged. -/
def concat₂ {a : Type} : List (List a) → List a → FreeM (ConcatOp a) (List a)
  | [],        acc => pure acc
  | xs :: xss, acc => do
      let acc' ← FreeM.lift (ConcatOp.app acc xs)
      concat₂ xss acc'

/-- The result of `concat₁` really is the concatenation (it does not cheat). -/
@[simp] theorem concat₁_eval {a : Type} (xss : List (List a)) :
    (concat₁ xss).eval concatOracle = xss.flatten := by
  induction xss with
  | nil => rfl
  | cons xs xss' ih => simp [concat₁, ih]

/-- If `xss` is a list of `m` lists each of length `n`, then `concat₁` is
`Θ(m * n)`. Query-model analogue of `Chapter2.concat₁''_time`. -/
theorem concat₁_runtime {a : Type} (xss : List (List a))
    (n : Nat) (h : ∀ xs ∈ xss, xs.length = n) :
    (concat₁ xss).cost concatOracle concatWeight = xss.length * n := by
  induction xss with
  | nil => simp [concat₁]
  | cons xs xss' ih =>
      have h₁ : xs.length = n := h xs List.mem_cons_self
      have h₂ : ∀ ys ∈ xss', ys.length = n :=
        fun ys hys => h ys (List.mem_cons_of_mem xs hys)
      have hstep : (concat₁ (xs :: xss')).cost concatOracle concatWeight
          = (concat₁ xss').cost concatOracle concatWeight + xs.length := by
        simp [concat₁]
      rw [hstep, ih h₂, h₁, List.length_cons]
      ring

/-- Cost of the left-associated fold: `concat₂` over `m` blocks of length `n`
starting from an accumulator of length `a₀` costs `a₀ * m + n * m * (m-1) / 2`.
We state it in the doubled, subtraction-free form used in
`Chapter2.concat₂'_time`: it is `Θ(m² * n)`. -/
theorem concat₂_runtime {a : Type} (xss : List (List a))
    (n : Nat) (h : ∀ xs ∈ xss, xs.length = n)
    (acc : List a) :
    (2 * (concat₂ xss acc).cost concatOracle concatWeight : Int)
      = 2 * acc.length * xss.length + n * xss.length * (xss.length - 1) := by
  induction xss generalizing acc with
  | nil => simp [concat₂]
  | cons xs xss' ih =>
      have h₁ : xs.length = n := h xs List.mem_cons_self
      have h₂ : ∀ ys ∈ xss', ys.length = n :=
        fun ys hys => h ys (List.mem_cons_of_mem xs hys)
      -- one fold step charges the current accumulator length, then recurses on
      -- the (grown) accumulator
      have hstep : (concat₂ (xs :: xss') acc).cost concatOracle concatWeight
          = acc.length + (concat₂ xss' (acc ++ xs)).cost concatOracle concatWeight := by
        simp [concat₂]
      have hIH := ih h₂ (acc ++ xs)
      rw [List.length_append, h₁] at hIH
      rw [hstep, List.length_cons]
      push_cast at hIH ⊢
      linear_combination hIH


/-! ## Practical comparison

The pay-off of the query model over `TimeM`: the *same* program is measured
under different cost models, with no change to the algorithm. Under `TimeM`
each of these would need a separately-written function.

`.eval` returns the result; `.cost`/`.queriesOn` return the cost. -/

-- `append` computes the same list, but costs one per element under unit weight,
-- two under `stepWeight2`:
#eval (append [1, 2, 3] [4, 5]).eval appendOracle                    -- [1,2,3,4,5]
#eval (append [1, 2, 3] [4, 5]).queriesOn appendOracle              -- 3
#eval (append [1, 2, 3] [4, 5]).cost appendOracle stepWeight2       -- 6

-- On 4 blocks of length 2, the right fold `concat₁` is Θ(m·n) = 4·2 = 8,
-- while the left fold `concat₂` is Θ(m²·n) = 0+2+4+6 = 12 — same result,
-- different cost, exposed purely by the cost model:
#eval (concat₁ [[1, 2], [3, 4], [5, 6], [7, 8]]).cost concatOracle concatWeight      -- 8
#eval (concat₂ [[1, 2], [3, 4], [5, 6], [7, 8]] []).cost concatOracle concatWeight   -- 12

-- the theorem, specialised: m = 4 blocks of length n = 2
example :
    (concat₁ [[1, 2], [3, 4], [5, 6], [7, 8]]).cost concatOracle concatWeight = 4 * 2 :=
  concat₁_runtime _ 2 (by decide)

end Chapter2Query
