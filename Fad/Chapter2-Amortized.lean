import Cslib.Algorithms.Lean.Query.Bounds
import Mathlib.Tactic

/-!
# Amortized complexity in the query model: a binary counter

Amortized analysis measures the cost of a *sequence* of operations rather than a
single one. Its textbook example is the **binary counter**: incrementing it once
can be expensive (a carry may ripple through every bit), yet `n` increments from
zero cost only `O(n)` in total — i.e. `O(1)` *amortized* per increment.

The query model is a natural home for this, and this is exactly where it pulls
ahead of the inline-tick `TimeM` style:

* `queriesOn` already counts cost over the **whole** program tree, so the total
  cost of a sequence is just `queriesOn` of the sequence — no manual summation.
* The **potential method** drops out cleanly. The classic potential of a binary
  counter is `Φ = (number of 1-bits)`. Here `Φ (bs) = bs.count true`, and the
  key single-step invariant

  ```
  (inc bs).queriesOn + Φ((inc bs).eval) = Φ(bs) + 2
  ```

  says each increment has **amortized cost exactly 2**: actual flips plus the
  change in potential is always `2`. Telescoping it over `n` steps gives the
  `≤ 2n` total bound, with `Φ` never negative doing the "banking".

Compare `Chapter2` (worst-case, single-shot) with this file (amortized, whole
sequence). With `TimeM` you would have to thread and sum the potential by hand;
here the two interpreters `queriesOn` and `eval` do it for you.
-/

set_option autoImplicit false

open Cslib (FreeM)

namespace Chapter2Amortized

/-! ## The counter and its one query

The counter is a little-endian list of bits (least-significant first). The only
operation with a cost is flipping one bit, modelled as the single query `flip`,
which costs one. `queriesOn` therefore counts **bit-flips** — the standard cost
measure for a binary counter. -/

inductive BitOp : Type → Type where
  | flip : BitOp Unit    -- flip one bit; this is the unit of cost

/-- Emit one flip query. -/
def flipBit : FreeM BitOp Unit := FreeM.lift BitOp.flip

/-- The (only sensible) oracle: answering a `flip` yields `()`. The result of a
program is independent of the oracle here — a flip carries cost, not data. -/
def bitOracle : {ι : Type} → BitOp ι → ι
  | _, .flip => ()

/-- Potential function `Φ`: the number of 1-bits currently set. -/
def phi : List Bool → Nat
  | []          => 0
  | false :: bs => phi bs
  | true  :: bs => phi bs + 1

/-! ## `inc`: increment by one

Increment flips the low bit; if it was already `1`, that bit goes to `0` and the
carry recurses into the higher bits. Each flip is one query. -/

def inc : List Bool → FreeM BitOp (List Bool)
  | []          => do flipBit; pure [true]              -- 0 → 1
  | false :: bs => do flipBit; pure (true :: bs)        -- no carry: one flip
  | true  :: bs => do flipBit; let bs' ← inc bs; pure (false :: bs')  -- carry

-- ## Step lemmas: how `eval` and `queriesOn` act on one `inc`

@[simp] theorem inc_eval_nil (o : {ι : Type} → BitOp ι → ι) :
    (inc []).eval o = [true] := by simp [inc, flipBit]
@[simp] theorem inc_eval_false (o : {ι : Type} → BitOp ι → ι) (bs : List Bool) :
    (inc (false :: bs)).eval o = true :: bs := by simp [inc, flipBit]
@[simp] theorem inc_eval_true (o : {ι : Type} → BitOp ι → ι) (bs : List Bool) :
    (inc (true :: bs)).eval o = false :: (inc bs).eval o := by simp [inc, flipBit]

@[simp] theorem inc_queriesOn_nil (o : {ι : Type} → BitOp ι → ι) :
    (inc []).queriesOn o = 1 := by simp [inc, flipBit]
@[simp] theorem inc_queriesOn_false (o : {ι : Type} → BitOp ι → ι) (bs : List Bool) :
    (inc (false :: bs)).queriesOn o = 1 := by simp [inc, flipBit]
@[simp] theorem inc_queriesOn_true (o : {ι : Type} → BitOp ι → ι) (bs : List Bool) :
    (inc (true :: bs)).queriesOn o = 1 + (inc bs).queriesOn o := by simp [inc, flipBit]

/-! ## Correctness: `inc` really is "+1"

The program does not cheat: read as a little-endian number, its result is the
input plus one. This uses only `eval`, never the cost. -/

def toNat : List Bool → Nat
  | []          => 0
  | false :: bs => 2 * toNat bs
  | true  :: bs => 1 + 2 * toNat bs

theorem inc_toNat (o : {ι : Type} → BitOp ι → ι) (bs : List Bool) :
    toNat ((inc bs).eval o) = toNat bs + 1 := by
  induction bs with
  | nil => simp [toNat]
  | cons b bs ih =>
    cases b with
    | false => simp only [inc_eval_false, toNat]; omega
    | true  => simp only [inc_eval_true, toNat, ih]; omega

/-! ## The amortized bound

### Single step: amortized cost is exactly 2

`actual flips + ΔΦ = 2`. Rearranged so both sides are `Nat`-subtraction-free. -/

theorem inc_amortized (o : {ι : Type} → BitOp ι → ι) (bs : List Bool) :
    (inc bs).queriesOn o + phi ((inc bs).eval o) = phi bs + 2 := by
  induction bs with
  | nil => simp [phi]
  | cons b bs ih =>
    cases b with
    | false => simp only [inc_eval_false, inc_queriesOn_false, phi]; omega
    | true  =>
      simp only [inc_eval_true, inc_queriesOn_true, phi] at ih ⊢
      omega

/-! ### Whole sequence

`incTimes n bs` runs `inc` `n` times in a row, carrying the counter along. -/

def incTimes : Nat → List Bool → FreeM BitOp (List Bool)
  | 0,     bs => pure bs
  | k + 1, bs => do let bs' ← inc bs; incTimes k bs'

/-- Telescoped invariant: total flips + final potential = initial potential + 2n.
The single-step amortized cost `2` sums exactly, with no error term. -/
theorem incTimes_amortized (o : {ι : Type} → BitOp ι → ι) (n : Nat) (bs : List Bool) :
    (incTimes n bs).queriesOn o + phi ((incTimes n bs).eval o) = phi bs + 2 * n := by
  induction n generalizing bs with
  | zero => simp [incTimes]
  | succ k ih =>
    have hstep : (incTimes (k + 1) bs).queriesOn o
          + phi ((incTimes (k + 1) bs).eval o)
        = (inc bs).queriesOn o
          + ((incTimes k ((inc bs).eval o)).queriesOn o
             + phi ((incTimes k ((inc bs).eval o)).eval o)) := by
      simp [incTimes]; omega
    rw [hstep, ih ((inc bs).eval o)]
    have := inc_amortized o bs
    -- (inc bs).queriesOn + (phi(inc bs eval) + 2k) = phi bs + 2(k+1)
    omega

/-- **Amortized `O(1)`.** Starting from zero, `n` increments cost at most `2 n`
bit-flips in total — even though a single increment can cost far more (see
`inc_all_ones` below). The potential `Φ ≥ 0` absorbs the difference. -/
theorem incTimes_queriesOn_le (o : {ι : Type} → BitOp ι → ι) (n : Nat) :
    (incTimes n []).queriesOn o ≤ 2 * n := by
  have h := incTimes_amortized o n []
  simp only [phi] at h
  omega

/-! ### Contrast: a single increment can be expensive

A counter of `k` ones (the value `2^k − 1`) is the worst case: the carry ripples
through all `k` bits and sets a new one, `k + 1` flips. This is the `Θ(log v)`
worst-case single-operation cost that the `2n` amortized bound smooths over. -/

theorem inc_all_ones (o : {ι : Type} → BitOp ι → ι) (k : Nat) :
    (inc (List.replicate k true)).queriesOn o = k + 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, inc_queriesOn_true, ih]
    omega


/-! ## Demonstration

The pay-off: `queriesOn` gives the total cost of a whole sequence directly, and
the amortized bound holds although individual steps vary. -/

-- One expensive increment: 0b111 (=7) → 0b1000 (=8) ripples 4 flips:
#eval (inc [true, true, true]).queriesOn bitOracle        -- 4
#eval toNat ((inc [true, true, true]).eval bitOracle)     -- 8

-- Eight increments from zero: per-step flips are 1,2,1,3,1,2,1,4 (= 15 total),
-- comfortably under the amortized bound 2·8 = 16:
#eval (incTimes 8 []).queriesOn bitOracle                 -- 15
#eval 2 * 8                                                -- 16 (the bound)
#eval phi ((incTimes 8 []).eval bitOracle)                -- 1  (Φ of 0b1000)

-- the amortized theorem, specialised to n = 8:
example : (incTimes 8 []).queriesOn bitOracle ≤ 2 * 8 :=
  incTimes_queriesOn_le bitOracle 8


/-! # Second example: `build p` (Bird & Gibbons, *ADwH* §2.4)

The book's headline amortized example, right next to the binary counter above:

```
build p     = foldr insert []   where insert x xs = x : dropWhile (p x) xs
```

`build (==)` removes *adjacent* duplicates, e.g. `build (==) [4,4,2,1,1,2,5] =
[4,2,1,2,5]`. A single `insert` can be `Θ(k)` — its `dropWhile` may scan the
whole accumulator — so naively `build` looks `Θ(n²)`. Yet its true cost is
`Θ(n)`: **each element, once added, can be dropped at most once**, so the total
number of drops is bounded by the number of adds, `n`. The amortized cost of
`insert` is therefore `O(1)`.

We formalise exactly the book's *uniform method* (its inequality 2.3): pick a
nonnegative size `S` and amortized cost `A` with

```
C(before) ≤ S(before) − S(after) + A          -- for every step
```

then summing telescopes to `Σ C ≤ S(x₀) − S(xₙ) + Σ A`. Here `C` is `queriesOn`
(one query per predicate evaluation `p x y`), `S = length`, and `A = 2`. The
`Nat`-subtraction-free rearrangement `C(before) + S(after) ≤ S(before) + A` is
what we prove and telescope, giving the `≤ 2n` total bound.

Unlike the counter (where amortized cost is *exactly* 2), here it is `≤ 2`, so
this example exercises the *inequality* form of the potential method. -/

/-- One evaluation of the adjacency predicate `p x y`; the unit of cost. Just
like the comparison query in the sorting examples, the predicate is a *query*. -/
inductive PredOp (a : Type) : Type → Type where
  | ask : a → a → PredOp a Bool

/-- Emit one predicate query. -/
def ask {a : Type} (x y : a) : FreeM (PredOp a) Bool := FreeM.lift (PredOp.ask x y)

/-- Honest oracle: answer `ask x y` with the actual predicate `p x y`. -/
def predOracle {a : Type} (p : a → a → Bool) : {ι : Type} → PredOp a ι → ι
  | _, .ask x y => p x y

/-- `dropWhile (p x)`, made explicit: one `ask` per element examined. -/
def dropW {a : Type} (x : a) : List a → FreeM (PredOp a) (List a)
  | []      => pure []
  | y :: ys => do
      let b ← ask x y
      if b then dropW x ys else pure (y :: ys)

/-- `insert x xs = x : dropWhile (p x) xs`. -/
def ins {a : Type} (x : a) (xs : List a) : FreeM (PredOp a) (List a) := do
  let r ← dropW x xs
  pure (x :: r)

/-- `build p = foldr insert []`. -/
def build {a : Type} : List a → FreeM (PredOp a) (List a)
  | []      => pure []
  | x :: xs => do
      let r ← build xs
      ins x r

-- ## Step lemmas for `dropW`

@[simp] theorem dropW_eval_nil {a : Type} (o : {ι : Type} → PredOp a ι → ι) (x : a) :
    (dropW x ([] : List a)).eval o = [] := by simp [dropW]
@[simp] theorem dropW_queriesOn_nil {a : Type} (o : {ι : Type} → PredOp a ι → ι) (x : a) :
    (dropW x ([] : List a)).queriesOn o = 0 := by simp [dropW]

theorem dropW_eval_cons {a : Type} (o : {ι : Type} → PredOp a ι → ι)
    (x y : a) (ys : List a) :
    (dropW x (y :: ys)).eval o =
      if o (PredOp.ask x y) then (dropW x ys).eval o else y :: ys := by
  simp [dropW, ask]; split <;> simp_all

theorem dropW_queriesOn_cons {a : Type} (o : {ι : Type} → PredOp a ι → ι)
    (x y : a) (ys : List a) :
    (dropW x (y :: ys)).queriesOn o =
      1 + (if o (PredOp.ask x y) then (dropW x ys).queriesOn o else 0) := by
  simp [dropW, ask]; split <;> simp_all

/-! ### The uniform bound (eq. 2.3) for one `dropWhile`/`insert`

`S = length`, `A = 2`. Everything below is `Nat`-subtraction-free. -/

/-- Cost plus size-after ≤ size-before + 1 for a `dropWhile`: the drops are the
"free" part paid for when the elements were originally added. -/
theorem dropW_bound {a : Type} (o : {ι : Type} → PredOp a ι → ι) (x : a) (xs : List a) :
    (dropW x xs).queriesOn o + ((dropW x xs).eval o).length ≤ xs.length + 1 := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    rw [dropW_queriesOn_cons, dropW_eval_cons]
    cases h : o (PredOp.ask x y) <;> simp <;> omega

/-- The book's inequality 2.3 for one `insert`: `C ≤ S(before) − S(after) + 2`,
in the subtraction-free form `C + S(after) ≤ S(before) + 2`. -/
theorem ins_bound {a : Type} (o : {ι : Type} → PredOp a ι → ι) (x : a) (xs : List a) :
    (ins x xs).queriesOn o + ((ins x xs).eval o).length ≤ xs.length + 2 := by
  have hq : (ins x xs).queriesOn o = (dropW x xs).queriesOn o := by simp [ins]
  have he : ((ins x xs).eval o).length = ((dropW x xs).eval o).length + 1 := by
    simp [ins, List.length_cons]
  rw [hq, he]
  have := dropW_bound o x xs
  omega

/-! ### Telescoped: `build` is `Θ(n)` -/

/-- Summing the per-step bound telescopes: total cost + final size ≤ `2n`. -/
theorem build_amortized {a : Type} (o : {ι : Type} → PredOp a ι → ι) (xs : List a) :
    (build xs).queriesOn o + ((build xs).eval o).length ≤ 2 * xs.length := by
  induction xs with
  | nil => simp [build]
  | cons x xs ih =>
    have hq : (build (x :: xs)).queriesOn o
        = (build xs).queriesOn o + (ins x ((build xs).eval o)).queriesOn o := by
      simp [build]
    have he : (build (x :: xs)).eval o = (ins x ((build xs).eval o)).eval o := by
      simp [build]
    rw [hq, he, List.length_cons]
    have hins := ins_bound o x ((build xs).eval o)
    omega

/-- **Amortized `O(1)` per insert.** `build` on `n` elements makes at most `2 n`
predicate evaluations, though a single `insert` can make `Θ(k)`. -/
theorem build_queriesOn_le {a : Type} (o : {ι : Type} → PredOp a ι → ι) (xs : List a) :
    (build xs).queriesOn o ≤ 2 * xs.length := by
  have := build_amortized o xs
  omega

/-! ## Demonstration (the book's own example)

`build (==)` removing adjacent duplicates, exactly as in Bird & Gibbons. -/

/-- Honest oracle for `build (==)`. -/
def eqOracle : {ι : Type} → PredOp Nat ι → ι := predOracle (fun x y => x == y)

#eval (build [4, 4, 2, 1, 1, 2, 5]).eval eqOracle        -- [4, 2, 1, 2, 5]  (the book)
#eval (build [4, 4, 2, 1, 1, 2, 5]).queriesOn eqOracle   -- 8   (predicate evaluations)
#eval 2 * [4, 4, 2, 1, 1, 2, 5].length                   -- 14  (the amortized bound 2n)

example : (build [4, 4, 2, 1, 1, 2, 5]).queriesOn eqOracle ≤ 2 * 7 := by
  simpa using build_queriesOn_le eqOracle [4, 4, 2, 1, 1, 2, 5]

end Chapter2Amortized
