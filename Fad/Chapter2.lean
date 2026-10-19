import Fad.Chapter1
import Fad.«Chapter1-Ex»
import Lean
import Cslib.Algorithms.Lean.TimeM
import Mathlib.Analysis.Asymptotics.Theta

namespace Chapter2

open Chapter1 (dropWhile)
open Cslib.Algorithms.Lean
open TimeM

-- # 2.0 Complexity

def fib : Nat → Nat
  | 0     => 1
  | 1     => 1
  | n + 2 => fib (n + 1) + fib n

def fibFast (n : Nat) : Nat :=
  (loop n).2
where
  loop : Nat → Nat × Nat
  | 0   => (0, 1)
  | n+1 => let p := loop n; (p.2, p.1 + p.2)

/-
#eval fibFast 100
#reduce fib 100 -- try eval
#print fib
-/

example : fibFast 4 = 5 := by
  unfold fibFast
  unfold fibFast.loop
  unfold fibFast.loop
  unfold fibFast.loop
  unfold fibFast.loop
  unfold fibFast.loop
  rfl


-- # 2.2 Estimating running times
--
-- Cost model: `xs ++ ys` costs `xs.length` ticks, one per element of its
-- left argument. `append'` charges the same thing one tick at a time.
-- Building `[]`, `pure`, and pattern matching are free.

def append' {a} : List a → List a → TimeM Nat (List a)
  | [], ys => pure ys
  | x :: xs, ys => do
      ✓ return x :: (← append' xs ys)


def concat₁' {a} : List (List a) → TimeM Nat (List a) :=
  List.foldr (fun xs tys => do
    let ys ← tys
    ✓[xs.length] return xs ++ ys) (pure [])

def concat₁'' {a} : List (List a) → TimeM Nat (List a)
 | []         => pure []
 | xs :: xss  => do
   let res ← concat₁'' xss
   ✓[xs.length] return xs ++ res

private lemma concat₁'_step {a : Type*}
  (xs : List a) (xss' : List (List a)) :
  (concat₁' (xs :: xss')).time = (concat₁' xss').time + xs.length := by
  simp [concat₁', List.foldr]

/- if `xss` is a list of length `m` consisting of lists each of length `n`, then
`concat₁` is `Θ(m * n)` -/
theorem concat₁'_time (xss : List (List a))
  (n : Nat) (h : ∀ xs ∈ xss, xs.length = n)
  : (concat₁' xss).time = xss.length * n := by
  induction xss with
  | nil => simp [concat₁', List.foldr]
  | cons xs xss' ih =>
    have h₁ : xs.length = n := h xs List.mem_cons_self
    have h₂ : ∀ ys ∈ xss', ys.length = n := by
      intro ys hys
      exact h ys (List.mem_cons_of_mem xs hys)
    rw [concat₁'_step, ih h₂, h₁, List.length_cons]
    ring

theorem concat₁''_time (xss : List (List a))
  (n : Nat) (h : ∀ xs ∈ xss, xs.length = n)
  : (concat₁'' xss).time = xss.length * n := by
  induction xss with
  | nil => simp [concat₁'']
  | cons xs xss' ih =>
      have h₁ : xs.length = n := h xs List.mem_cons_self
      have h₂ : ∀ ys ∈ xss', ys.length = n := by
        intro ys hys
        exact h ys (List.mem_cons_of_mem xs hys)
      simp [concat₁'', ih h₂, h₁]
      ring


def concat₂' {a} : List (List a) → TimeM Nat (List a) :=
  List.foldl (fun txs ys => do
    let xs ← txs
    ✓[xs.length] return xs ++ ys) (pure [])

def concat₂'' {a} : List (List a) → TimeM Nat (List a) → TimeM Nat (List a)
 | [], t => t
 | xs :: xss, t =>  do
   let res ← t
   concat₂'' xss (do ✓[res.length] return res ++ xs)

private lemma concat₂'_step {a}
  (xss : List (List a)) (n k : Nat)
  (h : ∀ xs ∈ xss, xs.length = n)
  (acc : TimeM Nat (List a))
  (hacc : acc.ret.length = k * n)
  : (2 * (List.foldl (fun txs ys => do
       let xs ← txs
       ✓[xs.length] pure $ xs ++ ys) acc xss).time : Int)
    = 2 * acc.time + 2 * k * n * xss.length + n * xss.length * (xss.length - 1) := by
  induction xss generalizing k acc with
  | nil => simp
  | cons bs bss ih =>
    simp only [List.foldl, List.length_cons]
    have hbs : bs.length = n := h bs List.mem_cons_self
    have hbss : ∀ zs ∈ bss, zs.length = n :=
      fun zs hzs => h zs (List.mem_cons_of_mem bs hzs)
    set acc' := do let xs ← acc; ✓[xs.length] pure (xs ++ bs)
    have hacc'_t : acc'.time = acc.time + k * n := by simp [acc', hacc]
    have hacc'_l : acc'.ret.length = (k + 1) * n := by
      simp [acc', List.length_append, hacc, hbs]; ring
    specialize ih (k + 1) hbss acc' hacc'_l
    grind only

/- if `xss` is a list of length `m` consisting of lists each of length `n`, then
`concat₂` is `Θ(m^2 * n)` or `2 * time = n * m * (m - 1)` -/
theorem concat₂'_time (xss : List (List a))
  (n : Nat) (h : ∀ xs ∈ xss, xs.length = n)
  : (2 * (concat₂' xss).time : Int) = n * xss.length * (xss.length - 1) := by
  have h₁ := concat₂'_step xss n 0 h (pure []) (by simp)
  simp only [concat₂', time_pure] at *
  grind only


section

open Asymptotics Filter

/-- `concat₁'` on `m` lists of length `n` is `Θ(m * n)`, as both grow. -/
theorem concat₁'_isTheta (xss : ℕ × ℕ → List (List a))
    (hm : ∀ p, (xss p).length = p.1) (hn : ∀ p, ∀ xs ∈ xss p, xs.length = p.2) :
    (fun p => ((concat₁' (xss p)).time : ℝ)) =Θ[atTop ×ˢ atTop]
      (fun p => (p.1 : ℝ) * p.2) := by
  have h : (fun p => ((concat₁' (xss p)).time : ℝ)) = fun p => (p.1 : ℝ) * p.2 := by
    funext p
    rw [concat₁'_time _ p.2 (hn p), hm p]
    push_cast
    ring
  rw [h]

/-- `concat₂'` on `m` lists of length `n` is `Θ(m ^ 2 * n)`, as both grow. -/
theorem concat₂'_isTheta (xss : ℕ × ℕ → List (List a))
    (hm : ∀ p, (xss p).length = p.1) (hn : ∀ p, ∀ xs ∈ xss p, xs.length = p.2) :
    (fun p => ((concat₂' (xss p)).time : ℝ)) =Θ[atTop ×ˢ atTop]
      (fun p => (p.1 : ℝ) ^ 2 * p.2) := by
  have h : (fun p => ((concat₂' (xss p)).time : ℝ))
      = fun p => (p.2 : ℝ) * p.1 * ((p.1 : ℝ) - 1) / 2 := by
    funext p
    have e := concat₂'_time (xss p) p.2 (hn p)
    rw [hm p] at e
    have e' : (2 * ((concat₂' (xss p)).time : ℝ)) = (p.2 : ℝ) * p.1 * ((p.1 : ℝ) - 1) := by
      exact_mod_cast e
    linarith
  rw [h]
  have h2 : ∀ᶠ p : ℕ × ℕ in atTop ×ˢ atTop, 2 ≤ p.1 :=
    (eventually_ge_atTop 2).prod_inl atTop
  refine ⟨IsBigO.of_bound 1 ?_, IsBigO.of_bound 4 ?_⟩
  · filter_upwards [h2] with p hp
    have hm1 : (1 : ℝ) ≤ p.1 := by exact_mod_cast (by omega : 1 ≤ p.1)
    have hn0 : (0 : ℝ) ≤ p.2 := Nat.cast_nonneg _
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    nlinarith [mul_nonneg hn0 (by linarith : (0 : ℝ) ≤ p.1 - 1)]
  · filter_upwards [h2] with p hp
    have hm2 : (2 : ℝ) ≤ p.1 := by exact_mod_cast hp
    have hn0 : (0 : ℝ) ≤ p.2 := Nat.cast_nonneg _
    have hpos : (0 : ℝ) ≤ (p.2 : ℝ) * p.1 * ((p.1 : ℝ) - 1) / 2 := by
      have := mul_nonneg (mul_nonneg hn0 (by linarith : (0 : ℝ) ≤ p.1))
        (by linarith : (0 : ℝ) ≤ (p.1 : ℝ) - 1)
      linarith
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg hpos]
    nlinarith [mul_nonneg hn0 (by nlinarith : (0 : ℝ) ≤ (p.1 : ℝ) * (p.1 - 2))]

end


-- # 2.4 Amortised running times

def build {a} (p : a → a → Bool) : List a → List a :=
 List.foldr insert []
 where
  insert x xs := x :: dropWhile (p x) xs

example : build (· = ·) [4,4,2,1,1] = [4, 2, 1] := by
 unfold build
 unfold List.foldr
 unfold List.foldr
 unfold List.foldr
 unfold List.foldr
 unfold List.foldr
 unfold List.foldr
 set p := (fun x1 x2 : Nat => decide (x1 = x2)) with hp
 unfold build.insert
 rw [dropWhile]
 rw [dropWhile]
 rw [dropWhile]
 rfl


/- primeiro argumento evita lista infinita -/
def iterate : Nat → (a → a) → a → List a
 | 0         , _, x => [x]
 | Nat.succ n, f, x => x :: iterate n f (f x)

def bits (n : Nat) : List (List Bool) :=
  iterate n inc []
 where
   inc : List Bool → List Bool
   | [] => [true]
   | false :: bs => true :: bs
   | true  :: bs => false :: inc bs

def init₀ : List α → List α
| []      => panic! "no elements"
| [_]     => []
| x :: xs => x :: init₀ xs

def init₁ : List α → Option (List α)
| []      => none
| [_]     => some []
| x :: xs =>
   match init₁ xs with
   | none => none
   | some ys => some (x :: ys)

def init₂ : List α → Option (List α)
| []      => none
| [_]     => some []
| x :: xs => init₂ xs >>= (fun ys => pure (x :: ys))

def prune (p : List a → Bool) (xs : List a) : List a :=
 List.foldr cut [] xs
  where
    cut x xs := Chapter1.until' done init₀ (x :: xs)
    done (xs : List a) := xs.isEmpty ∨ p xs

def ordered : List Nat → Bool
 | [] => true
 | [_] => true
 | x :: y :: xs => x ≤ y ∧ ordered (y :: xs)

-- #eval prune ordered [3,7,8,2,3]

end Chapter2
