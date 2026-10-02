import Fad.Chapter4
import Fad.Chapter3
import Mathlib.Analysis.SpecialFunctions.Log.Base   -- Real.logb, Real.log, Real.log_pos, Real.log_le_log, Real.log_pow
import Mathlib.Data.Rat.Floor                       -- Rat.floor_cast, Rat.floor_intCast_div_natCast, Int.le_floor
import Mathlib.Tactic.Linarith.Frontend             -- linarith
import Mathlib.Tactic.NormNum.Basic                 -- norm_num
import Mathlib.Tactic.Positivity.Basic              -- positivity
import Mathlib.Tactic.Ring                          -- ring


namespace Chapter4


/- # Exercício 4.1

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


/- 4.2
We have smallest (a,b) = x such that f x < t ≤ f (x + 1)
But for t = 1024 and f x = x^2 below f x = t and f (x + 1) > t

#eval D1.smallest (fun x => dbg_trace "fun {x}"; x * x) 1024 (0, 1024)
#eval (fun x => dbg_trace "fun {x}"; x * x) 32
#eval (fun x => dbg_trace "fun {x}"; x * x) 33
-/

/- 4.3

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


/- 4.4 : see the book -/

/-!
# Exercicio 4.5

Indexing the coordinates from zero, the positions are
(0, 9), (5, 6), (7, 5), (9, 0)
-/

-- # Exercicio 4.6

-- #eval D2.search₁ (λ (x, y) => x ^ 3 + y ^ 3) 1729


-- # Exercicio 4.7

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

-- # Exercicio 4.8

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


-- # Exercise 4.9

def partition {α : Type} (p : α → Bool) : List α → List α × List α :=
  let op (x : α) (r : List α × List α) :=
   if p x then (x :: r.1, r.2) else (r.1, x :: r.2)
  List.foldr op ([], [])


-- # Exercicio 4.10

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

/- # Exercicio 4.13 -/

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


/- # Exercicio 4.14 -/

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


-- # Exercicio 4.16 - see Chapter4.lean


-- # Exercicio 4.17

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
