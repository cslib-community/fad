import Fad.Chapter1
import Batteries.Data.List.Basic
import Mathlib.Algebra.Group.Int.Even

namespace Chapter1

/- # Exercicio 1.1 -/

def inits {a} : List a → List (List a)
| [] => [[]]
| (x :: xs) => [] :: (inits xs).map (x :: ·)

def tails {a} : List a → List (List a)
| [] => [[]]
| (x :: xs) => (x :: xs) :: tails xs

def dropWhile {α} (p : α → Bool) : (xs : List α) → List α
| [] => []
| (x :: xs) => if p x then dropWhile p xs else x :: xs

/- # Exercicio 1.2 -/

def uncons {α : Type} : (xs : List α) → Option (α × List α)
  | [] => none
  | x :: xs => some (x, xs)


/- # Exercicio 1.3 -/

def wrap {α : Type} (a : α) : List α := [a]

example : ∀ x : a, wrap x = [x] := by
  unfold wrap
  grind

def unwrap {α : Type} (a : List α) : Option α :=
  match a with
  | [x] => some x
  | _   => none

def unwrap! {α : Type} [Inhabited α]  : (a : List α) → α
 | [x] => x
 | _   => panic! "unwrap!: not single list"

def single {α : Type} (a : List α) : Bool :=
  match a with
  | [_] => true
  | _   => false

example : single [42] = true := rfl
example : single [0, 1] = false := rfl
example : single ([] : List Nat) = false := rfl

example : ∀ xs : List Nat, single xs ↔ xs.length = 1 := by
  intro xs
  induction xs with
  | nil => simp [single]
  | cons x xs ih =>
    cases xs with
    | nil => simp [single]
    | cons a xs => simp [single]


/- # Exercicio 1.4 -/

def reverse₀ {α : Type} (a : List α) : List α :=
  let rec helper (a : List α) (res : List α) : List α :=
    match a with
    | [] => res
    | x :: xs => helper xs (x :: res)
  helper a []

def reverse₁ {a : Type} : List a → List a :=
 List.foldl (flip List.cons) []

theorem aux_rev_append {α : Type} (as bs: List α)
 : List.foldl (flip List.cons) as bs = (List.foldl (flip List.cons) [] bs) ++ as := by
  induction bs generalizing as with
    | nil => rfl
    | cons c cs ih =>
      rw [List.foldl, flip]
      rw [List.foldl, flip]
      rw [ih, ih [c]]
      simp

theorem rev_cons : reverse₁ (x :: xs) = reverse₁ xs ++ [x] := by
  rw (occs := .pos [1]) [reverse₁]
  rw [List.foldl, flip]
  rw [aux_rev_append]
  rfl

theorem rev_append {α : Type} (as bs: List α) :
reverse₁ (as ++ bs) = reverse₁ bs ++ reverse₁ as := by
  induction as generalizing bs with
    | nil => simp; rfl
    | cons c cs ih =>
      rw [List.cons_append]
      rw [rev_cons, rev_cons, ← List.append_assoc]
      rw [ih]

theorem reverse_reverse {α : Type}  (xs : List α)
 : reverse₁ (reverse₁ xs) = xs := by
 induction xs with
 | nil => rfl
 | cons a as ih =>
   rw [rev_cons]
   rw [rev_append]
   rw [ih]; simp [reverse₁, flip]


/- # Exercicio 1.5 -/

def map' {α β : Type} (f : α → β) (xs : List α) : List β :=
  let op x xs := f x :: xs
  List.foldr op [] xs

def filter' {α : Type} (p : α → Bool) (xs : List α) : List α :=
  let op x xs := if p x then x :: xs else xs
  List.foldr op [] xs


/- # Exercicio 1.6 -/

theorem foldr_filter_aux :
 (foldr f e ∘ filter p) ys = foldr f e (filter p ys) := by
 rfl

example (f : α → β → β)
 : foldr f e ∘ filter p = foldr (λ x y => if p x then f x y else y) e
 := by
  funext xs
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    rw [Function.comp]
    rw [filter]
    by_cases h : p y = true
    rw [if_pos h]
    rw [foldr]
    rw [foldr]
    rw [if_pos h]
    rewrite [←foldr_filter_aux]
    exact congrArg (f y) ih
    rw [if_neg h]
    rw [foldr]
    rw [if_neg h]
    rewrite [←foldr_filter_aux]
    exact ih


/- # Exercicio 1.7 -/

def takeWhile {α : Type} (p : α → Bool) : List α → List α :=
  let op x acc := if p x then x :: acc else []
  List.foldr op []

example : takeWhile (fun x => x % 2 = 0) [2, 3, 4, 5] = [2] := by
  rw [takeWhile]
  rw [List.foldr]
  rw [List.foldr]
  rw [List.foldr]
  rw [List.foldr]
  rw [List.foldr]
  rfl


/- # Exercicio 1.8 -/

def dropWhileEnd {α : Type} (p : α → Bool) (xs : List α) : List α :=
 let op x xs := if p x ∧ xs.isEmpty then [] else x :: xs
 xs.foldr op []


/- # Exercicio 1.9 -/

def foldr' {a b : Type} [Inhabited a]
  (f : a → b → b) (e : b) (xs : List a) : b :=
  if h : xs.isEmpty then
    e
  else
    have : xs.length - 1 < xs.length := by
     cases xs with
     | nil => simp at h
     | cons a as => simp
    f (List.head xs (by simp at h; intro h₁ ; exact (h h₁)))
      (foldr' f e xs.tail)
termination_by xs.length


def last₁ {a : Type} (as : List a) (ok : as ≠ []) : a :=
  as.reverse.head (by simp ; assumption)

def init₁ {a : Type} : List a → List a :=
  List.reverse ∘ List.tail ∘ List.reverse


def foldl' {a b : Type}
  (f : b → a → b) (e : b) (xs : List a) : b :=
  if h: xs.isEmpty then
    e
  else
    have : (init₁ xs).length < xs.length := by
     unfold init₁
     cases xs with
     | nil => simp; simp at h
     | cons a as => simp
    have h₂ : xs ≠ [] := by simp at h ; assumption
    f (foldl' f e (init₁ xs)) (last₁ xs h₂)
termination_by xs.length


/- # Exercicio 1.11 -/

def integer: List Nat → Nat :=
  List.foldl shiftl 0
  where
   shiftl (n d : Nat) : Nat := 10 * n + d

def fraction : List Nat → Float :=
  List.foldr shiftr 0
  where
  shiftr (d : Nat) (n : Float) : Float := (d.toFloat + n)/10


/- # Exercicio 1.12 -/

example {a b : Type} (f : b → a → b) (e : b) :
  List.map (List.foldl f e) ∘ inits = scanl f e := by
  funext xs
  induction xs generalizing e with
  | nil => simp [inits, scanl]
  | cons x xs ih =>
    rw [Function.comp, inits]; simp
    rw [foldl_comp, scanl]
    rw [← ih (f e x)]
    simp

example {α β : Type} (f : α → β → β) (e : β) :
  List.map (List.foldr f e) ∘ tails = List.scanr f e := by
  funext xs
  induction xs with
  | nil =>
    rw [Function.comp]
    simp [tails, List.scanr]
  | cons y ys ih =>
    rw [Function.comp] at ih
    rw [Function.comp, tails, List.map, ih, List.scanr_cons]


/- # Exercicio 1.13 -/

def apply {a : Type} : Nat → (a → a) → a → a
 | 0, _     => id
 | n + 1, f => f ∘ apply n f

def apply₁ {a : Type} : Nat → (a → a) → a → a
 | 0, _     => id
 | n + 1, f => apply n f ∘ f


/- # Exercicio 1.14 -/

def inserts₁ {a : Type} (x : a) (ys : List a) : List (List a) :=
  let step y yss :=
    (x :: y :: (yss.head!.tail)) :: yss.map (y :: ·)
  ys.foldr step [[x]]


/- # Exercicio 1.15 -/

def remove {α : Type} [DecidableEq α] (x : α) : List α → List α
| []        => []
| (y :: ys) => if x = y then ys else y :: remove x ys

partial def perms₃ {α : Type} [DecidableEq α] : List α → List (List α)
| []  => [[]]
| as  =>
  as.flatMap (λ x => (perms₃ (remove x as)).map (λ ys => x :: ys))


/- # Exercício 1.17 -/

def replace (x : Int) : Int := if Even x then x else 0

def f (x y : Int) : Int := 2 * x + y

/- using `h = replace` and `f = g`, the general condition from the fusion law
does not work `∀ x y, h (f x y) = g x (h y)` for `x = 1` and `y = 1`. That is,
`replace (f 1 1) ≠ f 1 (replace 1)`
-/

theorem foldr_fusion_cxt {a b c : Type}
 (f : a → c → c) (e : c) (xs : List a)
 (g : a → b → b) (h : c → b)
 (h₁ : ∀ x (ys : List a), h (f x (ys.foldr f e)) = g x (h (ys.foldr f e)))
 : h (List.foldr f e xs) = List.foldr g (h e) xs := by
 induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [List.foldr]
    rw [h₁ x xs, ih]

/-- `replace` é a identidade em todo valor computado por `foldr f 0`,
  pois esses valores são sempre pares. --/
theorem replace_of_even {x : Int} (h : Even x) : replace x = x := by
  simp [replace, h]

theorem even_foldr_f (xs : List Int) : Even (xs.foldr f 0) := by
  induction xs with
  | nil => exact ⟨0, rfl⟩
  | cons x xs ih =>
    simp [f, Int.even_add, ih]
    use x
    exact Int.two_mul x


theorem replace_foldr_f_eq
  : replace ∘ List.foldr f 0 = List.foldr f 0 := by
  funext xs
  refine foldr_fusion_cxt f 0 xs f replace (fun x ys => ?_)
  have he : Even (ys.foldr f 0) := even_foldr_f ys
  rw [replace_of_even he]
  refine replace_of_even ?_
  obtain ⟨y, hy⟩ := he
  rw [hy]
  use x + y
  simp [f, Int.two_mul, Int.add_assoc]
  exact Int.add_left_comm x y y


/- # Exercício 1.18 -/

/-- Fusion law for `foldl`.

  The intuition mirrors the `foldr` fusion law: we want to push a
  post-processing function `h` *inside* a `foldl`, replacing an accumulator of
  type `c` by an already-transformed accumulator of type `b`.

  The hypothesis `h₁ : ∀ y x, h (f y x) = g (h y) x` states that `h` turns one
  step of `f` (taken on the untransformed accumulator) into the corresponding
  step of `g` (taken on the transformed accumulator). In other words, `h` is a
  step-by-step homomorphism between the two accumulators: the diagram commutes
  for every element `x` of the list.

  Consequently, applying `h` to the final result of `xs.foldl f e` is the same
  as running `xs.foldl g` starting from the transformed accumulator `h e`.

  Note the contrast with `foldr` fusion: since in `foldl` the accumulator sits
  on the *left*, the condition relates `h (f y x)` to `g (h y) x`, keeping `x`
  on the same side. --/
theorem foldl_fusion {a b c : Type}
  (f : c → a → c) (g : b → a → b) (h : c → b)
  (h₁ : ∀ y x, h (f y x) = g (h y) x)
  : ∀ e (xs : List a), h (xs.foldl f e) = xs.foldl g (h e) := by
  intro y xs
  induction xs generalizing y with
  | nil => rfl
  | cons x xs ih =>
    rewrite [List.foldl]
    rewrite [ih]
    rewrite [h₁]
    rfl


/- # Exercicio 1.20 -/

def concat {α : Type} (xss : List (List α)) : List α :=
  let op f (xs ys : List α) : List α := f (xs ++ ys)
  List.foldl op id xss []

example : concat [[1, 2], [3, 4]] = [1, 2, 3, 4] := by
  rw [concat]
  rewrite [List.foldl]
  rewrite [List.foldl]
  rewrite [List.foldl]
  rfl


/- # Exercicio 1.21 -/

-- set_option trace.profiler true

/- List.sum é implementada com List.foldr. Na documentação, List.foldr diz
   ser trocada em runtime pela implementação List.foldrTR onde TR é tail
   recursive.  -/

/-
def sum : (xs : List Nat) → Nat
 | [] => 0
 | x :: xs => x + sum xs

def sumTR : (xs : List Nat) → Nat → Nat
 | []     , ac => ac
 | x :: xs, ac => sumTR xs (ac + x)
-/

-- complexity O(n^2)
def steep₀ (xs : List Nat) : Bool :=
  match xs with
  | []  => true
  | x :: xs => x > xs.sum ∧ steep₀ xs

-- complexity O(n)
def steep₁ : List Nat → Bool :=
 Prod.snd ∘ faststeep
 where
  faststeep : List Nat → (Nat × Bool)
  | [] => (0, true)
  | x :: xs =>
    let (s, b) := faststeep xs
    (x + s, x > s ∧ b)

-- complexity O(n)
def steep₂ : List Nat → Bool :=
 Prod.snd ∘ faststeep
 where
  faststeep (xs : List Nat) : (Nat × Bool) :=
   xs.foldr (λ x t => (x + t.1, x > t.1 ∧ t.2) ) (0, true)

-- #eval steep₀ (List.range' 1 10000000).reverse
-- #eval steep₂ (List.range 10)
-- #eval steep₃ [8,5,2]

example : steep₀ [8,4,2,1] = steep₂ [8,4,2,1] := rfl

-- faststeep returns the correct sum as its first component
theorem faststeep_sum (xs : List Nat)
 : (steep₁.faststeep xs).1 = xs.sum := by
 induction xs with
 | nil =>
   simp [steep₁.faststeep]
 | cons x xs ih =>
   simp [steep₁.faststeep]
   rw [ih]

-- relationship between faststeep's boolean component and steep₀
theorem faststeep_bool (xs : List Nat)
 : (steep₁.faststeep xs).2 = steep₀ xs := by
  induction xs with
  | nil =>
    simp [steep₁.faststeep, steep₀]
  | cons x xs ih =>
    simp [steep₁.faststeep, steep₀]
    rw [faststeep_sum, ih]

-- steep₀ and steep₁ are equivalent
theorem steep₀_eq_steep₁ (xs : List Nat) : steep₀ xs = steep₁ xs
 := by
  simp [steep₁]
  rw [faststeep_bool]

end Chapter1
