import Cslib.Algorithms.Lean.TimeM
import Fad.Chapter1
import Fad.Chapter3
import Fad.Chapter5
import Fad.«Chapter1-Ex»
import Fad.«Chapter4-Ex»
import Fad.«Chapter5-Ex»

namespace Chapter6

open Chapter1 (unwrap until' single)
open Chapter3 (accumArray elems)
open Chapter4 (partition)
open Chapter4.BST2 (partition3 Tree rotl Tree.height)
open Chapter5.Mergesort (merge pairWith halve length_halve_fst length_halve_snd)
open Chapter5.Quicksort (qsort₁)
open Chapter5 (csort)
open Cslib.Algorithms.Lean
open TimeM

-- # Section 6.1: minimum and maximum

variable {a : Type}
  [Inhabited a] [DecidableRel (α := a) (· = ·)]
  [Max a] [Min a]
  [LT a] [DecidableRel (α := a) (· < ·)]
  [LE a] [DecidableRel (α := a) (· ≤ ·)]


def foldr1₀ (f : a → a → a) (xs : List a) (h : xs ≠ []) : a
  :=
  if h₁ : xs.length = 1 then
    xs.head (by simp [h])
  else
    let b :: bs := xs
    f b (foldr1₀ f bs (by
      intro h₂; apply h₁ ; rw [h₂]; simp))

def foldr1 (f : a → a → a) : List a → a
  | []    => default
  | [x]   => x
  | x::xs => f x (foldr1 f xs)

def foldl1 (f : a → a → a) : List a → a
  | []    => default
  | x::xs => xs.foldl f x

def minimum : List a → a :=
  foldr1 min

def maximum : List a → a :=
  foldr1 max

theorem maximum_eq_foldrmax {a : Type} [LinearOrder a] [Inhabited a]
  (x : a) (xs : List a)
  : maximum (x::xs) = xs.foldr max x := by
  simp [maximum]
  induction xs generalizing x with
  | nil => rfl
  | cons y ys ih =>
    simp [foldr1, ← ih]
    induction ys generalizing x y with
    | nil => exact max_comm x y
    | cons z zs ih2 => grind [foldr1]

theorem minimum_eq_foldrmin {a : Type} [LinearOrder a] [Inhabited a]
  (x : a) (xs : List a)
  : minimum (x::xs) = xs.foldr min x := by
  simp [minimum]
  induction xs generalizing x with
  | nil => rfl
  | cons y ys ih =>
    simp [foldr1, ← ih]
    induction ys generalizing x y with
    | nil => exact min_comm x y
    | cons z zs ih2 => grind [foldr1]

def foldr1M (f : a → a → TimeM ℕ a) : List a → TimeM ℕ a
  | []    => pure default
  | [x]   => pure x
  | x :: y :: ys => do
    let rest ← foldr1M f (y :: ys)
    f x rest

def maxM (x y : Nat) : TimeM ℕ Nat := do
  ✓ pure (max x y)

def maximumM : List Nat → TimeM ℕ Nat :=
  foldr1M maxM

theorem time_maximum (xs : List Nat) :
  (maximumM xs).time = xs.length - 1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => rfl
    | cons y ys =>
      simp_all [maximumM, foldr1M, maxM]

def minmax₀ : List a → (a × a)
  | []      => default
  | x :: xs =>
    let op x q := (min x q.1, max x q.2)
    xs.foldr op (x,x)

def minmax₁ : List a → (a × a)
  | []      => default
  | x :: xs =>
    let op x q :=
      if      x < q.1 then (x, q.2)
      else if x > q.2 then (q.1, x)
      else (q.1, q.2)
    xs.foldr op (x,x)

def minmax₁M : List Nat → TimeM ℕ (Nat × Nat)
  | [] => pure (0, 0)
  | [x] => pure (x, x)
  | x :: y :: ys => do
      let q ← minmax₁M (y :: ys)
      ✓ if x < q.1 then
        pure (x, q.2)
      else
        ✓ if x > q.2 then
          pure (q.1, x)
        else
          pure (q.1, q.2)

theorem time_minmax1M_worst :
∀ (xs : List Nat), (minmax₁M xs).time ≤ 2 * xs.length
  | [] => by rfl
  | [x] => by simp [minmax₁M]
  | x :: y :: ys => by
      simp [minmax₁M]
      have ih := time_minmax1M_worst (y :: ys)
      split_ifs
      all_goals
       simp_all
       omega

def minmax₂ : List a → (a × a)
  | []      => default
  | x :: xs =>
    if      h₁ : xs.length = 0 then (x, x)
    else if h₂ : xs.length = 1 then
     have h₃ : xs ≠ [] := by
      intro h; apply h₁
      apply List.length_eq_zero_iff.mpr; assumption
     if x ≤ xs.head h₃ then (x, xs.head h₃) else (xs.head h₃, x)
    else
     let p := halve xs
     have : (halve xs).fst.length < xs.length := by
      simp [length_halve_fst]; omega
     have : (halve xs).snd.length < xs.length := by
      simp [length_halve_snd]; omega
     let q := minmax₂ p.1
     let r := minmax₂ p.2
     (min q.1 r.1, max q.2 r.2)
termination_by xs => xs.length

def minmax2M : List Nat → TimeM ℕ (Nat × Nat)
  | [] => pure (0, 0)
  | [x] => pure (x, x)
  | [x, y] => do
    ✓ if x ≤ y then
      pure (x, y)
    else
      pure (y, x)
  | x₁ :: x₂ :: xs => do
      let p := halve (x₁ :: x₂ :: xs)
      let q ← minmax2M p.1
      let r ← minmax2M p.2
      ✓[2] pure (min q.1 r.1, max q.2 r.2)
termination_by xs => xs.length
decreasing_by
  . simp [length_halve_fst]
    omega
  . simp [length_halve_snd]
    omega

theorem time_minmax2M (xs : List Nat) (h : xs.length > 2) :
  (minmax2M xs).time =
    (minmax2M (halve xs).1).time + (minmax2M (halve xs).2).time + 2 := by
  match xs with
  | [] => contradiction
  | [x] => contradiction
  | [x, y] => contradiction
  | x :: y :: ys =>
    rw [minmax2M]
    simp_all
    . rfl
    . intro h
      simp_all


def mkPairs : List a → List (a × a)
  | []           => []
  | [x]          => [(x, x)]
  | x :: y :: xs =>
    if x ≤ y then
     (x, y) :: mkPairs xs
    else
     (y, x) :: mkPairs xs

def mkPairsM : List Nat → TimeM ℕ (List (Nat × Nat))
  | []           => pure []
  | [x]          => pure [(x, x)]
  | x :: y :: xs => do
      let rest ← mkPairsM xs
      ✓ if x ≤ y then
        pure ((x, y) :: rest)
      else
        pure ((y, x) :: rest)

theorem time_mkPairsM (xs : List Nat) : (mkPairsM xs).time = xs.length / 2 := by
  match xs with
  | [] => rfl
  | [x] => simp [mkPairsM]
  | x :: y :: ys =>
    simp [mkPairsM]
    split_ifs
    all_goals
      simp
      have ih := time_mkPairsM ys
      omega

def minmax (xs : List a) : (a × a) :=
  let op p q := (min p.1 q.1, max p.2 q.2)
  (unwrap ∘ until' single (pairWith op) ∘ mkPairs) xs
    |>.getD default


-- # Section 6.2: selection from one set

/-
#check let xs := [1,2,3];
 xs.get (Fin.mk 2 (by simp [List.length]) : Fin xs.length)
-/

def select₀ (k : Nat) (xs : List a) : a :=
 (qsort₁ xs)[k - 1]!

def median (xs : List a) : a :=
  let k := (xs.length + 1) / 2
  select₀ k xs


def group (n : Nat) (xs : List a) : List (List a) :=
  if      h₁ : n = 0   then []
  else if h₂ : xs = [] then []
  else
   let p := xs.splitAt n
   have : xs.length - n < xs.length := by
    induction xs with
    | nil => simp at *
    | cons b bs ih =>
      simp ; omega
   p.1 :: (group n p.2)
 termination_by xs.length

-- #eval group 5 (List.range' 1 12)

/- `qsort₁` or `qsort` ? -/
def medians : List a → List a :=
  let middle (xs : List a) := xs[((xs.length + 1) / 2) - 1]!
  List.map (middle ∘ qsort₁) ∘ group 5

-- #eval medians (List.range' 1 12)

/- `select₀` or `select` ? -/
def pivot : List a → a
  | [x] => x
  | xs  =>
    let median xs := select₀ ((xs.length + 1) / 2) xs
    median (medians xs)


partial def qsort : List a → List a
  | [] => []
  | xs =>
    let p := partition3 (pivot xs) xs
    qsort p.1 ++ p.2.1 ++ qsort p.2.2

theorem partition3_length {a : Type} [LT a] [DecidableRel (α := a) (· < ·)]
 [DecidableRel (α := a) (· = ·)]
 (y :a) (xs : List a) :
  (partition3 y xs).2.2.length +
  (partition3 y xs).2.1.length +
  (partition3 y xs).1.length =
  xs.length := by
  induction' xs with x xs ih
  . rfl
  . grind [partition3]

/- I can't proof the termination -/
partial def select (k : Nat) (xs : List a) (ok : k ≤ xs.length) : a :=
  let us := (partition3 (pivot xs) xs).1
  let vs := (partition3 (pivot xs) xs).2.1
  let ws := (partition3 (pivot xs) xs).2.2
  let m := us.length
  let n := vs.length
  if      h₁ : k ≤ m      then select k us (by grind)
  else if h₂ : k ≤ m + n  then vs[k - m - 1]
  else                         select (k - m - n) ws (by grind [partition3_length])

def partition3M (p : Nat) : List Nat → TimeM ℕ (List Nat × List Nat × List Nat)
  | [] => pure ([], [], [])
  | x :: xs => do
      let res ← partition3M p xs
      ✓ if x < p then
        pure (x :: res.1, res.2.1, res.2.2)
      else
        ✓ if x = p then
          pure (res.1, x :: res.2.1, res.2.2)
        else
          pure (res.1, res.2.1, x :: res.2.2)

theorem time_partition3M_le (p : Nat) (xs : List Nat) :
  (partition3M p xs).time ≤ 2 * xs.length := by
  induction xs with
  | nil =>
    rfl
  | cons x xs ih =>
    simp [partition3M]
    split_ifs
    all_goals
      simp_all
      omega

/- may not be necessary -/
def select' (k : Nat) (xs : List a) (q: k ≤ xs.length): a :=
  let rec help (k : Nat) (xs : List a) (q: k ≤ xs.length) (fuel: Nat) : a :=
   match fuel with
   | 0 => panic!"Never here"
   | fuel+1 =>
     let us := (partition3 (pivot xs) xs).1
     let vs := (partition3 (pivot xs) xs).2.1
     let ws := (partition3 (pivot xs) xs).2.2
     let m := us.length
     let n := vs.length
     if      h₁:  k ≤ m     then help k us (by omega) fuel
     else if h₂:  k ≤ m + n then vs[k - m - 1]
     else                        help (k-m-n) ws (by grind [partition3_length]) fuel
  termination_by fuel
  help k xs q xs.length

-- # Section 6.3: selection from two set

theorem merge_length_eq_add_lenght {a : Type} [LE a] [DecidableRel (α := a) (· ≤ ·)]
  (as bs : List a) : (merge as bs).length = as.length + bs.length := by
  induction as generalizing bs with
  | nil => simp [merge]
  | cons a₀ as ih =>
    simp_all
    induction bs generalizing a₀ as with
    | nil => simp [merge]
    | cons b₀ bs ih2 =>
      simp [merge]
      split_ifs
      all_goals
        simp_all
        linarith

def select2₀ (k: Nat) (as bs : List a) (ok : k < as.length + bs.length): a :=
  (merge as bs)[k]'(by grind [merge_length_eq_add_lenght])

def select2 (k : Nat) (as bs : List a)  (ok : k < as.length + bs.length): a :=
  match as, bs with
  | [], bs => bs[k]'(by simp_all)
  | as, [] => as[k]'(by simp_all)
  | a₀ :: as, b₀ :: bs =>
    let p  := (a₀ :: as).length / 2
    let q  := (b₀ :: bs).length / 2
    let xs := (a₀ :: as).take p
    let a  := ((a₀ :: as).drop p).head (by
      have h: p < (a₀ :: as).length := by grind
      simp_all
    )
    let ys := ((a₀ :: as).drop p).tail
    let us := (b₀ :: bs).take q
    let b  := ((b₀ :: bs).drop q).head (by
      have h: q < (b₀ :: bs).length := by grind
      simp_all
    )
    let vs := ((b₀ :: bs).drop q).tail
    if      h₁: a ≤ b ∧ k ≤ p + q then select2 k (a₀ :: as) us (by grind)
    else if h₂: a ≤ b             then select2 (k - p - 1) ys (b₀ :: bs) (by grind)
    else if h₃: b ≤ a ∧ k ≤ p + q then select2 k xs (b₀ :: bs) (by grind)
    else                           select2 (k - q - 1) (a₀ :: as) vs (by grind)
termination_by as.length + bs.length

-- #eval select2 6 [1, 4, 4, 7, 8, 11, 15] [2, 5, 9, 11, 15, 16, 20]

-- For some reason, there's a confusion with the Tree of Mathlib
-- #check Tree
-- #check _root_.Tree
abbrev BTree := Chapter4.BST2.Tree

/-
In this part, we will use .height as the size of the tree.
-/
def ValidSizeTree {a : Type} : BTree a → Prop
  | .null => True
  | .node s l _ r =>
      s = l.flatten.length + 1 + r.flatten.length ∧
      ValidSizeTree l ∧
      ValidSizeTree r

theorem size_eq_flatten_length {a : Type} (t : BTree a) (hValid : ValidSizeTree t) :
  t.height = t.flatten.length := by
  cases t with
  | null => rfl
  | node s l x r =>
    rcases hValid with ⟨hSize, hValid⟩
    simp [Chapter4.BST2.Tree.height, Tree.flatten]
    omega

def selectT₀ (k : Nat) (t₁ t₂ : BTree a)
  (ok : k < t₁.height + t₂.height) (hValid : ValidSizeTree t₁ ∧ ValidSizeTree t₂): a :=
  (merge (t₁.flatten) (t₂.flatten))[k]'(by
    repeat rw [size_eq_flatten_length] at ok
    . rw [merge_length_eq_add_lenght]
      omega
    . exact hValid.2
    . exact hValid.1
  )

def index₀ (t : BTree a) (k : Nat)
  (ok : k < t.height) (hValid : ValidSizeTree t): a :=
  (t.flatten)[k]'(by
    rw [size_eq_flatten_length] at ok
    . omega
    . exact hValid
  )

def index (t : BTree a) (k : Nat) (ok : k < t.height) (hValid : ValidSizeTree t) : a :=
  match t, hValid with
  | .null, _ => default
  | .node h l x r, ⟨hSize, hValidL, hValidR⟩ =>
    let p := l.height
    if      h₁: k < p then index l k (by omega) hValidL
    else if h₂: k = p then x
    else                   index r (k - p - 1) (by
      simp [Chapter4.BST2.Tree.height] at ok
      simp_all [size_eq_flatten_length, p]
      omega
    ) hValidR

theorem index_eq_index₀ {a : Type} [LE a] [DecidableRel (α := a) (· ≤ ·)] [Inhabited a]
(t : BTree a) (k : Nat) (ok : k < t.height) (hValid : ValidSizeTree t) :
  index t k ok hValid = index₀ t k ok hValid := by
    induction t generalizing k with
    | null => contradiction
    | node s l x r lih rih =>
      obtain ⟨hSize, hValidL, hValidR⟩ := hValid
      simp only [index, index₀, Tree.flatten]
      split_ifs with h1 h2
      . simp [lih, index₀]
        rw [size_eq_flatten_length] at h1
        . simp [h1]
        . exact hValidL
      . rw [size_eq_flatten_length] at h2
        . simp [h2]
        . exact hValidL
      . simp only [rih, index₀]
        rw [size_eq_flatten_length] at h1
        . rw [size_eq_flatten_length] at h2
          . simp_all [size_eq_flatten_length]
            grind
          . exact hValidL
        . exact hValidL

def selectT (k : Nat) (t₁ t₂ : BTree a)
    (ok : k < t₁.height + t₂.height) (hValid : ValidSizeTree t₁ ∧ ValidSizeTree t₂) : a :=
  match t₁, t₂, hValid with
  | t₁, .null, ⟨hValid1, hValid2⟩ =>
      index t₁ k (by simp_all [Chapter4.BST2.Tree.height]) hValid1
  | .null, t₂, ⟨hValid1, hValid2⟩ =>
      index t₂ k (by simp_all [Chapter4.BST2.Tree.height]) hValid2
  | .node h₁ l₁ x r₁, .node h₂ l₂ y r₂, ⟨hValid1, hValid2⟩ =>
    let ⟨hSize1, hValidL1, hValidR1⟩ := hValid1
    let ⟨hSize2, hValidL2, hValidR2⟩ := hValid2
    let p := l₁.height
    let q := l₂.height
    have hpl1 : l₁.height = l₁.flatten.length := size_eq_flatten_length l₁ hValidL1
    have hpr1 : r₁.height = r₁.flatten.length := size_eq_flatten_length r₁ hValidR1
    have hpl2 : l₂.height = l₂.flatten.length := size_eq_flatten_length l₂ hValidL2
    have hpr2 : r₂.height = r₂.flatten.length := size_eq_flatten_length r₂ hValidR2
    if ih₁ : x ≤ y ∧ k ≤ p + q then
      selectT k (.node h₁ l₁ x r₁) l₂
        (by simp_all [Chapter4.BST2.Tree.height, p, q]; omega)
        ⟨hValid1, hValidL2⟩
    else if ih₂ : x ≤ y then
      selectT (k - p - 1) r₁ (.node h₂ l₂ y r₂)
        (by simp_all [Chapter4.BST2.Tree.height, p, q]; omega)
        ⟨hValidR1, hValid2⟩
    else if ih₃ : y ≤ x ∧ k ≤ p + q then
      selectT k l₁ (.node h₂ l₂ y r₂)
        (by simp_all [Chapter4.BST2.Tree.height, p, q]; omega)
        ⟨hValidL1, hValid2⟩
    else
      selectT (k - q - 1) (.node h₁ l₁ x r₁) r₂
        (by simp_all [Chapter4.BST2.Tree.height, p, q]; omega)
        ⟨hValid1, hValidR2⟩

-- # Section 6.4: Selection from the complement of a set

def diffL {a : Type} [DecidableEq a] (xs ys : List a) : List a :=
  xs.filter (· ∉ ys)

infixl:50 " \\\\ " => diffL

-- Lean it's not lazy evaluation, but the min está a pelo menos xs.lenght+1
def selectC₀ (xs : List Nat) : Nat :=
  let searchSpace := List.range (xs.length + 1)
  let remaining := searchSpace \\ xs
  remaining.headD 0


def searchFrom (k : Nat) (xs : List Nat) : Nat :=
  match k, xs with
  | k, List.nil => k
  | k, x::xs =>
    if k = x then
      searchFrom (k + 1) xs
    else
      k

def selectC₁ (xs : List Nat) : Nat :=
  searchFrom 0 (qsort₁ xs)


def selectC₂ (xs : List Nat) : Nat :=
  let n := xs.length
  searchFrom 0 (csort n (xs.filter (· ≤ n)))


def selectC₃ (xs : List Nat) : Nat :=
  let n := xs.length
  let a := accumArray Nat.add 0 (0, n) ((xs.filter (· ≤ n)).map (·, 1))
  (elems (0, n) 0 a |>.takeWhile (· ≠ 0)).length


partial def selectFrom₀ (a : Nat) (xs : List Nat) : Nat :=
  if xs.isEmpty then a
  else
    let b := a + 1 + (xs.length / 2)
    let (ys, zs) := xs.partition (fun x => x < b)

    if ys.length = b - a then
      selectFrom₀ b zs
    else
      selectFrom₀ a ys

def selectC₄ (xs : List Nat) : Nat :=
  selectFrom₀ 0 xs


def selectFrom (a n : Nat) (xs : List Nat) : Nat :=
  if n = 0 then a
  else
    let b := a + 1 + (n / 2)
    let (ys, zs) := partition (· < b) xs
    let l := ys.length
    if      l = b - a then selectFrom b (n - l) zs
    else if l < n     then selectFrom a l ys
    -- se l>= n, quer dizer que tem números repetidos, retorna 'a' por padrão.
    else                   a

def selectC (xs : List Nat) : Nat :=
  selectFrom 0 xs.length xs

end Chapter6
