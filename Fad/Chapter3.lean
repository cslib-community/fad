import Fad.Chapter1
import Fad.«Chapter1-Ex»
import Lean.Data.AssocList

namespace Chapter3
open List (reverse tail cons)

-- # Section 3.1 Symmetric lists

def _root_.List.single (xs : List α) : Bool := xs.length = 1

def snoc {a : Type} (x : a) (xs : List a) : List a :=
  xs ++ [x]


namespace DoesNotWork

variable {α : Type}

abbrev SymList α := (List α) × (List α)

def nilSL : SymList α := ([], [])

def fromSL (sl : SymList α) : List α :=
 sl.1 ++ sl.2.reverse

def snocSL : α → SymList α → SymList α
| z, ([], ys) => (ys, [z])
| z, (bs, ys) => (bs, z :: ys)

def consSL : α  → SymList α → SymList α
| z, (xs, []) => ([z], xs)
| z, (xs, ys) => (z :: xs, ys)

/-
example (x : α) (xs : SymList α)
 : (snoc x ∘ fromSL) xs = (fromSL ∘ snocSL x) xs
 := by
 have (as, bs) := xs
 unfold Function.comp
 unfold snoc
 induction as generalizing bs with
 | nil =>
   simp [fromSL, snocSL]
   sorry
 | cons y ys ih =>
   simp [fromSL, snocSL, List.reverse_cons, List.append_assoc]
-/

end DoesNotWork



structure SymList (a : Type) where
  lhs : List a
  rhs : List a
  ok : (lhs.isEmpty → rhs.isEmpty ∨ rhs.length = 1) ∧
       (rhs.isEmpty → lhs.isEmpty ∨ lhs.length = 1)
 deriving Repr

namespace SymList

variable {a : Type}

def nil : SymList a := SymList.mk [] [] (by simp)

instance : Inhabited (SymList a) where
  default := nil

def fromSL (sl : SymList a) : List a :=
 sl.lhs ++ sl.rhs.reverse

def consSL : a → SymList a → SymList a
| z, ⟨xs, [], h⟩ => SymList.mk [z] xs (by simp)
| z, ⟨xs, y :: ys, h⟩ => SymList.mk (z :: xs) (y :: ys) (by simp)

def snocSL : a → SymList a → SymList a
| z, ⟨ [], bs, _ ⟩ => ⟨bs, [z], by simp⟩
| z, ⟨ a :: as, bs, _ ⟩ => ⟨a :: as, z :: bs, by simp⟩

theorem cons_fromSL_eq_fromSL_consSL (x : a)
 : cons x ∘ fromSL = fromSL ∘ consSL x := by
 funext s
 cases s with
 | mk as bs h =>
   cases bs with
   | nil =>
     simp [consSL, fromSL]
     simp at h
     apply Or.elim h
     intro h1 ; rw [h1]; simp
     intro h1
     cases as with
     | nil => simp
     | cons z zs =>
       simp at h1
       rw [h1]; simp
   | cons z zs => simp [consSL, fromSL]

theorem snoc_fromSL_eq_fromSL_snocSL (x : a)
  : snoc x ∘ fromSL = fromSL ∘ snocSL x := by
  funext sl
  simp [Function.comp]
  have ⟨lhs, rhs, ok⟩ := sl
  unfold snoc snocSL fromSL
  match h: lhs with
  | [] =>
    simp
    simp at ok
    apply ok.elim <;> intro h2; simp [h2]
    have a :: [] := rhs
    simp
  | y :: ys => simp

def isEmpty (sl : SymList a) : Bool :=
  sl.lhs.isEmpty ∧ sl.rhs.isEmpty


theorem fromSL_isEmpty_iff_isEmpty (sl : SymList a)
  : (fromSL sl).isEmpty ↔ isEmpty sl := by
  cases sl with
  | mk as bs ok =>
    simp [isEmpty, fromSL]

theorem fromSL_ne_nil_of_not_isEmpty (sl : SymList a) (h : ¬ isEmpty sl)
  : fromSL sl ≠ [] := by
  intro he
  exact h ((fromSL_isEmpty_iff_isEmpty sl).mp (List.isEmpty_iff.mpr he))


def getLast (sl : SymList a) (ne : ¬ isEmpty sl) : a :=
 match sl with
 | ⟨xs, ys, ok⟩ =>
   if h₁ : ys.isEmpty then
     xs.head (by
      unfold isEmpty at ne; simp at ne
      intro h₂
      apply ne
      exact h₂
      simp at h₁
      exact h₁)
   else
     ys.head (by simp at h₁ ; exact h₁)

def getLast? : SymList a → Option a
 | ⟨[]    , []    , _⟩ => none
 | ⟨x :: _, []    , _⟩ => x
 | ⟨_     , y :: _, _⟩ => y


theorem fromSL_getLast_eq_getLast (sl : SymList a) (h : ¬ isEmpty sl)
  : (fromSL sl).getLast (fromSL_ne_nil_of_not_isEmpty sl h) = sl.getLast h := by
  cases sl with
  | mk as bs ok =>
    cases bs with
    | cons b bs' =>
      -- Case: bs is non-empty, so getLast = bs.head
      simp only [fromSL, getLast]
      rw [List.getLast_append_of_ne_nil (h₂ := by simp)]
      exact List.getLast_reverse _
    | nil =>
      -- Case: bs = [], the invariant forces as to be a singleton
      match as, ok.2 (by rfl) with
      | [x], h₂ => simp [fromSL, getLast]


def _root_.List.toSL : List a → SymList a
 | [] => nil
 | x :: xs => consSL x (toSL xs)

def headSL : SymList a → Option a
 | ⟨[], [], _⟩     => none
 | ⟨[], y :: _, _⟩ => some y
 | ⟨x::_, _, _⟩    => some x

def headSL! [Inhabited a] : SymList a → a
 | ⟨[], [], _⟩     => panic!"empty list"
 | ⟨[], y :: _, _⟩ => y
 | ⟨x::_, _, _⟩    => x


def singleSL (sl : SymList a): Bool :=
 match sl with
 | mk as [] _ => as.single
 | mk [] bs _ => bs.single
 | mk _ _ _   => false

def lengthSL (sl : SymList a) : Nat :=
  sl.lhs.length + sl.rhs.length


/- subtipos -/

@[simp]
def splitInTwoSL (xs : List a) : SymList a :=
  let p := List.MergeSort.Internal.splitInTwo (Subtype.mk xs (by rfl))
  SymList.mk p.1.val p.2.val.reverse (by
    have ⟨⟨as, aok⟩, ⟨bs, bok⟩⟩ := p
    simp [aok, bok]
    apply And.intro <;>
     (intro h; simp [h] at bok aok)
    if h2: bs.length = 0 then simp at h2; simp [h2] else omega
    if h2: as.length = 0 then simp at h2; simp [h2] else omega)

def tailSL {a : Type} (as : SymList a) : SymList a :=
  match as with
  | ⟨xs, ys, ok⟩ =>
    if h : xs.isEmpty then nil
    else
      if h2 : xs.length = 1 then
        splitInTwoSL ys.reverse
      else
        SymList.mk xs.tail ys (by
         simp [← not_congr List.length_eq_zero_iff] at h
         apply And.intro
         all_goals intro h3; have k :: (l :: ms) := xs
         repeat simp [ok] at *)


theorem tailSL_eq_tail
  : fromSL ∘ @tailSL a = tail ∘ fromSL := by
  funext as
  have ⟨xs, ys, ok⟩ := as
  cases xs with
  | nil =>
    induction ys with
    | nil => simp [tailSL, fromSL, nil]
    | cons b bs ih =>
      simp [fromSL, tailSL, nil]
      simp at *
      rw [ok]
      rw [List.reverse_nil, List.nil_append, List.tail]
  | cons a as =>
    induction ys with
    | nil =>
      by_cases h : as = [] <;> simp [h, fromSL, tailSL]
    | cons b bs ih =>
      by_cases h: as = []
      . simp [h, List.tail, fromSL] at ih
        simp [h, fromSL, tailSL]
      . simp [tailSL, h, fromSL]


theorem lengthSL_splitInTwoSL_eq_length (xs : List a)
 : lengthSL (splitInTwoSL xs) = List.length xs := by
  simp [lengthSL]
  omega


theorem length_tail_lt_length (sl : SymList a) (h : sl ≠ nil)
 : lengthSL sl > lengthSL (tailSL sl) := by
  have ⟨lsl, rsl, ok⟩ := sl
  unfold lengthSL tailSL
  simp
  by_cases k: lsl.isEmpty = true
  · simp [nil]
    simp_all
    cases ok with
    | intro h1 h2 =>
      simp [k] at h1
      cases h1 with
      | inl l => simp_all; contradiction
      | inr m => simp [m]
  · simp_all
    by_cases l: lsl.length = 1
    · simp [l, Nat.min_def]
      by_cases q: (rsl.length + 1) / 2 ≤ rsl.length
      · simp [q]
      simp [q]
      omega
    simp [l]
    grind

theorem headSL_none_iff_nilSL {sl : SymList a} : headSL sl = none ↔ sl = nil := by
  apply Iff.intro <;> intro h
  unfold headSL at h
  split at h
  unfold nil
  exact rfl
  repeat simp [eq_comm] at h
  rw [h]
  unfold headSL nil
  simp

theorem lengthSL_zero_iff_nilSL: lengthSL sl = 0 ↔ sl = nil := by
  apply Iff.intro <;> intro h
  rw [lengthSL] at h
  rw [Nat.add_eq_zero_iff] at h
  repeat rw [List.length_eq_zero_iff] at h
  unfold nil
  have ⟨h1, h2⟩ := h
  have ⟨lhs, rhs, ok⟩ := sl
  simp at h1 h2
  simp [h1, h2]
  rw [h]
  unfold nil lengthSL
  simp


def dropWhileSL (p : a → Bool) (sl : SymList a) : SymList a :=
  match h : headSL sl with
  | none => nil
  | some hsl =>
    if p hsl then
      let tl := tailSL sl
      have : lengthSL (tailSL sl) < lengthSL sl :=
        length_tail_lt_length sl (by
         if h2: sl = nil then
          rw [← headSL_none_iff_nilSL] at h2
          rw [h2] at h
          contradiction
         else
          exact h2)
      dropWhileSL p tl
    else sl
termination_by lengthSL sl


theorem head?_fromSL_eq_headSL : List.head? ∘ fromSL = @headSL a := by
  funext sl
  have ⟨lhs, rhs, ok⟩ := sl
  simp [Function.comp, headSL, fromSL]
  split <;> (
    rename_i h
    simp at h
    have ⟨ha, hb⟩ := h
    subst ha hb
    simp
  )
  simp at ok
  simp [ok]


theorem fromSL_eq_cons_fromSL_tailSL (sl : SymList a) (x : a)
    (h : headSL sl = some x)
  : fromSL sl = x :: fromSL (tailSL sl) := by
  have hhead : (fromSL sl).head? = some x := by
    have := congrFun head?_fromSL_eq_headSL sl
    simp [Function.comp] at this
    rw [this, h]
  have htail : fromSL (tailSL sl) = (fromSL sl).tail := by
    have := congrFun (@tailSL_eq_tail a) sl
    simpa [Function.comp] using this
  rw [htail]
  cases hc : fromSL sl with
  | nil => rw [hc] at hhead; simp at hhead
  | cons y ys =>
    rw [hc] at hhead
    simp at hhead
    simp [hhead]


theorem dropWhile_eq_dropWhileSL (p : a → Bool)
  : List.dropWhile p ∘ fromSL = fromSL ∘ dropWhileSL p := by
  funext sl
  simp only [Function.comp]
  fun_induction dropWhileSL p sl with
  | case1 sl hnone =>
    rw [headSL_none_iff_nilSL] at hnone
    subst hnone
    simp [nil, fromSL]
  | case2 sl hsl hhead hp tl _hterm ih =>
    rw [fromSL_eq_cons_fromSL_tailSL sl hsl hhead]
    rw [List.dropWhile_cons_of_pos (by simpa using hp)]
    exact ih
  | case3 sl hsl hhead hp =>
    rw [fromSL_eq_cons_fromSL_tailSL sl hsl hhead]
    rw [List.dropWhile_cons_of_neg (by simpa using hp)]


end SymList

/- examples of use -/

open List (map reverse tails) in

def inits₁ {a : Type} : List a → List (List a) :=
 map reverse ∘ reverse ∘ tails ∘ reverse

def inits₂ {a : Type} : List a → List (List a) :=
 List.map SymList.fromSL ∘ List.scanl (flip SymList.snocSL) SymList.nil


/- Let us show that inits₁ = inits₂ -/

theorem tails_append_singleton (xs : List α) (x : α) :
    (xs ++ [x]).tails = xs.tails.map (fun ys => ys ++ [x]) ++ [[]] := by
  induction xs with
  | nil      => simp
  | cons y ys ih =>
      simp [List.tails, ih]

theorem map_reverse_tails_snoc (x : α) (xs : List α) :
    List.map reverse (snoc x xs).tails =
      List.map (fun ys : List α => x :: reverse ys) xs.tails ++ [[]] := by
  simp [snoc, List.map_append, List.map_map, Function.comp]

theorem map_reverse (f : α → β) (xs : List α) :
    List.map f xs.reverse = (List.map f xs).reverse := by
  induction xs
  all_goals
  simp

theorem fromSL_snoc {α} (z : α) (sl : SymList α) :
    SymList.fromSL (SymList.snocSL z sl) = SymList.fromSL sl ++ [z] := by
  cases sl with
  | mk lhs rhs ok =>
      cases lhs with
      | nil =>
          cases rhs with
          | nil =>
              unfold SymList.fromSL
              unfold SymList.snocSL
              simp
          | cons y ys =>
              cases ys with
              | nil =>
                  unfold SymList.fromSL
                  unfold SymList.snocSL
                  simp
              | cons z zs =>
                  have hFalse : False := by
                    have h := (ok.left) (by simp)
                    cases h with
                    | inl h0 =>
                        simp at h0
                    | inr hlen1 =>
                        have : (List.length (y :: z :: zs)) = 1 := by
                          simp at hlen1
                        simp at this
                  cases hFalse
      | cons a as =>
          simp [SymList.snocSL, SymList.fromSL, List.reverse_cons,
            List.append_assoc]


theorem fromSL_foldl_snocSL {α} (zs : List α) (sl : SymList α) :
    SymList.fromSL (List.foldl (flip SymList.snocSL) sl zs)
      = SymList.fromSL sl ++ zs := by
  induction zs generalizing sl with
  | nil => simp
  | cons z zs ih =>
    simp [List.foldl_cons, flip, ih, fromSL_snoc]


theorem inits_eq {a : Type} (xs : List a) : inits₁ xs = inits₂ xs := by
  induction xs using List.reverseRecOn with
  | nil =>
    unfold inits₁ inits₂ SymList.fromSL SymList.nil
    simp
  | append_singleton ys y ih =>
    have hleft : inits₁ (ys ++ [y]) = inits₁ ys ++ [ys ++ [y]] := by
      simp [inits₁, Function.comp, List.reverse_append,
            List.reverse_cons, List.map_append, List.reverse_reverse]
    have hright : inits₂ (ys ++ [y]) = inits₂ ys ++ [ys ++ [y]] := by
      simp only [inits₂, Function.comp, List.scanl_append, List.map_append]
      congr 1
      simp only [List.scanl_cons, List.scanl_nil, List.tail_cons,
                 List.map_cons, List.map_nil, flip]
      rw [fromSL_snoc, fromSL_foldl_snocSL]
      simp [SymList.fromSL, SymList.nil]
    rw [hleft, hright, ih]


-- # Section 3.2 Random-access lists

namespace RAList

def fetch {a : Type} : Nat → List a → Option a
 | _, []      => none
 | k, x :: xs => if k = 0 then x else fetch (k - 1) xs

/-- info: some 3 -/
#guard_msgs in
#eval fetch 2 [1,2,3,4]

/-- info: some 3 -/
#guard_msgs in
#eval [1,2,3,4][2]?


inductive Tree (α : Type) : Type where
 | leaf (n : α) : Tree α
 | node (n : Nat) (t₁ : Tree α) (t₂ : Tree α) : Tree α
 deriving Repr

def Tree.toString {α : Type} [ToString α] : Tree α → String
 | leaf x => s!"leaf {x}"
 | node n t₁ t₂ => s!"node {n} ({t₁.toString}) ({t₂.toString})"

instance {α : Type} [ToString α] : ToString (Tree α) where
  toString := Tree.toString

def Tree.size {a : Type} : Tree a → Nat
 | leaf _ => 1
 | node n _ _ => n

def Tree.height : Tree α → Nat
 | leaf _ => 1
 | node _ t₁ t₂ => 1 + max t₁.height t₂.height

def Tree.mk (t₁ t₂ : Tree a) : Tree a :=
 node (t₁.size + t₂.size) t₁ t₂


inductive Digit (a : Type) : Type where
 | zero : Digit a
 | one (t : Tree a) : Digit a
 deriving Repr

def Digit.toString [ToString α] : Digit α → String
  | zero => "zero"
  | one t => s!"one ({t.toString})"

instance {α : Type} [ToString α] : ToString (Digit α) where
  toString := Digit.toString

end RAList

abbrev RAList (a : Type) : Type := List (RAList.Digit a)


def concat1 {a : Type} : List (List a) → List a :=
 List.foldr List.append []

def concatMap (f : a → List b) : List a → List b :=
 concat1 ∘ (List.map f)

namespace RAList

def fromT : Tree a → List a
 | .leaf x => [x]
 | .node _ t₁ t₂ => fromT t₁ ++ fromT t₂

def fromRA : RAList a → List a :=
  concatMap frm
 where
  frm : Digit a → List a
   | Digit.zero => []
   | Digit.one t => fromT t


def fetchT [ToString a] (n : Nat) (t : Tree a) : Option a :=
 match n, t with
 | 0, .leaf x       => x
 | k, .node n t₁ t₂ =>
   let m := n / 2
   if k < m then fetchT k t₁ else fetchT (k - m) t₂
 | _, .leaf _ => none

def fetchRA [ToString a] (n : Nat) (ra : RAList a) : Option a :=
 match n, ra with
 | _, [] => none
 | k, .zero :: xs  => fetchRA k xs
 | k, .one t :: xs =>
   if k < t.size then fetchT k t else fetchRA (k - t.size) xs


def nilRA {a : Type} : RAList a := []

def consRA {a : Type} (x : a) (xs : RAList a) : RAList a :=
 let rec consT : Tree a → RAList a → RAList a
  | t1, [] => [Digit.one t1]
  | t1, Digit.zero :: xs => Digit.one t1 :: xs
  | t1, Digit.one t2 :: xs => Digit.zero :: consT (Tree.mk t1 t2) xs
 consT (Tree.leaf x) xs

end RAList

/- # Section 3.3 Arrays -/

class Ix (α : Type) extends Ord α where
  inRange : (α × α) → α → Bool
  range : (α × α) → List α
  index : (α × α) → α → Nat
  rangeSize : (α × α) → Nat


instance instIxNat : Ix Nat where
  inRange := fun (low, high) i => low ≤ i ∧ i ≤ high
  range := fun (low, high) => List.range' low (high - low + 1)
  index := fun (low, high) i =>
    if low ≤ i ∧ i ≤ high then (i - low) else 0
  rangeSize := fun (low, high) =>
    if low ≤ high then (high - low + 1) else 0

instance instIxChar : Ix Char where
  inRange := fun (low, high) c => low ≤ c ∧ c ≤ high
  range := fun (low, high) =>
    if low ≤ high then
      let lc := low.toNat
      let hc := high.toNat
      List.range (hc - lc + 1) |>.map (Char.ofNat <| lc + ·)
    else []
  index := fun (low, high) c =>
    if low ≤ c ∧ c ≤ high then (c.toNat - low.toNat) else 0
  rangeSize := fun (low, high) =>
    if low ≤ high then (high.toNat - low.toNat + 1)  else 0


def listArray {i e : Type}  [Ix i] (bnds : i × i) (xs : List e)
  : Lean.AssocList i e :=
  (Ix.range bnds).zip xs |> List.toAssocList'


-- #eval listArray (0,5) [10, 20, 30, 40, 50] |>.toList

def accumArray₀ {i e v} [Ix i] [BEq i] (fcmb : e → v → e) (init : e)
  (bounds : i × i) (pairs : List (i × v)) : Lean.AssocList i e :=
  let valid := pairs.filter (fun (idx, _) => Ix.inRange bounds idx)
  valid.foldl (fun acc (idx, val) =>
    match acc.find? idx with
    | some v => acc.replace idx (fcmb v val)
    | none => acc.cons idx (fcmb init val)
  ) Lean.AssocList.nil


def accumArray {i e v : Type} [Ix i] [BEq i]
  (cmb : e → v → e) (init : e) (bounds : i × i)
  (as : List (i × v)) : Lean.AssocList i e :=
  let all := Ix.range bounds
  let initial := all.foldl (init := Lean.AssocList.nil)
    (fun acc idx => acc.cons idx init)
  let valids := as.filter (fun (idx, _) => Ix.inRange bounds idx)
  valids.foldl (init := initial) (fun acc (idx, val) =>
    match acc.find? idx with
    | some v => acc.replace idx (cmb v val)
    | none => acc  -- shouldn't happen since we pre-populated
  )

/-
#eval accumArray (· + ·) 0 (0,10) [(1,10),(1,10),(2,20),(3,30),(1,80)]
  |>.toList
-/

def assocs {i e : Type} [Ix i] [BEq i] (bounds : i × i)
  (default : e) (arr : Lean.AssocList i e) : List (i × e) :=
  let indices := Ix.range bounds
  indices.map (fun i => (i, arr.find? i |>.getD default))

def elems {i e : Type} [Ix i] [BEq i]
  (bnds : i × i) (default : e) (arr : Lean.AssocList i e)
  : List e :=
  assocs bnds default arr |>.map Prod.snd

def indices {i e : Type} [Ix i] [BEq i]
  (bnds : i × i) (default : e) (arr : Lean.AssocList i e)
  : List i :=
  assocs bnds default arr |>.map Prod.fst


def sort (m : Nat) (xs : List Nat) : List Nat :=
  let    a := accumArray (· + ·) 0 (0, m) (xs.map ((·, 1)))
  let copy := Function.uncurry (flip List.replicate)
  Chapter1.concatMap copy (assocs (0, m) 0 a)

-- #eval sort 6 [4,1,3,3,1,4,0]


end Chapter3
