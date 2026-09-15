import Fad.Chapter3
import Fad.Chapter1
import Fad.«Chapter1-Ex»

namespace Chapter3
open SymList

/- # Exercicio 3.1 -/
section Ex31

def abcd := "abcd".toList

example : (SymList.mk ['a','b','c'] ['d'] (by grind)).fromSL = abcd :=
  by rfl

example : (SymList.mk ['a'] ['d','c','b'] (by grind)).fromSL = abcd :=
  by rfl

example : (SymList.mk ['a','b'] ['d','c'] (by grind)).fromSL = abcd :=
  by rfl

example : abcd.toSL = List.foldr consSL nil abcd := by rfl

example : abcd.toSL = List.foldr consSL nil abcd := by rfl

example : List.foldl (flip snocSL) nil abcd =
  SymList.mk ['a'] ['d','c','b'] (by grind) := by rfl

end Ex31

/- # Exercicio 3.2

in Chapter3.lean

-/

/- # Exercicio 3.3

in Chapter3.lean

-/

-- # Exercicio 3.4

namespace SymList

def initSL {a : Type} : (sl : SymList a) → SymList a
| ⟨xs, ys, ok⟩ =>
  if h : ys.isEmpty then
    match xs with
    | [] => nil
    | _  => nil
  else
    if h2 : ys.length = 1 then
     splitInTwoSL xs
    else SymList.mk xs ys.tail (by
      simp [← not_congr List.length_eq_zero_iff] at h
      apply And.intro
      all_goals
       intro h3
       simp [h3] at ok
       cases ys with
       | nil => contradiction
       | cons b bs => simp_all)

/-- Reverter uma `SymList` é apenas trocar as duas metades, e a
    invariante é simétrica. -/
def reverseSL : SymList a → SymList a
 | ⟨as, bs, ok⟩ => ⟨bs, as, And.intro ok.2 ok.1⟩

theorem reverse_fromSL_eq_fromSL_reverseSL (sl : SymList a)
  : (fromSL sl).reverse = fromSL sl.reverseSL := by
  cases sl with
  | mk as bs _ => simp [fromSL, reverseSL]

/-- Em vez de duplicar o código das funções da frente nas funções de
    trás, definimos `initSL` em termos de `tailSL` e `reverseSL`.
    Compare com a definição direta acima. -/
def initSL₁ (sl : SymList a) : SymList a :=
  sl.reverseSL.tailSL.reverseSL

-- #eval [1,2,3].toSL |>.initSL₁ |>.fromSL -- returns [1,2]

/- A obrigação de correção é sobre `fromSL`, e não a igualdade
   `initSL₁ = initSL`: as duas podem devolver representações
   diferentes da mesma lista, já que `initSL` chama
   `splitInTwoSL xs` onde `tailSL` chama `splitInTwoSL ys.reverse`. -/

theorem reverse_tail_reverse_eq_dropLast (xs : List a)
  : xs.reverse.tail.reverse = xs.dropLast := by
  induction xs using List.reverseRecOn with
  | nil => simp
  | append_singleton xs x => simp

theorem fromSL_initSL₁_eq_dropLast_fromSL
  : fromSL ∘ @initSL₁ a = List.dropLast ∘ fromSL := by
  funext sl
  simp only [Function.comp, initSL₁]
  rw [← reverse_fromSL_eq_fromSL_reverseSL]
  rw [← Function.comp_apply (f := fromSL) (g := tailSL), tailSL_eq_tail]
  simp only [Function.comp]
  rw [← reverse_fromSL_eq_fromSL_reverseSL]
  exact reverse_tail_reverse_eq_dropLast _

end SymList

/- # Exercicio 3.5

in Chapter3.lean

-/

/- # Exercicio 3.6 -/

namespace SymList

theorem lengthSL_gt_lengthSL_initSL {a : Type}
 (sl : SymList a) (h : sl ≠ nil)
 : sl.lengthSL > sl.initSL.lengthSL := by
 have ⟨xs, ys, h₁⟩ := sl
 induction xs with
 | nil =>
   cases ys with
   | nil => contradiction
   | cons b bs =>
     have h₂ := h₁.1 ; simp at h₂
     simp [lengthSL, initSL, h₂, splitInTwoSL]
 | cons b bs ih₁ =>
   induction ys with
   | nil =>
     have h₂ := h₁.2 ; simp at h₂
     simp [lengthSL, initSL, h₂, nil]
   | cons n ns ih₂ =>
     clear ih₁ ih₂
     rcases ns with _ | ⟨m, ms⟩
     · have hsplit := lengthSL_splitInTwoSL_eq_length (b :: bs)
       simp only [initSL, List.isEmpty_cons, List.length_cons, List.length_nil,
                  reduceDIte, dif_neg, Bool.false_eq_true, not_false_eq_true]
       rw [hsplit]
       simp only [lengthSL, List.length_cons]
       omega
     · simp [lengthSL, initSL]

def initsSL {a : Type} (sl : SymList a) : SymList (SymList a) :=
  if h : sl.isEmpty then
   nil.snocSL sl
  else
    have : (initSL sl).lengthSL <  sl.lengthSL :=
      lengthSL_gt_lengthSL_initSL sl (by
       have ⟨lsl, rsl, _⟩ := sl
       simp [isEmpty] at h
       simp [nil]
       exact h)
    snocSL sl (initsSL (initSL sl))
 termination_by sl.lengthSL


theorem fromSL_splitInTwoSL {a : Type} (xs : List a) : fromSL (splitInTwoSL xs) = xs := by
  simp only [fromSL, splitInTwoSL, List.reverse_reverse]
  exact List.MergeSort.Internal.splitInTwo_fst_append_splitInTwo_snd _

theorem fromSL_initSL_eq_dropLast_fromSL {a : Type}
  : fromSL ∘ @initSL a = List.dropLast ∘ fromSL := by
  funext sl
  have ⟨xs, ys, ok⟩ := sl
  simp only [Function.comp]
  cases ys with
  | nil =>
    -- rhs empty: invariant forces xs empty or singleton
    simp only [initSL, List.isEmpty_nil, reduceDIte]
    simp only [fromSL, List.reverse_nil, List.append_nil]
    simp at ok
    rcases ok with h | h
    · subst h; simp [nil]
    · obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp h
      simp [nil]
  | cons y ys =>
    cases ys with
    | nil =>
      -- ys.length = 1: initSL = splitInTwoSL xs
      simp only [initSL, List.isEmpty_cons, List.length_cons, List.length_nil,
                 reduceDIte, dif_neg, Bool.false_eq_true, not_false_eq_true]
      rw [fromSL_splitInTwoSL]
      simp [fromSL]
    | cons z zs =>
      -- ys.length ≥ 2: initSL = mk xs ys.tail
      have hlen : ¬ (y :: z :: zs).length = 1 := by simp
      simp only [initSL, List.isEmpty_cons, Bool.false_eq_true, dif_neg,
                 not_false_eq_true, hlen]
      simp only [fromSL, List.tail_cons, List.reverse_cons]
      simp

theorem inits_eq_inits_dropLast_append {a : Type} (l : List a) (h : l ≠ [])
  : l.inits = l.dropLast.inits ++ [l] := by
  conv_lhs => rw [← List.dropLast_append_getLast h, List.inits_append]
  simp [List.dropLast_append_getLast h]

theorem initsSL_eq_inits {a : Type}
  : List.inits ∘ fromSL = List.map fromSL ∘ fromSL ∘ @initsSL a := by
  funext sl
  simp only [Function.comp]
  fun_induction initsSL sl with
  | case1 sl hempty =>
    have hnil : fromSL sl = [] :=
      List.isEmpty_iff.mp ((fromSL_isEmpty_iff_isEmpty sl).mpr hempty)
    rw [fromSL_snoc, hnil]
    simp only [fromSL, List.append_eq_nil_iff, List.reverse_eq_nil_iff] at hnil
    simp [nil, fromSL, hnil.1, hnil.2]
  | case2 sl hempty _hterm ih =>
    have hne : fromSL sl ≠ [] :=
      fromSL_ne_nil_of_not_isEmpty sl (by simpa using hempty)
    have hinit := congrFun (@fromSL_initSL_eq_dropLast_fromSL a) sl
    simp only [Function.comp] at hinit
    rw [fromSL_snoc, List.map_append, ← ih, hinit]
    rw [inits_eq_inits_dropLast_append (fromSL sl) hne]
    simp


end SymList

/- # Exercicio 3.7 -/

def inits {α : Type} : List α → List (List α) :=
 (List.map List.reverse ∘ (Chapter1.scanl (flip List.cons) []))


/- # Exercicio 3.8  -/

namespace RAList

def measure (ts : List (Tree a)) : Nat :=
  ts.foldr (λ t acc => size t + acc) 0
 where
  size : Tree a → Nat
  | Tree.leaf _       => 1
  | Tree.node _ t1 t2 => 1 + size t1 + size t2

def fromTs : List (Tree a) → List a
| [] => []
| (Tree.leaf x) :: ts =>
  have : measure ts < measure (Tree.leaf x :: ts) := by
   simp [measure,measure.size]
  x :: fromTs ts
| (Tree.node n t1 t2) :: ts =>
  have : measure (t1 :: t2 :: ts) < measure (Tree.node n t1 t2 :: ts) := by
   simp [measure, measure.size]
   rw [Nat.add_assoc]; simp
  fromTs (t1 :: t2 :: ts)
termination_by x1 => measure x1

end RAList

/- # Exercício 3.10

The first one I used `calc` and `apply?` helped a lot , despite it looks ugly.
But the second one (comented) I guess is more elegant and convenient, using
`show` -/

namespace RAList

def toRA {a : Type} : List a → RAList a :=
  List.foldr consRA nilRA

theorem fromRA_consT {a : Type} (t : Tree a) (ds : RAList a) :
    fromRA (consRA.consT t ds) = fromT t ++ fromRA ds := by
  induction ds generalizing t with
  | nil => rfl
  | cons d ds ih =>
    cases d with
    | zero => rfl
    | one t₂ =>
      calc
      fromRA (Digit.zero :: consRA.consT (Tree.mk t t₂) ds)
        = fromRA (consRA.consT (Tree.mk t t₂) ds) := by
          simp [fromRA, concatMap, concat1]
          exact Eq.symm ((fun {α} {xs} => List.nil_eq.mpr) rfl)
      _ = fromT (Tree.mk t t₂) ++ fromRA ds := by
          exact ih (Tree.mk t t₂)
      _ = fromT t ++ fromRA (Digit.one t₂ :: ds) := by
          simp [fromRA, concatMap, concat1, fromT, Tree.mk, List.append_assoc]
          exact List.toList_toArray

theorem fromRA_consT' {a : Type} (t : Tree a) (ds : RAList a) :
    fromRA (consRA.consT t ds) = fromT t ++ fromRA ds := by
  induction ds generalizing t with
  | nil => rfl
  | cons d ds ih =>
    cases d with
    | zero => rfl
    | one t₂ =>
      show fromRA (consRA.consT (Tree.mk t t₂) ds) = fromT t ++ (fromT t₂ ++ fromRA ds)
      rw [ih]
      show fromT t ++ fromT t₂ ++ fromRA ds = fromT t ++ (fromT t₂ ++ fromRA ds)
      rw [List.append_assoc]

example {a : Type} : ∀ (xs : List a), xs = fromRA (toRA xs) := by
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [toRA]
    unfold consRA
    simp [fromRA_consT, fromT]
    exact List.append_cancel_left (congrArg (HAppend.hAppend xs) ih)

example {a : Type} : ∀ (xs : List a), xs = fromRA (toRA xs) := by
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    show x :: xs = fromRA (consRA.consT (Tree.leaf x) (toRA xs))
    rw [fromRA_consT]
    show x :: xs = x :: fromRA (toRA xs)
    rw [← ih]

end RAList

-- # Exercicio 3.11

namespace RAList

def updateT : Nat → α → Tree α → Tree α
| 0, x, Tree.leaf _ => Tree.leaf x
| _, _, Tree.leaf y => Tree.leaf y -- problem
| k, x, Tree.node n t1 t2 =>
  let m := n / 2
  if k < m then
   Tree.node n (updateT k x t1) t2
  else
   Tree.node n t1 (updateT (k - m) x t2)

def updateRA : Nat → α → RAList α → RAList α
| _, _, [] => []
| k, x, Digit.zero :: xs => Digit.zero :: (updateRA k x xs)
| k, x, (Digit.one t) :: xs =>
  if k < t.size then
    (Digit.one $ updateT k x t) :: xs
  else
    (Digit.one t) :: (updateRA (k- t.size) x xs)

end RAList

-- ## Exercise 3.12

namespace RAList

open Function (uncurry) in

def updatesRA : RAList α → List (Nat × α) → RAList α
  | r, up => List.foldl (flip (uncurry updateRA)) r up

-- infix: 60 " // " => updatesRA
-- #eval fromRA <| (toRA ['a','b','c']) // [(2, 'x'), (0, 'y')]

end RAList

-- ## Exercise 3.13

namespace RAList

def unconsT : RAList a → Option (Tree a × RAList a)
| [] => none
| Digit.one t :: xs =>
  if xs.isEmpty then
   some (t, [])
  else
   some (t, Digit.zero :: xs)
| Digit.zero :: xs =>
  match unconsT xs with
  | none => none
  | some (Tree.leaf _, _) => none
  | some (Tree.node _ t1 t2, ys) => some (t1, Digit.one t2 :: ys)

def unconsRA (xs : RAList a) : Option (a × RAList a) :=
 match unconsT xs with
 | some (Tree.leaf x, ys) => some (x, ys)
 | some (Tree.node _ _ _, _) => none
 | none => none


/-
#eval unconsT <| toRA ([] : List Nat)
#eval do
 let a ← unconsRA <| toRA [1,2,3]
 pure (a.1, fromRA a.2)
#eval (unconsRA <| toRA [1,2,3]) >>= (fun x => pure (x.1, fromRA x.2))
-/

def headRA (xs : RAList a) : Option a :=
  Prod.fst <$> unconsRA xs

def tailRA (xs : RAList a) : Option (RAList a) :=
  Prod.snd <$> unconsRA xs

end RAList

-- 3.14

def fa₀ (n : Nat) : Array Nat :=
  Chapter1.scanl (· * ·) 1 (List.range' 1 n) |>.toArray



-- # Exercicio 3.15

/-
ghci> import Data.Array
ghci> listArray (0,5) [0..]
array (0,5) [(0,0),(1,1),(2,2),(3,3),(4,4),(5,5)]
ghci> accum (\ a b -> a + b) (listArray (0,5) [0..10]) [(1,10),(2,10)]
array (0,5) [(0,0),(1,11),(2,12),(3,3),(4,4),(5,5)]
ghci> accum (\ a b -> a + b) (listArray (0,5) [0..10]) [(1,10),(1,30)]
array (0,5) [(0,0),(1,41),(2,2),(3,3),(4,4),(5,5)]
-/

def accum : (e → v → e) → Array e → List (Nat × v) → Array e
 | _, a, []        => a
 | f, a, (p :: ps) =>
   if h : p.1 < a.size then
    let i : Fin a.size := Fin.mk p.1 h
    accum f (a.set i (f a[i] p.2)) ps
   else
    accum f a ps

-- #eval accum (λ a b => a + b) (List.range 5).toArray [(1,10), (1,10), (3,10)]

def accumArray₁ (f : a → v → a) (e : a) (n : Nat) (is : List (Nat × v)) : Array a :=
 accum f (Array.replicate n e) is

-- #eval accumArray₁ (λ a b => a + b) 0 5 [(1,10), (1,10), (3,10)]


end Chapter3
