import Fad.Chapter1
import Fad.«Chapter1-Ex»
import Fad.Chapter3

import Lean.Data
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Interval.Finset.Defs

namespace Chapter5

-- ## Section 5.1 Quicksort

namespace Quicksort

variable {a : Type} [h₁ : LT a] [h₂ : DecidableRel (α := a) (· < ·)]

inductive Tree a where
| null : Tree a
| node : (Tree a) → a → (Tree a) → Tree a

def mkTree: List a → Tree a
| [] => Tree.null
| x :: xs =>
  let p := xs.partition (. < x)
  Tree.node (mkTree p.1) x (mkTree p.2)
 termination_by l => l.length
 decreasing_by
  all_goals simp
   [List.partition_eq_filter_filter, List.length_filter_le]

def Tree.flatten : Tree a → List a
| null => []
| node l x r => l.flatten ++ [x] ++ r.flatten

def qsort₀ : List a → List a :=
 Tree.flatten ∘ mkTree

def qsort₁ : List a → List a
 | []        => []
 | (x :: xs) =>
  let p := xs.partition (· < x)
  (qsort₁ p.1) ++ [x] ++ (qsort₁ p.2)
 termination_by xs => xs.length
 decreasing_by
  all_goals simp
   [List.partition_eq_filter_filter, List.length_filter_le]


def qsort₂ [Ord a] (f : a → a → Ordering) : List a → List a
  | []        => []
  | (x :: xs) =>
    let p := xs.partition (λ z => f z x = Ordering.lt)
    (qsort₂ f p.1) ++ [x] ++ (qsort₂ f p.2)
 termination_by xs => xs.length
 decreasing_by
  all_goals simp
   [List.partition_eq_filter_filter, List.length_filter_le]

/-
#eval qsort₁ (List.iota 145)
#eval qsort₂ (fun a b => Ordering.swap <| compare a b) ['c','a','b']
#eval qsort₂ compare ['c','a','b']
-/

end Quicksort

-- ## Section 5.2 MergeSort

namespace Mergesort

open Chapter1 (wrap unwrap single until')

theorem twoStepInduction {a : Type} {P : List a → Prop} (empty : P [])
  (single : ∀ as, as.length = 1 → P as)
  (more : ∀ a b as, P as → P (a :: b :: as))
  : ∀ as, P as
  | []           => empty
  | [a]          => single [a] (by simp)
  | a :: b :: cs =>
    more _ _ _ (twoStepInduction empty single more _)


variable {a : Type}
  [LE a]
  [DecidableRel (α := a) (· ≤ ·)]
  [Inhabited a]

inductive Tree (a : Type) : Type where
 | null : Tree a
 | leaf : a → Tree a
 | node : Tree a → Tree a → Tree a
 deriving Repr, Inhabited


def merge : List a → List a → List a
 | []       , ys        => ys
 | xs       , []        => xs
 | (x :: xs), (y :: ys) =>
   if x ≤ y then
    x :: merge xs (y :: ys)
   else
    y :: merge (x :: xs) ys


def Tree.flatten : Tree a → List a
 | Tree.null     => []
 | Tree.leaf x   => [x]
 | Tree.node l r => merge l.flatten r.flatten


def halve₀ (xs : List a) : (List a × List a) :=
 let m := xs.length / 2
 (xs.take m,xs.drop m)


def halve : List a → (List a × List a) :=
 let op x p := (p.2, x :: p.1)
 List.foldr op ([],[])



theorem length_halve_fst
 : (halve xs).fst.length = xs.length / 2 := by
 induction xs using twoStepInduction with
 | empty          => simp [halve]
 | single a h     =>
   have b :: [] := a
   simp [halve]
 | more a b cs ih =>
   repeat rw [halve, List.foldr, ←halve]
   simp
   omega


theorem length_halve_snd
 : (halve xs).snd.length = (xs.length + 1) / 2 := by
 induction xs using twoStepInduction with
 | empty          => simp [halve]
 | single a h     =>
   have _ :: [] := a
   simp [halve]
 | more a b cs ih =>
   rw [halve, List.foldr, List.foldr, ←halve]
   simp
   omega


def mkTree₀ : (as : List a) → Tree a
 | []      => Tree.null
 | x :: xs =>
   if h : xs.length = 0 then
    Tree.leaf x
   else
    let p := halve (x :: xs)
    have : (halve <| x :: xs).1.length < xs.length + 1 :=
     by simp [length_halve_fst]; omega
    have : (halve <| x :: xs).2.length < xs.length + 1 :=
     by simp [length_halve_snd]; omega
    Tree.node (mkTree₀ p.1) (mkTree₀ p.2)
 termination_by xs => xs.length


def msort₀ (xs : List a) : List a :=
  (Tree.flatten ∘ mkTree₀) xs


def msort₁ : List a → List a
 | []      => []
 | x :: xs =>
   if h: xs.length = 0 then [x]
   else
    let p := halve (x :: xs)
    have : (halve $ x :: xs).1.length < xs.length + 1 := by
      simp [length_halve_fst]; omega
    have : (halve $ x :: xs).2.length < xs.length + 1 := by
      simp [length_halve_snd]; omega
    merge (msort₁ p.1) (msort₁ p.2)
 termination_by xs => xs.length


def mkPair (n : Nat) (xs : List a) : (Tree a × List a) :=
 if n = 0 then
  (Tree.null, xs)
 else
  if n = 1 then
   (Tree.leaf xs.head!, xs.tail)
  else
   let m := n / 2
   let (t₁, ys) := mkPair m xs
   let (t₂, zs) := mkPair (n - m) ys
   (Tree.node t₁ t₂, zs)
 termination_by (n, xs)


def mkTree₁ (as : List a) : Tree a := mkPair as.length as |>.1

def msort₂ (xs : List a) : List a := (Tree.flatten ∘ mkTree₁) xs

def pairWith (f : a → a → a) : List a → List a
 | []             => []
 | [x]            => [x]
 | (x :: y :: xs) => f x y :: pairWith f xs

def mkTree₂ : List a → Tree a
 | []  => .null
 | as  =>
   unwrap (until' single (pairWith .node) (as.map .leaf))
    |>.getD .null

def msort₃ (xs : List a) : List a :=
  (Tree.flatten ∘ mkTree₂) xs

def msort₄ : List a → List a
 | []   => []
 | as   =>
   unwrap (until' single (pairWith merge) (as.map wrap))
    |>.getD []

def msort₅ : List a → List a
  | []  => []
  | xs  =>
    let op (x : a) : List (List a) → List (List a)
    | []               => [[x]]
    | [] :: yss        => [x] :: yss -- unreachable case
    | (y :: ys) :: yss =>
      if x ≤ y then
        (x :: y :: ys) :: yss
      else
        [x] :: (y :: ys) :: yss
    let runs := List.foldr op []
  unwrap (until' single (pairWith merge) (runs xs)) |>.getD []

end Mergesort


-- ## Section 5.3 Heapsort

namespace Heapsort

variable {a : Type} [LE a] [ToString a]

inductive Tree (a : Type) : Type
 | null : Tree a
 | node : a → Tree a → Tree a → Tree a
 deriving Inhabited

def flatten [DecidableRel (α := a) (· ≤ ·)] : Tree a → List a
| Tree.null       => []
| Tree.node x u v => x :: Mergesort.merge (flatten u) (flatten v)

open Std.Format in

def Tree.toFormat : (t: Tree a) → Std.Format
| .null => Std.Format.text "."
| .node x t₁ t₂ =>
  bracket "(" (f!"{x}" ++
   line ++ nest 2 t₁.toFormat ++ line ++ nest 2 t₂.toFormat) ")"

instance : Repr (Tree a) where
 reprPrec e _ := Tree.toFormat e

end Heapsort


-- ## Section 5.4 Bucketsort and Radixsort

namespace Bucketsort

variable {α : Type}
variable {β : Type} [BEq β] [LT β] [DecidableRel (α := β) (· < ·)]

def ordered : List (α → β) → α → α → Bool
 | []       , _, _ => true
 | (d :: ds), x, y => (d x < d y) || ((d x == d y) && (ordered ds x y))

-- #eval ordered [(·.toList[0]!),(·.toList[1]!)] "ba" "ab"

inductive Tree (α : Type)
| leaf : α → Tree α
| node : List (Tree α) → Tree α
deriving Repr


def Tree.flatten (r : Tree (List α)) : List α :=
 match r with
 | .leaf v  => v
 | .node ts =>
   List.flatten <| ts.map flatten

def ptn₀ (rng : List β) (f : α → β) (xs : List α) : List (List α) :=
  rng.map (λ m => xs.filter (λ x => f x == m))

def mkTree (rng : List β) (ds : List (α → β)) (xs : List α) : Tree (List α) :=
  match ds with
  | []       => .leaf xs
  | d :: ds' =>
    .node ((ptn₀ rng d xs).map (mkTree rng ds'))

def bsort₀ (rng : List β) (ds : List (α → β)) (xs : List α) : List α :=
  Tree.flatten (mkTree rng ds xs)

def bsort₁ (rng : List β) : List (α → β) → List α → List α
| []     , xs => xs
| d :: ds, xs => Chapter1.concatMap (bsort₁ rng ds) (ptn₀ rng d xs)


def rsort₀ (rng : List β) : List (α → β) → List α → List α
| []     , xs => xs
| d :: ds, xs => List.flatten (ptn₀ rng d (rsort₀ rng ds xs))


/-
#eval rsort₀ "abc".toList [(·.toList[0]!),(·.toList[1]!)]
  ["ba", "ab", "aab", "bba","abb"]
-/

def ptn₁ {a b : Type} (bnds : b × b) [Chapter3.Ix b] [BEq b]
 (d : a → b) (xs : List a) : List (List a) :=
 let snoc xs x := xs ++ [x]
 let xa := Chapter3.accumArray snoc [] bnds ((xs.map d).zip xs)
 Chapter3.elems bnds default xa

/-
#eval ptn₁ ('a','z') (·.toList[0]!)
  ["ba", "ab", "aab", "bba","abb"]
-/

/- mathlib classes to be explored
instance : BoundedOrder Char where
  top := ⟨1114111, by decide⟩
  bot := ⟨0, by decide⟩
  le_top x := x.valid.by_cases
    (fun h => (h.trans (by decide)).le)
    (fun h => Nat.le_of_lt_add_one h.right)
  bot_le x := Nat.zero_le x.val.toNat

#eval (Finset.Icc ⊥ ⊤ : Finset Char)
-/

end Bucketsort


-- ## Section 5.5 Sorting sums

namespace SortingSums

open Quicksort (qsort₂)
open Mergesort (merge)

variable {a : Type} [Ord a] [Add a]
 [Sub a] [Neg a] [OfNat a 0] [LE a]
 [DecidableRel (· ≤ · : a → a → Prop)]

def sortsums₀ (xs ys : List a) : List a :=
  qsort₂ compare (xs.flatMap (fun x => ys.map fun y => x + y))

abbrev Label := Nat
abbrev Pair := Label × Label

def subs (xs ys : List (a × Label)) : List (a × Pair) :=
  xs.flatMap (fun (x, i) =>
   ys.map (fun (y, j) => (x - y, (i, j))))

def switch : a × Pair → a × Pair
| (x, (i, j)) => (-x, (j, i))

instance : Ord (a × Pair) where
  compare p q :=
    compare p.1 q.1

def sortWith (abs : List (a × Pair)) (xis yis : List (a × Label))
  : List (a × Pair) :=
  let a := Std.HashMap.ofList (qsort₂ compare abs |>.map Prod.snd |>.zipIdx)
  let cmp p₁ p₂ :=
    let (_,(i,k)) := p₁
    let (_,(j,l)) := p₂
    compare a[(i,j)]! a[(k,l)]!
  qsort₂ cmp (subs xis yis)

def sortsubs₁ : List (a × Label) → Nat → List (a × Pair)
  | []     , _        => []
  | [(_,i)], _        => [(0, (i, i))]
  | _      , 0        => panic! "never here"
  | xis    , fuel + 1 =>
    let mid := xis.length / 2
    let (xis1, xis2) := xis.splitAt mid
    let abs := merge (sortsubs₁ xis1 fuel) (sortsubs₁ xis2 fuel)
    let cs := sortWith abs xis1 xis2
    let ds := cs.map switch |>.reverse
    merge abs (merge cs ds)

def sortsubs (xs ys : List a) : List a :=
 let   n := xs.length
 let xis := xs.zipIdx
 let yis := ys.zipIdx n
 let abs := merge (sortsubs₁ xis xis.length) (sortsubs₁ yis yis.length)
 sortWith abs xis yis |>.map Prod.fst

def sortsums₁ (xs ys : List a) : List a :=
  sortsubs xs (ys.map Neg.neg)


end SortingSums


end Chapter5
