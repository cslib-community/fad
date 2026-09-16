import Fad.Chapter1

namespace Chapter4

/- # Section 4.1: a one-dimensional search problem -/

namespace D1

def search₀ (f : Nat → Nat) (t : Nat) : List Nat :=
 (List.range $ t + 1).filter (t = f ·)

-- #eval search₀ (fun _ => 3) 3

def search₁ (f : Nat → Nat) (t : Nat) : List Nat :=
  seek (0, t)
 where
  seek : (Nat × Nat) → List Nat
  | (a, b) => List.range' a (b - a + 1) |>.filter (t = f ·)


def search₂ (f : Nat → Nat) (t : Nat) : List Nat :=
 let rec seek (a b : Nat) : List Nat :=
  let m := (a + b) / 2
  let v := f m
  if      h₁ : a = b then
   if t = v then [m] else []
  else if h₉ : a > b then []
  else if h₂ : t = v then [m]
  else if h₃ : t < v then
    seek a (m - 1)
  else
    seek (m + 1) b
 termination_by (b - a) -- see https://tinyurl.com/57szywn5
 seek 0 t

-- #eval search₂ (λ a => dbg_trace "f {a}"; a * a) 1024

def bound (f : Nat → Nat) (t : Nat) : (Nat × Nat) :=
  if t ≤ f 0 then (0, 0) else (b / 2, b)
 where
  b := Chapter1.until' done (· * 2) 1
  done b := t ≤ f b

-- #eval bound (fun x => dbg_trace "fun {x}"; x + 10) 10

def smallest (f : Nat → Nat) (t : Nat) (p : Nat × Nat) : Nat :=
 match p with
 | (a, b) =>
   let m := (a + b) / 2
   let v := f m
   if      h₀ : a = b then b
   else if h₁ : a > b then b
   else if h₃ : t = v then m
   else if h₂ : t < v then
    smallest f t (a, m)
   else
    smallest f t (m + 1, b)
 termination_by (p.2 - p.1)

def search₃ (f : Nat → Nat) (t : Nat) : List Nat :=
  if f x = t then [x] else []
 where
  x := smallest f t (bound f t)

/-
#eval search₁ (fun x => dbg_trace "fun {x}"; x * x) 1024
#eval search₂ (fun x => dbg_trace "fun {x}"; x * x) 1048576
#eval search₃ (fun x => dbg_trace "fun {x}"; x ^ 3) 175616
-/

end D1


/- # Section 4.2 A two-dimensional search problem -/

namespace D2

def search₀ (f : (Nat × Nat) → Nat) (t : Nat) : List (Nat × Nat) :=
 ps.filter (λ p => t = f p)
 where
  as := (List.range $ t + 1)
  ps := Chapter1.concatMap (λ x => as.map (λ y => (x, y))) as

-- #eval search₀ (λ p => dbg_trace "fun {p}"; p.1 + p.2) 5

/- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/.E2.9C.94.20proof.20termination -/

def search₁ (f : Nat × Nat → Nat) (t : Nat) : List (Nat × Nat) :=
  searchIn 0 t []
where
  searchIn (x y : Nat) (sofar : List (Nat × Nat)) : List (Nat × Nat) :=
    let z := f (x, y)
    if x > t then sofar
    else if z < t then
      searchIn (x + 1) y sofar
    else if z = t then
      match y with
      | 0 => (x,y) :: sofar
      | y' + 1 => searchIn (x + 1) y ((x, y) :: sofar)
    else
      match y with
      | 0 => sofar
      | y + 1 => searchIn x y sofar
  termination_by (t + 1 - x, y)

-- #eval search₁ (λ (x, y) => dbg_trace "fun {x} {y}"; x + y) 5
-- #eval search₁ (λ (x, y) => dbg_trace "fun {x} {y}"; x^2 + 3^y) 12
-- #eval search₁ (λ (x, y) => x^2 + 3^y) 2223
-- #eval search₁ (λ (x, y) => x^2 + 3^y) 20259


-- BUG #eval helper 12 (λ (x, y) => x^2 + 3^y) (0, 12) (12,0)

partial def helper (t : Nat) (f : Nat × Nat → Nat)
 : (Nat × Nat) → (Nat × Nat) → List (Nat × Nat)
 | (x₁, y₁), (x₂, y₂) =>
  let c := (x₁ + x₂) / 2
  let r := (y₁ + y₂) / 2
  let x := D1.smallest (λ x => f (x,r)) t (x₁ - 1, x₂)
  let y := D1.smallest (λ y => f (c,y)) t (y₂ - 1, y₁)
  if x₂ < x₁ ∨ y₁ < y₂ then
   []
  else
   if y₁ - y₂ ≤ x₂ - x₁ then
    let z := f (x,r)
    if z < t then
     helper t f (x₁, y₁) (x₂, r + 1)
    else if z = t then
     (x, r) :: helper t f (x₁, y₁) (x - 1, r + 1) ++ helper t f (x + 1, r - 1) (x₂, y₂)
    else
     helper t f  (x₁, y₁) (x - 1, r + 1) ++ helper t f (x, r - 1) (x₂, y₂)
   else
    let z := f (c, y)
    if z < t then
     helper t f (c + 1, y₁) (x₂, y₂)
    else if z = t then
     (c, y) :: helper t f (x₁, y₁) (c - 1, y + 1) ++ helper t f (c + 1, y - 1) (x₂, y₂)
    else
     helper t f (x₁, y₁) (c - 1, y) ++ helper t f (c + 1, y - 1) (x₂, y₂)

partial def search₂ (f : Nat × Nat → Nat) (t : Nat) : List (Nat × Nat) :=
 let p := D1.smallest (λ y => f (0, y)) t (0, t)
 let q := D1.smallest (λ x => f (x, 0)) t (0, t)
 helper t f (0, p) (q, 0)


/- https://kmill.github.io/informalization/ucsc_cse_talk.pdf -/

def scale (a : Array Int) (c : Int) : Array Int := Id.run do
  let mut b : Array Int := #[]
  for h: i in [0:a.size] do
   b := b.push (c * a[i])
  return b

-- #eval scale #[1,2,3,4] 4
-- #eval for i in [0:12] do println! i

def myhead₁ (xs : List a) (h : xs.length ≠ 0) : a :=
 match xs with
 | [] => absurd rfl h
 | x :: _ => x

def myhead₂ (xs : List a) (h : xs.length ≠ 0) : a :=
 match xs, h with
 | x :: _, _ => x

end D2


/- # Section 4.3 Binary search trees -/

namespace BST1

variable {α : Type}

inductive Tree (α : Type) : Type
| null : Tree α
| node : (Tree α) → α → (Tree α) → Tree α
deriving Inhabited

open Std.Format in

def Tree.toFormat [ToString α] : (t : Tree α) → Std.Format
| .null => Std.Format.text "."
| .node t₁ x t₂ =>
  bracket "(" (f!"{x}" ++
   line ++ nest 2 t₁.toFormat ++ line ++ nest 2 t₂.toFormat) ")"

instance [ToString α] : Repr (Tree α) where
 reprPrec e _ := e.toFormat

def Tree.size : Tree α → Nat
| null => 0
| node t₁ _ t₂ => 1 + t₁.size + t₂.size

def Tree.flatten : Tree α → List α
| null => []
| node l x r => l.flatten ++ [x] ++ r.flatten

def search (f : Nat → Nat) : Nat → Tree Nat → Option Nat
| _, Tree.null       => none
| k, Tree.node l x r =>
  if f x < k then
   search f k r
  else
   if f x = k then
    some x
   else
    search f k l

def Tree.height : Tree α → Nat
| null => 0
| node l _ r => 1 + (max l.height r.height)


def mkTree [LT α] [DecidableRel (α := α) (· < ·)]
: List α → Tree α
| [] => Tree.null
| x :: xs =>
  let p := xs.partition (· < x)
  Tree.node (mkTree p.1) x (mkTree p.2)
 termination_by l => l.length
 decreasing_by
  all_goals
   simp [List.partition_eq_filter_filter]
   apply Nat.le_iff_lt_add_one.mp
   apply List.length_filter_le

end BST1


namespace BST2

variable {a : Type} [LT a] [DecidableRel (α := a) (· < ·)]

inductive Tree (a : Type) : Type
| null : Tree a
| node : Nat → (Tree a) → a → (Tree a) → Tree a
deriving Nonempty, Inhabited

open Std.Format in

def Tree.toFormat [ToString a] : (t : Tree a) → Std.Format
| .null => Std.Format.text "."
| .node _ t₁ x t₂ =>
  bracket "(" (f!"{x}" ++
   line ++ nest 2 t₁.toFormat ++ line ++ nest 2 t₂.toFormat) ")"

instance [ToString a] : Repr (Tree a) where
 reprPrec e _ := e.toFormat


def Tree.height : Tree a → Nat
 | .null => 0
 | .node x _ _ _ => x

def Tree.flatten : Tree a → List a
| null => []
| node _ l x r => l.flatten ++ [x] ++ r.flatten

def node (l : Tree a) (x : a) (r : Tree a): Tree a :=
  Tree.node h l x r
 where h := 1 + (max l.height r.height)

def bias : Tree a → Int
 | .null => 0
 | .node _ l _ r => l.height - r.height

def rotr : Tree a → Tree a
| .null => .null
| .node _ (.node _ ll y rl) x r => node ll y (node rl x r)
| .node _ .null _ _ => .null

def rotl : Tree a → Tree a
| .null => .null
| .node _ ll y (.node _ lrl z rrl) => node (node ll y lrl) z rrl
| .node _ _ _ .null => .null

def balance (t1 : Tree a)  (x : a)  (t2 : Tree a) : Tree a :=
 if Int.natAbs (h1 - h2) ≤ 1 then
   node t1 x t2
 else if h1 = h2 + 2 then
   rotateR t1 x t2
 else if h2 = h1 + 2 then
   rotateL t1 x t2
 else
   panic! "balance: impossible case"
 where
  h1 := t1.height
  h2 := t2.height
  rotateR t1 x t2 :=
   if 0 <= bias t1 then
    rotr (node t1 x t2)
   else rotr (node (rotl t1) x t2)
  rotateL t1 x t2 :=
   if bias t2 <= 0 then
    rotl (node t1 x t2)
   else rotl (node t1 x (rotr t2))


def insert : (x : a) -> Tree a -> Tree a
 | x, .null => node .null x .null
 | x, .node h l y r =>
   if x < y then balance (insert x l) y r else
   if x > y then balance l y (insert x r) else .node h l y r

def mkTree : (xs : List a) → Tree a :=
 List.foldr insert (.null : Tree a)


def balanceR (t₁ : Tree a) (x : a) (t₂ : Tree a) : Tree a :=
 match t₁ with
 | Tree.null => Tree.null
 | Tree.node _ l y r =>
   if r.height ≥ t₂.height + 2
   then balance l y (balanceR r x t₂)
   else balance l y (node r x t₂)

def balanceL (t₁ : Tree a) (x : a) (t₂ : Tree a) : Tree a :=
 match t₂ with
 | Tree.null => Tree.null
 | Tree.node _ l y r =>
   if l.height ≥ t₁.height + 2 then
     balance (balanceL t₁ x l) y r
   else
     balance (node t₁ x l) y r

def gbalance (t₁ : Tree a) (x : a) (t₂ : Tree a) : Tree a :=
 let h1 := t₁.height
 let h2 := t₂.height
 if Int.natAbs (h1 - h2) ≤ 2 then
   balance t₁ x t₂
 else if h1 > h2 then
   balanceR t₁ x t₂
 else
   balanceL t₁ x t₂

def insert₁ : (x : a) -> Tree a -> Tree a
 | x, .null => node .null x .null
 | x, .node h l y r =>
   if x < y then gbalance (insert₁ x l) y r else
   if x > y then gbalance l y (insert₁ x r) else .node h l y r

def mkTree₁ : List a → Tree a :=
  List.foldr insert₁ Tree.null

def insert₂ {b : Type} [Ord b] (key: a → b)
 : (x : a) -> Tree a -> Tree a
 | x, .null         => node .null x .null
 | x, .node h l y r =>
     match compare (key x) (key y) with
   | .lt => gbalance (insert₂ key x l) y r
   | .gt => gbalance l y (insert₂ key x r)
   | .eq => .node h l y r

def mkTree₂ {b : Type} [Ord b] (key: a → b)
  : List a → Tree a :=
  List.foldr (insert₂ key) Tree.null


/- how to deal with list with duplicated elements -/

instance : Ord (Nat × Nat) where
  compare a b :=
   match compare a.1 b.1 with
   | .eq => compare a.2 b.2
   | x   => x

/-
#eval
  (λ xs => mkTree₂ id xs.zipIdx |> Tree.flatten |>.map (·.1))
  [1,3,2,1,2]
-/

def sort : List a → List a :=
  Tree.flatten ∘ mkTree₁

def search {b : Type} [Ord b] (key : a → b) (k : b)
 : Tree a → Option a
 | Tree.null         => none
 | Tree.node _ l x r =>
   match compare (key x) k with
   | .lt => search key k r
   | .gt => search key k l
   | .eq => some x


end BST2

namespace DSet
open BST2 (Tree insert node balance gbalance mkTree)

abbrev Set a := BST2.Tree a

def member {a : Type} [LT a] [DecidableRel (α := a) (· < ·)] (x : a) : Set a → Bool
| .null => false
| .node _ l y r =>
  if x < y      then member x l
  else if x > y then member x r
  else true

inductive Piece (α : Type) : Type
| lp : Set α → α → Piece α
| rp : α → Set α → Piece α

@[simp]
theorem flatten_left_lt  {α : Type}
    {t : BST2.Tree α} {h : Nat} {l r : BST2.Tree α} {x : α}
    (ht : t = BST2.Tree.node h l x r) :
    (Tree.flatten t).length > (Tree.flatten l).length := by
  subst ht
  have :
    (Tree.flatten (BST2.Tree.node h l x r)).length = (Tree.flatten l).length + 1 + (Tree.flatten r).length := by
    simp [Tree.flatten, List.length_append, List.length_cons]
    omega
  simp
  omega

def deleteMin {α : Type} (t  : Set α) (ht : t ≠ .null) :
  α × Set α := by
  cases hEq : t with
  | null =>
      contradiction
  | node h l x r =>
      cases l with
      | null =>
          exact (x, r)
      | node hₗ lₗ yₗ rₗ =>
          let (y, l') := deleteMin (.node hₗ lₗ yₗ rₗ) (by intro h; cases h)
          exact (y, balance l' x r)
termination_by t.flatten.length
decreasing_by exact flatten_left_lt hEq

def combine {a : Type} [LT a] [DecidableRel (α := a) (· < ·)] :
    Set a → Set a → Set a
| .null, r => r
| l, .null => l
| l, r =>
  match h : r with
  | .null => l -- nunca vai chegar nesse caso
  | .node a b c d =>
    let (x, t) := deleteMin r (by rw [h]; intro H; cases H)
    balance l x t

def delete {a : Type} [LT a] [DecidableRel (α := a) (· < ·)] [DecidableEq a] :
    a → Set a → Set a
| _, .null => .null
| x, .node _ l y r =>
  if x < y then
    balance (delete x l) y r
  else if x > y then
    balance l y (delete x r)
  else
    combine l r

open Piece

def pieces {α : Type} [LT α] [DecidableRel (α := α) (· < ·)] :
    α → Set α → List (Piece α)
| x, t =>
  let rec addPiece : Set α → List (Piece α) → List (Piece α)
  | .null, ps => ps
  | .node _ l y r, ps =>
    if x < y then
      addPiece l (rp y r :: ps)
    else
      addPiece r (lp l y :: ps)
  addPiece t []


def sew {α : Type} : List (Piece α) → Set α × Set α :=
  List.foldl step (.null, .null)
where
  step : Set α × Set α → Piece α → Set α × Set α
  | (t1, t2), lp t x => (gbalance t x t1, t2)
  | (t1, t2), rp x t => (t1, gbalance t2 x t)


def split {α : Type} [LT α] [DecidableRel (α := α) (· < ·)] :
    α → Set α → Set α × Set α :=
  fun x t => sew (pieces x t)


-- #eval pieces 10 (BST2.mkTree <| List.range 123213) |>.length

end DSet

end Chapter4
