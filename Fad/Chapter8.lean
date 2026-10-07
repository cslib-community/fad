import Fad.Chapter1
import Fad.«Chapter1-Ex»
import Fad.Chapter3
import Fad.Chapter5
import Fad.Chapter6
import Fad.Chapter7

namespace Chapter8

namespace S1

/- 8.1 Minimum-height trees -/

open Chapter5.Mergesort (halve length_halve_fst length_halve_snd pairWith)
open Chapter1 (wrap unwrap single until' concatMap)
open Chapter6 (foldl1)
open Chapter7 (minWith)

inductive Tree (α : Type) : Type where
 | leaf : α → Tree α
 | node : Tree α → Tree α → Tree α
 deriving Repr, Inhabited


def Tree.size {α : Type} : Tree α → Nat
 | Tree.leaf _ => 1
 | Tree.node t₁ t₂ => t₁.size + t₂.size


def Tree.height {α : Type} : Tree α → Nat
 | Tree.leaf _ => 0
 | Tree.node t₁ t₂ => Nat.max t₁.height t₂.height + 1


def Tree.fringe {α : Type} : Tree α → List α
 | Tree.leaf x => [x]
 | Tree.node t₁ t₂ => t₁.fringe ++ t₂.fringe


def mkTree {a : Type} [Inhabited a] : (as : List a) → Tree a
 | []      => .leaf default
 | x :: xs =>
   if h : xs.length = 0 then
    .leaf x
   else
    let p := halve (x :: xs)
    have : (halve (x :: xs)).1.length < xs.length + 1 :=
     by simp [length_halve_fst]; omega
    have : (halve (x :: xs)).2.length < xs.length + 1 :=
     by simp [length_halve_snd]; omega
    .node (mkTree p.1) (mkTree p.2)
 termination_by xs => xs.length

def mkTree₁ {a : Type} [Inhabited a] : List a → Tree a
 | [] => .leaf default
 | xs =>
   unwrap (until' single (pairWith .node) (xs.map .leaf)) |>.getD default


def cost : Tree Nat → Nat
 | Tree.leaf x     => x
 | Tree.node t₁ t₂ => 1 + Nat.max (cost t₁) (cost t₂)


def extend {a : Type} (x : a) : Tree a → List (Tree a)
 | Tree.leaf y     => [.node (.leaf x) (.leaf y)]
 | Tree.node t₁ t₂ =>
   [.node (.leaf x) (.node t₁ t₂)] ++ (extend x t₁).map (.node · t₂)


def mkTrees {a : Type} [Inhabited a] : List a → List (Tree a)
 | []      => []
 | [x]     => [Tree.leaf x]
 | x :: xs => concatMap (extend x) (mkTrees xs)


/- this should be defined only for nonempty lists -/
def foldrn {α β : Type} [Inhabited β] (f : α → β → β) (g : α → β) : List α → β
 | []      => default
 | [x]     => g x
 | x :: xs => f x (foldrn f g xs)

def mkTrees₁ {a : Type} [Inhabited a] : List a → List (Tree a) :=
 foldrn (concatMap ∘ extend) (wrap ∘ .leaf)


abbrev Forest (a : Type) := List (Tree a)


def rollup [Inhabited (Tree a)] : List (Tree a) → Tree a :=
  Chapter6.foldl1 .node

def spine {a : Type} : Tree a → List (Tree a)
 | .leaf x   => [.leaf x]
 | .node u v => spine u ++ [v]

theorem spine_foldl {a : Type} (ts : List (Tree a)) :
    ∀ s : Tree a, spine (List.foldl .node s ts) = spine s ++ ts := by
  induction ts with
  | nil =>
    intro s
    simp
  | cons t ts ih =>
    intro s
    simp [List.foldl, ih, spine]

example [Inhabited a] (ts : List (Tree a)) :
 spine (rollup ([Tree.leaf x] ++ ts)) = [Tree.leaf x] ++ ts := by
  induction ts with
  | nil =>
    simp [rollup, foldl1, spine]
  | cons t ts ih =>
    simp [rollup, foldl1, List.foldl]
    simp [rollup, foldl1] at ih
    simp [spine_foldl, spine]

def extend₁ {a : Type} [Inhabited a] (x : a) (ts : Forest a) : List (Forest a) :=
  (List.range' 1 ts.length).map
    (λ i => .leaf x :: rollup (ts.take i) :: ts.drop i)

def mkForests {a : Type} [Inhabited a] : List a → List (Forest a) :=
 foldrn (concatMap ∘ extend₁) (wrap ∘ wrap ∘ .leaf)

def mkTrees₂ {a : Type} [Inhabited a] : List a → List (Tree a) :=
 List.map rollup ∘ mkForests


def mct₀ : List Nat → Tree Nat :=
 minWith cost ∘ mkTrees₂


def scanl1 (f : a → a → a) : List a → List a
 | x :: xs => Chapter1.scanl f x xs
 | []      => []

def lcost : Tree Nat → List Nat :=
  let op (x y : Nat) : Nat := 1 + Nat.max x y
  List.reverse ∘ scanl1 op ∘ List.map cost ∘ spine


def add (x : Nat) (ts : List (Tree Nat)) : List (Tree Nat) :=
  let rec join (x : Nat) : List (Tree Nat) → List (Tree Nat)
   | [u] => [u]
   | []  => []  -- not used
   | (u :: v :: ts) =>
     if Nat.max x (cost u) < cost v then
       u :: v :: ts
     else
       join x (Tree.node u v :: ts)
  termination_by ts => ts.length
  (Tree.leaf x) :: join x ts

def mct₁ : List Nat → Tree Nat :=
 let gstep (x : Nat) : Tree Nat → Tree Nat :=
  rollup ∘ add x ∘ spine
 foldrn gstep .leaf


abbrev Pair := (Tree Nat × Nat)

def node : Pair → Pair → Pair
 | (u, c), (v, d) => (Tree.node u v, 1 + Nat.max c d)

def leaf : Nat → Pair
 | x => (Tree.leaf x, x)

def join (x : Nat) : List Pair → List Pair
 | [u] => [u]
 | []  => [] -- not used
 | u :: v :: ts =>
   if Nat.max x u.snd < v.snd then
     u :: v :: ts
   else
     join x (node u v :: ts)
 termination_by ts => ts.length

def mct : List Nat → Tree Nat :=
 let hstep (x : Nat) (ts : List Pair) : List Pair :=
  leaf x :: join x ts
 rollup ∘ List.map Prod.fst ∘ foldrn hstep (wrap ∘ leaf)

end S1


/- 8.2 Huffman coding trees -/

namespace S2

open S1 (Tree Forest)
open Chapter1 (concatMap wrap unwrap unwrap! single until' single picks apply)
open Chapter3.SymList (nil singleSL headSL headSL! snocSL isEmpty tailSL)


def depths : S1.Tree a → List Nat :=
 let rec frm (n : Nat) : S1.Tree a → List Nat
  | .leaf _   => [n]
  | .node u v => frm (n + 1) u ++ frm (n + 1) v
 frm 0

abbrev Weight := Nat
abbrev Elem   := Char × Weight
abbrev Cost   := Nat

def cost (t : S1.Tree Elem) : Cost :=
 let t := t.fringe.zip (depths t)
 List.sum $ t.map (λ (c, d) => d * c.snd)

def weight : S1.Tree Elem → Nat
 | .leaf (_, w) => w
 | .node u v    => weight u + weight v

def cost₁ : S1.Tree Elem → Cost
 | .leaf _   => 0
 | .node u v => cost u + cost v + weight u + weight v

def pairs (xs : List α) : List ((α × α) × List α) :=
  (picks xs).flatMap
    fun (x, ys) =>
     (picks ys).map
      fun (y, zs) => ((x, y), zs)

/- Exercise 8.11 -/
def insert (t₁ : S1.Tree Elem) : Forest Elem → Forest Elem
 | [] => [t₁]
 | t₂ :: ts =>
   if weight t₁ ≤ weight t₂ then
     t₁ :: t₂ :: ts
   else
     t₂ :: insert t₁ ts

def combine (ts : Forest Elem) : List (Forest Elem) :=
  (pairs ts).map fun (p, us) =>
    insert (S1.Tree.node p.1 p.2) us

def mkForests : List (S1.Tree Elem) → List (Forest Elem) :=
 until' (flip List.all single) (concatMap combine) ∘ wrap

def mkTrees : List Elem → List (S1.Tree Elem) :=
 List.map unwrap! ∘ mkForests ∘ List.map Tree.leaf

def mkForests₁ (ts : List (S1.Tree Elem)) : List (Forest Elem) :=
 apply (ts.length - 1) (concatMap combine) [ts]

def mkTrees₁ : List Elem → List (S1.Tree Elem) :=
 List.map unwrap! ∘ mkForests₁ ∘ List.map Tree.leaf


/- quadractic version -/

def huffman₁ (es : List Elem) : S1.Tree Elem :=
 let gstep : Forest Elem → Forest Elem
  | t₁ :: t₂ :: ts => insert (S1.Tree.node t₁ t₂) ts
  | []             => dbg_trace "error"; []       -- not used
  | t₁ :: ts       => dbg_trace "error"; t₁ :: ts -- not used
 unwrap! (until' single gstep (List.map Tree.leaf es))

-- #eval huffman₁ [('a', 2), ('b', 3), ('c', 1), ('d', 20)]

/- linear time version -/

abbrev Queue (α : Type) := Chapter3.SymList α
abbrev Stack (α : Type) := List α
abbrev SQ (α : Type)    := Stack α × Queue α
abbrev Pair             := S1.Tree Elem × Weight

def leaf : Elem → Pair
 | (c, w) => (Tree.leaf (c, w), w)

def node : Pair → Pair → Pair
 | (t₁, w₁), (t₂, w₂) => (S1.Tree.node t₁ t₂, w₁ + w₂)

def makeSQ (xs : List Pair) : SQ Pair :=
  (xs, nil)

def singleSQ (sq : SQ a) : Bool :=
  sq.1.isEmpty ∧ singleSL sq.2

def extractSQ (sq : SQ Pair) : S1.Tree Elem :=
  (headSL! sq.2).1


def extractMin (ps : SQ Pair) : Pair × SQ Pair :=
  let (xs, ys) := ps
  if isEmpty ys then
   (xs.head!, (xs.tail, ys))
  else if xs.isEmpty then
   (headSL! ys, (xs, tailSL ys))
  else
   let x := xs.head!
   let y := headSL! ys
   if x.snd ≤ y.snd then
    (x, (xs.tail, ys))
   else
    (y, (xs, tailSL ys))

def gstep (ps : SQ Pair) : SQ Pair :=
  let add : Pair → SQ Pair → SQ Pair
   | y, (xs, ys) => (xs, snocSL y ys)
  let (p₁, qs) := extractMin ps
  let (p₂, rs) := extractMin qs
  add (node p₁ p₂) rs

def huffman : List Elem → S1.Tree Elem :=
 extractSQ ∘ until' singleSQ gstep ∘ makeSQ ∘ List.map leaf

-- #eval huffman [('a', 2), ('b', 3), ('c', 1), ('d', 20)]

end S2

namespace PriorityQueue
-- β precisa ser ordenável para sabermos determinar a prioridade
variable {α β : Type} [LE β] [DecidableRel (α := β) (· ≤ ·)]

abbrev Rank := Nat -- Chamando de rank para ficar parecido com o livro

inductive PQ (α : Type) (β : Type) : Type where
  | null : PQ α β
  | fork : Rank → α → β → PQ α β → PQ α β → PQ α β
  deriving Repr, Inhabited

def mergeOnSnd : List (α × β) → List (α × β) → List (α × β)
  | [], ys => ys
  | xs, [] => xs
  | (x, p) :: xs, (y, q) :: ys =>
    if p ≤ q then
      (x, p) :: mergeOnSnd xs ((y, q) :: ys)
    else
      (y, q) :: mergeOnSnd ((x, p) :: xs) ys

def toListQ : PQ α β → List (α × β)
  | .null => []
  | .fork _ x p t₁ t₂ =>
    (x, p) :: mergeOnSnd (toListQ t₁) (toListQ t₂)

def rank : PQ α β → Rank
  | .null => 0
  | .fork r _ _ _ _ => r

def fork (x : α) (p : β) (t₁ t₂ : PQ α β) : PQ α β :=
  let r₁ := rank t₁
  let r₂ := rank t₂
  if r₂ ≤ r₁ then
    .fork (r₂ + 1) x p t₁ t₂
  else
    .fork (r₁ + 1) x p t₂ t₁

def combineQ : PQ α β → PQ α β → PQ α β
  | .null, t => t
  | t, .null => t
  | .fork k₁ x₁ p₁ l₁ r₁, .fork k₂ x₂ p₂ l₂ r₂ =>
    if p₁ ≤ p₂ then
      fork x₁ p₁ l₁ (combineQ r₁ (.fork k₂ x₂ p₂ l₂ r₂))
    else
      fork x₂ p₂ l₂ (combineQ (.fork k₁ x₁ p₁ l₁ r₁) r₂)

def insertQ (x : α) (p : β) (t : PQ α β) : PQ α β :=
  combineQ (fork x p .null .null) t


def deleteQ (q : PQ α β) (h : q ≠ PQ.null) : (α × β) × PQ α β :=
  match q with
  | .null => by contradiction
  | .fork _ x p t₁ t₂ => ((x, p), combineQ t₁ t₂)

/-
Tive que usar essa versão de deleteQ no algoritmo de Huffman,
pois não consegui fazer a prova de que o gstep recebe uma fila não nula.
-/
def deleteQ? (q : PQ α β) : Option ((α × β) × PQ α β) :=
  match q with
  | .null => none
  | .fork _ x p t₁ t₂ => some (((x, p), combineQ t₁ t₂))

/- Funções necessárias para o algoritmo de Huffman -/
def emptyQ : PQ α β := .null

def nullQ : PQ α β → Bool
  | .null => true
  | _ => false

def addListQ (xs : List (α × β)) (q : PQ α β) : PQ α β :=
  xs.foldl (λ acc (x, p) => insertQ x p acc) q

def makeQ (xs : List (α × β)) : PQ α β :=
  addListQ xs emptyQ

def singleQ (q : PQ α β) : Bool :=
  match deleteQ? q with
  | none => true
  | some (_, remaining) => nullQ remaining

def leaf (x : α) (p : β) : PQ α β :=
  fork x p .null .null

def extract (q : PQ α β) : Option α :=
  match deleteQ? q with
  | none => none
  | some ((x, _), _) => some x

def node : (S1.Tree S2.Elem × S2.Weight) → (S1.Tree S2.Elem × S2.Weight) → (S1.Tree S2.Elem × S2.Weight)
  | (t₁, w₁), (t₂, w₂) => (S1.Tree.node t₁ t₂, w₁ + w₂)

def gstep (ps : PQ (S1.Tree S2.Elem) S2.Weight) : PQ (S1.Tree S2.Elem) S2.Weight :=
  match deleteQ? ps with
  | none => .null
  | some (p₁, qs) =>
    match deleteQ? qs with
    | none => .null
    | some (p₂, rs) =>
      let (t, w) := node p₁ p₂
      insertQ t w rs

/- O algoritmo de Huffman usando priority queues -/
def huffmanPQ (es : List S2.Elem) : Option (S1.Tree S2.Elem) :=
  let q := makeQ (es.map S2.leaf)
  extract (Chapter1.until' singleQ gstep q)

/- Exemplos -/
def pqInsert1 : PQ Nat Nat := insertQ 5 3 emptyQ
def pqInsert2 : PQ Nat Nat := insertQ 2 1 pqInsert1
def pqInsert3 : PQ Nat Nat := insertQ 8 4 pqInsert2

/-
#eval toListQ pqInsert1  -- [(5, 3)]
#eval toListQ pqInsert2  -- [(2, 1), (5, 3)]
#eval toListQ pqInsert3  -- [(2, 1), (5, 3), (8, 4)]
-/

/-
#eval deleteQ? pqInsert3  -- some ((2, 1), remaining queue)
#eval deleteQ? (emptyQ : PQ Nat Nat)     -- none (fila vazia)
-/

def pqAfterDelete1 := match deleteQ? pqInsert3 with | some (_, q) => q | none => emptyQ
def pqAfterDelete2 := match deleteQ? pqAfterDelete1 with | some (_, q) => q | none => emptyQ

/-
#eval toListQ pqAfterDelete1
#eval toListQ pqAfterDelete2
-/

def pqMake1 : PQ Nat Nat := makeQ [(5, 3), (2, 1), (8, 4)]
def pqMake2 : PQ String Nat := makeQ [("baixa", 5), ("urgente", 1), ("normal", 3)]

/-
#eval toListQ pqMake1
#eval toListQ pqMake2

#eval singleQ (emptyQ : PQ Nat Nat)
#eval singleQ pqInsert1
#eval singleQ pqInsert2

#eval extract (emptyQ : PQ Nat Nat)
#eval extract pqInsert1
#eval extract pqInsert2
-/

def initialQueue : PQ Nat Nat := insertQ 10 5 emptyQ
def elementsToAdd : List (Nat × Nat) := [(3, 1), (7, 4), (2, 2), (9, 6)]
def finalQueue : PQ Nat Nat := addListQ elementsToAdd initialQueue

/-
#eval toListQ initialQueue
#eval toListQ finalQueue
-/

def pq1 : PQ Nat Nat := makeQ [(2, 1), (5, 3)]
def pq2 : PQ Nat Nat := makeQ [(1, 0), (8, 4)]
def pqCombined : PQ Nat Nat := combineQ pq1 pq2

/-
#eval toListQ pq1
#eval toListQ pq2
#eval toListQ pqCombined

#eval huffmanPQ [('a', 2), ('b', 3), ('c', 1), ('d', 20)]
#eval huffmanPQ [('x', 1), ('y', 1)]
#eval huffmanPQ [('z', 5)]
#eval huffmanPQ []
-/

end PriorityQueue

end Chapter8
