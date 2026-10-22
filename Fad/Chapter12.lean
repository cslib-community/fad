module

public import Fad.Chapter1
public import Fad.Chapter7
public import Fad.Chapter8

@[expose] public section

namespace Chapter12
open Chapter1 (concatMap)

/-!
# Chapter Info

In this chapter $ 2 ∈ 3$ we will confine ourselves to just two examples.
The first is a simple **scheduling problem**, while the second involves **breaking paragraphs into lines**.
-/

-- # Section12.1 Ways of generating partitions
section

/-- A partition of a list of type [A] has type [[A]], so a list of partitions has type
[[[A]]]. -/
abbrev Segment (a : Type) := List a
abbrev Partition (a : Type) := List (Segment a)


def splits {a : Type} : List a → List (List a × List a)
 | [] => []
 | x :: xs => ([x], xs) :: (splits xs).map fun ⟨ys, zs⟩ => (x :: ys, zs)


theorem length_lt_of_cons_split {α : Type} (xs ys zs : List α)
  (h : (ys, zs) ∈ splits xs) : zs.length < xs.length := by
  induction xs generalizing ys zs with
  | nil =>
    simp [splits] at h
  | cons x xs ih =>
    simp only [splits, List.mem_cons, List.mem_map] at h
    cases h with
    | inl h' =>
      simp at h'
      cases h'; simp_all [List.length]
    | inr h'' =>
      rcases h'' with ⟨p, hin, heq⟩
      cases p with
      | mk ys' zs' =>
        cases heq
        specialize ih ys' zs' hin
        grind

def parts {a : Type} : List a → List (Partition a)
  | [] => [[]]
  | xs =>
    (splits xs).flatMap fun ⟨ys, zs⟩ =>
      have : zs.length < xs.length := by
        apply length_lt_of_cons_split xs ys zs
        sorry
      (parts zs).map fun yss => ys :: yss
  termination_by xs => xs.length

def cons (x : a) (p : Partition a) : Partition a :=
 [x] :: p

def glue (x : a) : Partition a → Partition a
 | s :: p => (x :: s) :: p
 | []     => panic! "glue: empty partition"

def extendl (x : a) : Partition a → List (Partition a)
 | [] => [cons x []]
 | p  => [cons x p, glue x p]

def parts₁ : List Nat → List (Partition Nat) :=
  List.foldr (concatMap ∘ extendl) [[]]


def last [Inhabited a] : List a → a
 | [x]   => x
 | []    => panic! "last: empty list"
 | _::xs => last xs

def init [Inhabited a] : List a → List a
 | [_]     => []
 | []      => panic! "init: empty list"
 | x :: xs => x :: init xs

def snoc (x : a) (p : Partition a) : Partition a :=
 p ++ [[x]]

def bind (x : a) (p : Partition a) : Partition a :=
 init p ++ [last p ++ [x]]

def extendr (x : a) : Partition a → List (Partition a)
 | [] => [snoc x []]
 | p  => [snoc x p, bind x p]

def parts₂ : List Nat → List (Partition Nat) :=
  List.foldl (flip (concatMap ∘ extendr)) [[]]
end

-- # Section 12.3 The paragraph problem
section
open Chapter1 (foldr)
open Chapter7 (minWith)
open Chapter8.S1 (foldrn)

/-- The major constraint on paragraphs is that all lines have to fit into a specified
width. For simplicity, we assume a single globally defined value maxWidth that
gives the maximum width a line can possess.
-/
def maxWidth : Nat := 80

/--The definition depends on another globally defined constant optWidth, whose value
is at most maxWidth and which specifies the optimum width of each line of a
paragraph.
-/
def optWidth : Nat := 60

/-- It is assumed that a text consists of a nonempty sequence of words, each word being
a nonempty sequence of non-space characters. A paragraph therefore consists of at
least one line.
-/
abbrev Word := List Char
abbrev Text := List Word
abbrev Line := List Word
abbrev Para := List Line

def width (line : Line) : Nat :=
  foldrn (fun w n => w.length + 1 + n) (fun w => w.length) line

--- another way
def aux_add (w : Word) (n : Nat) : Nat := w.length + 1 + n

def width₁ : Line → Nat :=
  foldrn aux_add List.length
---

def fits (line : Line) : Bool :=
  width line ≤  maxWidth

--- test cases
def foo : Word := ['f', 'o', 'o']
def bar : Word := ['b', 'a', 'r']
def line : Line := [foo, bar]

example : width line = 7 := rfl
example : width₁ line = 7 := rfl

--- end test cases

/-- ## Cost functions -/

def cost₁ (p : Para) : Nat := p.length


def waste₂ (line : Line) : Nat := maxWidth - width line

def cost₂ (p : Para) : Nat :=
  (Chapter12.init p).map waste₂ |> List.sum

def waste₃ (line : Line) : Nat :=
  let d := optWidth - width line
  d * d

def cost₃ (p : Para) : Nat :=
  (Chapter12.init p).map waste₃ |> List.sum

def cost₄ (p : Para) : Nat :=
  (Chapter12.init p).map waste₂ |> List.foldr max 0

def cost₅ (p : Para) : Nat :=
  (Chapter12.init p).map waste₃ |> List.foldr max 0

/--  There is an obvious greedy algorithm for the paragraph problem: -/
def add (p : Para) (w : Word) : Para :=
  match p with
  | [] => Chapter12.snoc w []
  | _  =>
    let candidates := [Chapter12.bind w p, Chapter12.snoc w p]
    let valid := candidates.filter (λ para => fits (Chapter12.last para))
    valid.headD []

def basic_greedy (ws : Text) : Para :=
  ws.foldl add []

/-- Adding cost to the algorithm -/
def tstep (ps : List Para) (w : Word) (cost : Para -> Nat) : List Para :=
  match ps with
  | [[]] => [[[w]]]
  | _    =>
    let newLine := Chapter7.minWith cost (ps.map (Chapter12.snoc w))
    let sameLine := ps.map (Chapter12.bind w) |>.filter (fits ∘ Chapter12.last)
    newLine :: sameLine

def para (ws : Text) (cost : Para -> Nat) : Para :=
  let step := λ ps w => tstep ps w cost
  Chapter7.minWith cost (ws.foldl step [[]])

end

end Chapter12
