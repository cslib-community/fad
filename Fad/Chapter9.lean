import Lean.Data.AssocList
import Fad.Chapter1
import Fad.Chapter3
import Fad.«Chapter1-Ex»
import Fad.«Chapter5-Ex»
import Fad.Chapter7

namespace Chapter9

/- # Section 9.1 Graphs and spanning trees -/

abbrev Vertex := Nat
abbrev Weight := Int
abbrev Edge   := (Vertex × Vertex × Weight)
abbrev Graph  := (List Vertex × List Edge)

def nodes (g : Graph) : List Vertex := g.1
def edges (g : Graph) : List Edge := g.2
def souce  (e : Edge) : Vertex := e.1
def target (e : Edge) : Vertex := e.2.1
def weight (e : Edge) : Weight := e.2.2

abbrev AdjArray := Lean.AssocList Vertex (List (Vertex × Weight))

abbrev Tree   := Graph
abbrev Forest := List Tree

def cost (t : Tree) : Int :=
  (edges t).map weight |>.sum


/- # Section 9.2 Kruskal’s algorithm -/

namespace  SpanningTrees

open Chapter1 (wrap apply)
open Chapter5 (sortOn₃)

abbrev State  := Forest × List Edge

def extract (s : State) : Tree :=
  s.1.head!

def done (s : State) : Bool :=
  s.1.length = 1

def start₀ (g : Graph) : State :=
  (nodes g |>.map (fun v => ([v], [])), edges g)

def find (ts : Forest) (v : Vertex) : Tree :=
  (ts.find? (fun t => (nodes t).contains v)).get!

def safeEdge (e : Edge) (ts : Forest) : Bool :=
  find ts (souce e) ≠ find ts (target e)

def add (e : Edge) (ts : Forest) : Forest :=
  let t1 := find ts (souce e)
  let t2 := find ts (target e)
  let rest := ts.filter (fun t => t ≠ t1 ∧ t ≠ t2)
  ((t1.1 ++ t2.1), e :: (t1.2 ++ t2.2)) :: rest

def steps : State → List State
| (ts, es) =>
  Chapter7.picks es
  |>.filterMap (fun (e, es') =>
    if safeEdge e ts then
      some (add e ts, es')
    else
      none)

def spats (g : Graph) : List Tree :=
  (Chapter1.until' (fun ss => ss.all done) (fun ss => List.flatMap steps ss)) (wrap (start₀ g))
  |>.map extract

def MCC (g : Graph) : Tree := Chapter7.minWith cost (spats g)

def gstep (s : State) : State :=
  match s with
  | (_, []) => s
  | (ts, e :: es) =>
    let t1 := find ts (souce e)
    let t2 := find ts (target e)
    let rest := ts.filter (fun t => t ≠ t1 ∧ t ≠ t2)
    let ts' := ((t1.1 ++ t2.1), e :: (t1.2 ++ t2.2)) :: rest
    if t1 ≠ t2 then
      (ts', es)
    else
      gstep (ts, es)

def start₁ (g : Graph) : State :=
  (nodes g |>.map (fun v => ([v], [])), sortOn₃ weight (edges g))

def kruskal₁ (g : Graph) : Tree :=
  Chapter1.until' done gstep (start₁ g) |> extract

def kruskal₂ (g : Graph) : Tree :=
  let n := (nodes g).length
  extract (apply (n - 1) gstep (start₁ g))

end SpanningTrees


/- # Section 9.4 Prim’s algorithm -/

namespace primsalgorithm

open Chapter7 (minWith picks)
open Chapter1 (concatMap apply)


abbrev State := (Tree × List Edge)


def add (e: Edge) (t: Tree) : Tree :=
  let (vs, es) := t
  cond (vs.contains (souce e)) (target e :: vs, e :: es) (souce e :: vs, e::es)


def safeEdge (e: Edge) (t: Tree) : Bool :=
  (nodes t).contains (souce e) ≠ (nodes t).contains (target e)


def steps (s: State) : List State :=
  let (t,es) := s
  (picks es).filterMap fun (e, es') => cond (safeEdge e t) (some (add e t, es')) none


def spats (g : Graph) : List Tree :=
  let start : State :=
    match nodes g with
     | []     => (([], []), [])
     | v :: _ => (([v], []), edges g)

  let done : State → Bool :=
    fun (t, _) => (nodes t).length == (nodes g).length

  let rec helper (ss : List State) (fuel: Nat): List Tree :=
    match fuel with
      | 0        => panic! "Never here"
      | fuel + 1 => cond (ss.all done) (ss.map Prod.fst) (helper (concatMap steps ss) fuel)
        termination_by fuel

  helper [start] g.1.length


def mcst : Graph → Tree :=
  minWith cost ∘ spats


def gstep : State → State
  | (t, [])      => (t, [])
  | (t, e :: es) =>

    let keep (e: Edge) (s: State) : State :=
      let (t', es') := s
      (t', e :: es')

    cond (safeEdge e t) (add e t, es) (keep e (gstep (t, es)))


def prim (g : Graph) : Tree :=
  let start : State :=
    match nodes g with
    | []     => (([], []), [])
    | v :: _ => (([v], []), edges g)

  let done : State → Bool :=
    fun (t, _) => (nodes t).length == (nodes g).length

  let rec helper (s : State) (fuel : Nat) : State :=
    match fuel with
    | 0        => panic! "Never Here"
    | fuel + 1 => cond (done s) s (helper (gstep s) fuel)
    termination_by fuel

  (helper start g.1.length).1


def prim' (g : Graph) : Tree :=
  let start : State :=
    match nodes g with
    | []     => (([], []), [])
    | v :: _ => (([v], []), edges g)
  let n := (nodes g).length
(apply (n-1) gstep (start)).1

/-
def graphA : Graph := ([1,2,3,4],[(1, 2, 1), (1, 3, 2), (2, 3, 5), (3,4,20), (3,4,50)])

#eval prim graphA
#eval prim' graphA
-/


abbrev Links := Std.HashMap Vertex (Vertex × Weight)
abbrev State' := Links × List Vertex

def parent (ls : Links) (v : Vertex) : Vertex :=
  (ls.get! v).1

def weight' (ls: Links) (v : Vertex) : Weight :=
  (ls.get! v).2

abbrev Weights := Std.HashMap (Vertex × Vertex) Weight

def start (n : Nat) : State' :=
  let vs := List.range n |>.map (· + 1)
  let lk : Links :=
    vs.foldl (init := Std.HashMap.emptyWithCapacity)
      fun map v => cond (v==1) (map.insert v (1, 0)) (map.insert v (v, 2^63) )
      --Utilizei o valor de 2^63 para representar o comprimento infinito (definido como maxBound em Haskell)
  (lk, vs)

--#eval start 3


def gstep' (wa : Weights) (s: State') : State' :=
  let (lk, vs) := s
  let better (vwa vwb : Vertex × Weight)  := cond (vwa.2 ≤ vwb.2) vwa vwb
  let v := minWith (weight' lk) vs
  let vs' := vs.filter (· ≠ v)

  let lk' := vs'.foldl (fun acc u =>
   match wa.get? (u, v) with
    | none => acc
    | some w =>
        let newLink := (v, w)
        acc.alter u (fun curr =>
          match curr with
          | none => some newLink
          | some existing => some (better existing newLink)
        )
  ) lk
  (lk', vs')


def extract (s : State') : Tree :=
  let (ls, _) := s
  let vs := ls.toList.map (fun (v, _) => v)
  let es := ls.toList.filterMap fun (v, (u, w)) => cond (v ≠ 1) (some (u, v, w)) (none)
  (vs, es)

/-
def weightsA : Weights := Std.HashMap.emptyWithCapacity.insert (2,3) 5
  |>.insert (3,4) 7
  |>.insert (4,5) 9
  |>.insert (5,6) 1
  |>.insert (6,7) 13

def linkA : Links := Std.HashMap.emptyWithCapacity.insert 1 (2,3)
  |>.insert 2 (3,5)
  |>.insert 3 (4,7)
  |>.insert 4 (5,9)
  |>.insert 5 (6,11)
  |>.insert 6 (7,13)

def vertS : List Vertex :=
  [2,3,4,5,6]

def stateA : State' :=
  (linkA, vertS)

#eval extract (gstep' weightsA stateA)
-/

end primsalgorithm
end Chapter9
