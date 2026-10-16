module

public import Fad.Chapter9
public import Fad.Chapter3

@[expose] public section

namespace Chapter9
open Chapter3 (accumArray assocs indices)
open SpanningTrees

-- # Ex 9.2

def toAdj (g : Graph) : AdjArray :=
  let n := (nodes g).length
  accumArray (flip List.cons) [] (1,n) ((edges g).map (λ (a,b,c) => (a, (b,c))))

/- FIXME
def toGraph (adj : AdjArray) : Graph :=
 let vs := indices _ _ adj
 let es : List Edge :=
  (assocs _ _ adj).flatMap (λ (v, ps) => ps.map (λ p => (v, p.1, p.2)))
 (vs, es)
-/

def g : Graph :=
 ([0, 1, 2, 3],
  [(0, 1, 1), (1, 2, 5), (1, 3, 10), (2, 3, 2), (3, 0, 4)])

-- #eval toAdj g |> toGraph

end Chapter9
