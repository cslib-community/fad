import Fad.Chapter9
import Fad.Chapter3

namespace Chapter9
open Chapter3 (accumArray assocs indices)
open SpanningTrees

/-!
# Exercises
-/

/-!
## Exercise 9.1
Some quick questions on graphs and digraphs:
1. Why can a digraph of `n` vertices contain up to `n²` edges, while a graph can
   contain no more than `n (n − 1)/2` edges?
2. Can a digraph have a cycle of length two?
3. Why is it the case that in an acyclic graph there is at most one path between
   any two vertices? Is this true of acyclic digraphs?
4. Can a labelled graph have more than one edge between two vertices?
5. Why is a spanning forest of a connected graph necessarily a spanning tree?
6. Why does a spanning tree of a connected graph of `n` vertices have exactly
   `n − 1` edges?
7. What is the maximum number of edges in a longest possible cycle of a graph of
   `n` vertices?
-/

-- TODO

/-!
## Exercise 9.2
Assuming vertices are labelled from 1 to `n`, define functions
  `toAdj : Graph → AdjArray`
  `toGraph : AdjArray → Graph`
for converting a digraph into its adjacency representation and vice versa.
-/

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

/-!
## Exercise 9.3
Draw all the spanning trees for the following graph:
(figure in the book)
-/

-- TODO

/-!
## Exercise 9.4
Assign weights to the edges `AB` and `CD` in the following graph to show
that the path from `A` to `D` in a MCST is not necessarily the shortest path
from `A` to `D`.
(figure in the book)
-/

-- TODO

/-!
## Exercise 9.5
Here is a possible divide-and-conquer algorithm for computing a MCST.
Divide the vertices `V` of the graph into two sets `V₁` and `V₂` that differ in
size by at most one. Let `Eᵢ` be the set of edges whose endpoints are in `Vᵢ`.
Recursively find a MCST for `G₁ = (V₁, E₁)` and `G₂ = (V₂, E₂)`. Finally, select
a lightest edge, one of whose endpoints is in `V₁` and the other in `V₂`, and
add it to the two MCSTs to form a single MCST. Does this algorithm work?
-/

-- TODO

/-!
## Exercise 9.6
The function `steps` in the specification of Kruskal's algorithm does
not discard an edge if it creates a cycle in a given forest, even though it will
also create a cycle in any subsequent forest. Write down a version of `steps`
that does discard such edges.
-/

-- TODO

/-!
## Exercise 9.7
What is the output of Kruskal's algorithm if the input is not a
connected graph? Adapt the algorithm to find the minimum-cost spanning forest of
an unconnected graph.
-/

-- TODO

/-!
## Exercise 9.8
Why is the test `t₁ ≠ t₂` in the specification of Kruskal's algorithm
sufficient to determine whether two trees in a forest are different? After all,
the trees `t₁ = ([1, 2], [(1, 2, 3)])` and `t₂ = ([2, 1], [(1, 2, 3)])` are the
same tree but the test `t₁ ≠ t₂` returns `True`. As a supplementary question,
can the test be made more efficient?
-/

-- TODO

/-!
## Exercise 9.9
Construct the function `weights` as used in Prim's algorithm when the
input is an undirected graph. What is the definition when the input is a
directed graph?
-/

-- TODO

/-!
## Exercise 9.10
Consider the problem of finding a maximum-cost spanning tree. Is there a
greedy algorithm for this problem?
-/

-- TODO

/-!
## Exercise 9.11
Here is the specification of a shortest-paths spanning tree:
  `spst ← MinWith cost · spats`
The function `spats` returns all spanning trees of a directed graph. Give a
definition of `spats`. To define `cost`, we need to compute the path from the
source vertex to every other vertex in the tree. Define a function
  `pathsFrom : Vertex → Tree → [Path]`
where `Path` is a synonym for `[Edge]`, such that `pathsFrom 1 t` returns the
paths from the source vertex 1 to every other vertex in the tree. Finally,
define
  `cost : Tree → [Distance]`
so that `cost t = [d₂, ..., dₙ]`, where `d_v` is the distance from the source
vertex 1 to vertex `v`.
-/

-- TODO

/-!
## Exercise 9.12
To find the shortest path between `A` and `B`, suppose we
simultaneously compute shortest routes from `A` to various towns, and shortest
routes from various towns to `B`, stopping when some intermediate town `C` has
been found in both directions. Does this idea work?
-/

-- TODO

/-!
## Exercise 9.13
Give an example to show that Dijkstra's algorithm does not work with
negative lengths even if there are no negative-length cycles.
-/

-- TODO

/-!
## Exercise 9.14
How would you modify Dijkstra's algorithm to stop as soon as the
shortest path to a given vertex is found?
-/

-- TODO

/-!
## Exercise 9.15
In the jogger's problem we can install a third component in the `links`
array to represent the root associated with each vertex:
  `type Links = Array Vertex (Vertex, Vertex, Distance)`
  `type State = (Links, [Vertex])`
  `parent : Links → Vertex → Vertex`
  `parent ls v = u where (u, _, _) = ls ! v`
  `root : Links → Vertex → Vertex`
  `root ls v = r where (_, r, _) = ls ! v`
  `distance : Links → Vertex → Distance`
  `distance ls v = d where (_, _, d) = ls ! v`
The starting state is then given by
  `start : Nat → State`
  `start n = (array (1, n) ((1, (1, 1, 0)) : [(v, (v, v, maxInt)) | v ← [2..n]]), [1..n])`
Give the modified definition of `gstep : Weights → State → State`.
-/

-- TODO

end Chapter9
