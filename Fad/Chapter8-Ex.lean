module

public import Fad.Chapter8

@[expose] public section

namespace Chapter8

def splits : List α → List (List α × List α)
| []       => []
| x :: xs  =>
  ([], x :: xs) :: (splits xs).map (fun (ys, zs) => (x :: ys, zs))

def splitsn : List α → List (List α × List α)
| []       => []
| [_]      => []
| x :: xs  =>
  ([x], xs) :: (splitsn xs).map (fun (ys, zs) => (x :: ys, zs))


end Chapter8
