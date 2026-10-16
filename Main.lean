import Fad

def readFile (filename : String) : IO (List Nat) := do
  let contents ← IO.FS.readFile filename
  let lines := contents.splitOn "\n"
  let mut result := []
  for line in lines do
    match line.trimAscii.toNat? with
    | some n => result := n :: result
    | none => result := result
  return result


def main (args : List String) : IO Unit := do
 match args with
 | [] => println! "Usage: lake fad FILE"
 | a :: _ =>
  let r ← readFile a
  let t := Chapter4.BST2.mkTree r
  println! t.height
  println! Chapter4.BST2.search id 678 t
