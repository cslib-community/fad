module

public import Fad.Chapter1

@[expose] public section

namespace Chapter13
open Chapter1 (scanr₀)


-- # Section 13.1 Two numeric examples

def fib₀ : Nat → Int
| 0 => 0
| 1 => 1
| n + 2 => fib₀ (n + 1) + fib₀ n

--#eval fib₀ 10

def tab (f : Nat → Int) (lo hi : Nat) : Array Int :=
  (List.range (hi - lo + 1)).map (fun i => f (lo + i)) |>.toArray

def fib₁ (n : Nat) : Int :=
  let rec a : Nat → Int :=
    fun i => if i ≤ 1 then i else a (i - 1) + a (i - 2)
  let arr := tab a 0 n
  arr[n]!

--#eval fib₁ 10

def fib₂ (n : Nat) : Int :=
  let step := fun (a b : Int) => (b, a + b)
  let rec apply : Nat → Int × Int → Int × Int
    | 0, p => p
    | n+1, (a, b) => apply n (step a b)
  let (a, _) := apply n (0, 1)
  a

--#eval fib₂ 10

def fact (n : Nat) : Int :=
  ((List.range (n + 1)).drop 1).map Int.ofNat |>.foldl (· * ·) 1

def bin₀ (n r : Nat) : Int :=
  fact n / (fact r * fact (n - r))

--#eval bin₀ 6 3

def bin₁ : Nat → Nat → Int
| _, 0               => 1
| 0, _           => 0
| n + 1, r + 1       =>
  if r + 1 = n + 1 then 1
  else bin₁ n (r + 1) + bin₁ n r

--#eval bin₁ 6 3

def bin₂ (n r : Nat) : Int := Id.run do
  let mut a : Array ((Nat × Nat) × Int) := #[]
  for i in [0:n+1] do
    for j in [0:Nat.min (r + 1) (i + 1)] do
      let value :=
        if j = 0 ∨ i = j then 1
        else
          let get := fun i j =>
            (a.find? (fun (x, _) => x = (i, j))).map Prod.snd |>.getD 0
          get (i - 1) j + get (i - 1) (j - 1)
      a := a.push ((i, j), value)
  return (a.find? (fun (x, _) => x = (n, r))).map Prod.snd |>.getD 0

--#eval bin₂ 6 3

def apl {α : Type} : Nat → (List α → List α) → List α → List α
| 0, _, acc => acc
| n + 1, f, acc => apl n f (f acc)

def bin₃ (n r : Nat) : Int :=
  let row := apl (n - r) (scanr₀ (· + ·) 0) (List.replicate (r + 1) 1)
  row.headD 1

--#eval bin₃ 6 3

end Chapter13
