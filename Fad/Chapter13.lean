import Fad.Chapter1
import Fad.Chapter10
import Fad.API

namespace Chapter13

open Chapter1 (scanr₀)


-- # Section 13.1 Two numeric examples

def fib₀ : Nat → Int
| 0 => 0
| 1 => 1
| n + 2 => fib₀ (n + 1) + fib₀ n

def fib₀T : Nat → TimeM Int
| 0     => TimeM.pure 0
| 1     => TimeM.pure 1
| n + 2 => do
    let x ← fib₀T (n + 1)
    let y ← fib₀T n
    ✓ (x + y)

-- #eval fib₀ 10
-- #eval fib₀T 10
-- The complexity is exponential
-- #eval [5, 10, 15, 20].map fun n => (n, (fib₀T n).time)

--Litaral translation of tab and fib1

def tabAntigo (f : Nat → Int) (lo hi : Nat) : Array Int :=
  (List.range (hi - lo + 1)).map (fun i => f (lo + i)) |>.toArray

def tabAntigoT (f : Nat → TimeM Int) (lo hi : Nat) :
    TimeM (Array Int) := do
  let indices := List.range (hi - lo + 1)

  let values ← indices.mapM (fun i => f (lo + i))

  TimeM.tick (values.toArray) (2 * values.length)

def fib₁Antigo (n : Nat) : Int :=
  let rec a : Nat → Int :=
    fun i => if i ≤ 1 then i else a (i - 1) + a (i - 2)
  let arr := tabAntigo a 0 n
  arr[n]!

def fib₁AntigoT (n : Nat) : TimeM Int :=
  let rec aT : Nat → TimeM Int
    | 0 => TimeM.pure 0
    | 1 => TimeM.pure 1
    | k + 2 => do
        let x ← aT (k + 1)
        let y ← aT k
        ✓ (x + y)
  do
    let arr ← tabAntigoT aT 0 n
    ✓ (arr[n]!)

--#eval (fib₁AntigoT 10).ret
--#eval (fib₁AntigoT 10).time
--The Haskell example in the bool was supposed to be O(n),
--but given that Haskell is lazy, the complexity is O(n^2)

-- So we will append another tab function using thunk to get the O(n) complexity
private def badDependency [Inhabited α] : Thunk α :=
  Thunk.mk fun _ => panic! "undefined lazy-array entry"

def tabulate [Inhabited α]
    (f : (Nat → Thunk α) → Nat → Thunk α)
    (bounds : Nat × Nat) : Array (Thunk α) :=
  let (lo, hi) := bounds
  if hi < lo then
    #[]
  else
    (List.range (hi - lo + 1)).foldl
      (fun cells k =>
        let i := lo + k
        let fetch := fun j =>
          match cells[j - lo]? with
          | some cell => cell
          | none      => badDependency
        cells.push (f fetch i))
      #[]

def tabulateT [Inhabited α]
    (f : (Nat → Thunk α) → Nat → Thunk α)
    (bounds : Nat × Nat) : TimeM (Array (Thunk α)) :=
  let (lo, hi) := bounds
  if hi < lo then
    TimeM.pure #[]
  else
    (List.range (hi - lo + 1)).foldl
      (fun timedCells k => do
        let cells ← timedCells
        let i := lo + k
        let fetch := fun j =>
          match cells[j - lo]? with
          | some cell => cell
          | none      => badDependency
        ✓ (cells.push (f fetch i)))
      (TimeM.pure #[])

private def forceAt [Inhabited α]
    (cells : Array (Thunk α)) (bounds : Nat × Nat) (i : Nat) : α :=
  let (lo, _) := bounds
  match cells[i - lo]? with
  | some cell => cell.get
  | none      => panic! "index outside lazy-array bounds"


-- Lazy tabulation, corresponding to `a = tabulate f (0,n)` in the book.
private def fibF (a : Nat → Thunk Int) (i : Nat) : Thunk Int :=
  if i ≤ 1 then
    Thunk.mk fun _ => Int.ofNat i
  else
    let previous := a (i - 1)
    let beforePrevious := a (i - 2)
    Thunk.mk fun _ => previous.get + beforePrevious.get

def fib₁ (n : Nat) : Int :=
  let bounds := (0, n)
  let a := tabulate fibF bounds
  forceAt a bounds n

def fib₁T (n : Nat) : TimeM Int := do
  let bounds := (0, n)
  let a ← tabulateT fibF bounds
  TimeM.pure (forceAt a bounds n)

--#eval fib₁ 10
--#eval fib₁T 10
-- The complexity is O(n)
--#eval [10, 20, 40, 80].map fun n => (n, (fib₁T n).time)

def fib₂ (n : Nat) : Int :=
  let step := fun (a b : Int) => (b, a + b)
  let rec apply : Nat → Int × Int → Int × Int
    | 0, p => p
    | n+1, (a, b) => apply n (step a b)
  let (a, _) := apply n (0, 1)
  a

def fib₂T (n : Nat) : TimeM Int :=
  let step := fun (a b : Int) => (b, a + b)
  let rec applyT : Nat → Int × Int → TimeM (Int × Int)
    | 0, p          => TimeM.pure p
    | k + 1, (a, b) => do
        let next ← (✓ (step a b))
        applyT k next
  do
    let (a, _) ← applyT n (0, 1)
    TimeM.pure a

--#eval fib₂ 10
--#eval fib₂T 10
-- The complexity is O(n)
--#eval [10, 20, 40, 80].map fun n => (n, (fib₂T n).time)

def fact (n : Nat) : Int :=
  ((List.range (n + 1)).drop 1).map Int.ofNat |>.foldl (· * ·) 1

private def productT : List Int → TimeM Int
| []      => TimeM.pure 1
| x :: xs => do
    let p ← productT xs
    ✓ (x * p)

def factT (n : Nat) : TimeM Int :=
  productT (((List.range (n + 1)).drop 1).map Int.ofNat)


def bin₀ (n r : Nat) : Int :=
  fact n / (fact r * fact (n - r))

def bin₀T (n r : Nat) : TimeM Int :=
  if r > n then
    TimeM.pure 0
  else do
    let fn ← factT n
    let fr ← factT r
    let fnr ← factT (n - r)
    let denominator ← (✓ (fr * fnr))
    ✓ (fn / denominator)

--#eval bin₀ 6 3
--#eval bin₀T 6 3
--#eval [10, 20, 40, 80].map fun n =>((n, n / 2), (bin₀T n (n / 2)).time)

def bin₁ : Nat → Nat → Int
| _, 0               => 1
| 0, _           => 0
| n + 1, r + 1       =>
  if r + 1 = n + 1 then 1
  else bin₁ n (r + 1) + bin₁ n r

def bin₁T : Nat → Nat → TimeM Int
| _, 0         => TimeM.pure 1
| 0, _         => TimeM.pure 0
| n + 1, r + 1 =>
  if r + 1 = n + 1 then
    TimeM.pure 1
  else do
    let x ← bin₁T n (r + 1)
    let y ← bin₁T n r
    ✓ (x + y)

--#eval bin₁ 6 3
--#eval bin₁T 6 3
--#eval [4, 8, 12, 16].map fun n =>((n, n / 2), (bin₁T n (n / 2)).time)


-- For bin2 we need a two dimentianl tab function
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

def aplT {α : Type} : Nat → (α → TimeM α) → α → TimeM α
| 0, _, acc     => TimeM.pure acc
| n + 1, f, acc => do
    let next ← f acc
    aplT n f next

-- scanr0 of chapter 1 always add the initial accumulator q₀ to the end.

--#eval scanr₀ (· + ·) 0 [1, 1, 1, 1]
--It ends in 0, but in the book the example takes this values [4,3,2,1]
--So we will defind scar1

def scanr₁ {α : Type} (f : α → α → α) (xs : List α) : List α :=
  match xs.reverse with
  | [] => []
  | q₀ :: rest =>
      scanr₀ f q₀ rest.reverse

def scanr₁T {α : Type}
    (f : α → α → α) (xs : List α) : TimeM (List α) :=
  match xs.reverse with
  | [] =>
      TimeM.pure []
  | q₀ :: rest =>
      ✓ (scanr₀ f q₀ rest.reverse), rest.length

--#eval scanr₁ (· + ·) [1, 1, 1, 1]

def bin₃Antigo (n r : Nat) : Int :=
  let row := apl (n - r) (scanr₀ (· + ·) 0) (List.replicate (r + 1) 1)
  row.headD 1

--#eval bin₃Antigo 6 3

def bin₃ (n r : Nat) : Int :=
  let row :=
    apl (n - r)
      (scanr₁ (· + ·))
      (List.replicate (r + 1) 1)
  row.headD 1

def bin₃T (n r : Nat) : TimeM Int := do
  let row ←
    aplT (n - r)
      (scanr₁T (· + ·))
      (List.replicate (r + 1) 1)
  TimeM.pure (row.headD 1)


--#eval [10, 20, 40, 80].map fun n => ((n, n / 2), (bin₃T n (n / 2)).time)
--#eval bin₃ 6 3

-- # Section 13.2

namespace Knapsack

open Chapter10.Knapsack
  (Name Value Weight Item Selection name value weight add maxWith items₁)

private def emptySelection : Selection :=
  ([], 0, 0)

def choices : Weight → List Item → List Selection
| _, [] => [emptySelection]
| w, i :: its =>
  if w < weight i then
    choices w its
  else
    let withoutI := choices w its
    let withI := (choices (w - weight i) its).map (add i)
    withoutI ++ withI

def choicesT : Weight → List Item → TimeM (List Selection)
| _, [] => TimeM.pure [emptySelection]
| w, i :: its => do
  -- `decide` converts the decidable proposition into a `Bool` before it is
  -- placed inside `TimeM`.
  let tooHeavy ← (✓ (decide (w < weight i)))
  match tooHeavy with
  | true => choicesT w its
  | false => do
      let withoutI ← choicesT w its
      let remaining ← choicesT (w - weight i) its
      ✓ (withoutI ++ remaining.map (add i))

--#guard (choices 50 items₁).length = 11


def better (sn₁ sn₂ : Selection) : Selection :=
  if value sn₂ ≤ value sn₁ then sn₁ else sn₂

def betterT (sn₁ sn₂ : Selection) : TimeM Selection :=
  ✓ (better sn₁ sn₂)

private def maxWithValueT : List Selection → TimeM Selection
| [] => TimeM.pure emptySelection
| sn :: sns =>
  let rec go : Selection → List Selection → TimeM Selection
    | best, [] => TimeM.pure best
    | best, candidate :: rest => do
        let winner ← betterT best candidate
        go winner rest
  go sn sns

def swag₀ (w : Weight) (its : List Item) : Selection :=
  maxWith value (choices w its)

def swag₀T (w : Weight) (its : List Item) : TimeM Selection := do
  let sns ← choicesT w its
  maxWithValueT sns

--#guard swag₀ 50 items₁ = (["Laptop", "Jewellery", "CD collection"], 99, 46)
--#guard (swag₀T 50 items₁).ret = swag₀ 50 items₁

def swag₁ : Weight → List Item → Selection
| _, [] => emptySelection
| w, i :: its =>
  if w < weight i then
    swag₁ w its
  else
    better
      (swag₁ w its)
      (add i (swag₁ (w - weight i) its))

def swag₁T : Weight → List Item → TimeM Selection
| _, [] => TimeM.pure emptySelection
| w, i :: its => do
  let tooHeavy ← (✓ (decide (w < weight i)))
  match tooHeavy with
  | true => swag₁T w its
  | false => do
      let withoutI ← swag₁T w its
      let bestForRemaining ← swag₁T (w - weight i) its
      betterT withoutI (add i bestForRemaining)

--#guard swag₁ 50 items₁ = swag₀ 50 items₁
--#guard (swag₁T 50 items₁).ret = swag₁ 50 items₁

-- ## Dynamic programming with one row

private def foldrT {α β : Type}
    (f : α → β → TimeM β) (e : β) : List α → TimeM β
| [] => TimeM.pure e
| x :: xs => do
    let acc ← foldrT f e xs
    f x acc

def step (w : Weight) (i : Item) (row : List Selection) : List Selection :=
  let wi := weight i
  let shifted := (row.drop wi).map (add i)
  List.zipWith better row shifted ++ row.drop (w + 1 - wi)

def stepT (w : Weight) (i : Item) (row : List Selection) :
    TimeM (List Selection) :=
  -- The abstract cost is one unit for every position in the row.
  ✓ (step w i row), row.length

def swag₂ (w : Weight) (its : List Item) : Selection :=
  let start := List.replicate (w + 1) emptySelection
  let row := its.foldr (step w) start
  row.headD emptySelection

def swag₂T (w : Weight) (its : List Item) : TimeM Selection := do
  let start := List.replicate (w + 1) emptySelection
  let row ← foldrT (stepT w) start its
  TimeM.pure (row.headD emptySelection)

--#guard swag₂ 50 items₁ = swag₀ 50 items₁
--#guard (swag₂T 50 items₁).ret = swag₂ 50 items₁
--#guard (swag₂T 50 items₁).time = items₁.length * (50 + 1)

--#eval (Chapter13.Knapsack.swag₀T 50 Chapter10.Knapsack.items₁)
--#eval (Chapter13.Knapsack.swag₁T 50 Chapter10.Knapsack.items₁)
--#eval (Chapter13.Knapsack.swag₂T 50 Chapter10.Knapsack.items₁)

end Knapsack

-- # Section 13.3

inductive Op where
  | copy    : Char → Op
  | replace : Char → Char → Op
  | delete  : Char → Op
  | insert  : Char → Op
deriving Repr, BEq

abbrev Edit := List Op

def ecost : Op → Nat
| .copy _      => 0
| .replace _ _ => 3
| .delete _    => 2
| .insert _    => 2

def cost : Edit → Nat
| []        => 0
| op :: ops => ecost op + cost ops

def pick (x y : Char) : Op :=
  if x = y then Op.copy x else Op.replace x y

def minByCost : List Edit → Edit
| []      => []
| e :: es =>
  es.foldl
    (fun best candidate =>
      if cost candidate < cost best then candidate else best)
    e



end Chapter13
