module

public import Fad.Chapter2
public import Fad.Chapter1

@[expose] public section

namespace Chapter2
open Chapter1


-- # Exercicio 2.9

def op1 {a : Type} : (List a) → a → a
| [], y => y
| (x::_), _ => x

example {xss : List (List α)} {e : α} (h : (concat₁ xss) ≠ [])
  : List.head (concat₁ xss) h = foldr op1 e xss:= by
    induction xss with
    | nil => contradiction
    | cons xs xss ih =>
      cases xs with
      | nil => simp [concat₁, List.head, foldr, op1]; exact ih h
      | cons x xs => simp [concat₁, List.head, foldr, op1]

-- # Exercicio 2.12

def inits (as : List a) : List (List a) :=
  let rec help (f : List a → List a) : List a → List (List a)
  | []      => (f []) :: []
  | x :: xs =>
    (f []) :: help (f ∘ List.cons x) xs
  help id as


-- 2.14

def tails1 (xs : List α) : List (List α) :=
  List.takeWhile (¬ ·.isEmpty) (iterate xs.length List.tail xs)


end Chapter2
