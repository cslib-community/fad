module

public import Fad.Chapter1
public import Fad.Chapter12

@[expose] public section

namespace Chapter12
open Chapter1 (concatMap)

/- # Exercicio 12.1
   a definição recursiva de `parts` provavelmente teria uma prova mais simples
   mas não consigo usar na prova por ser `partial`.
-/

example : ∀ xs : List Nat, (parts₁ xs).length = 2^(xs.length - 1) := by
 intro xs
 induction xs with
 | nil => simp [parts₁]
 | cons x xs ih =>
   sorry

/- # Exercício 12.2
   como parts é partial, não consigo expandir em uma prova. E `parts₁`
   obviamente não é a primeira definição de `parts` tratada no exercício.
-/

example : parts₁ [1,2] = [[[1], [2]], [[1, 2]]] := by
  unfold parts₁
  rw [List.foldr]; rw [Function.comp]
  rw [List.foldr]; rw [Function.comp]
  simp [concatMap, Chapter1.concat₁]
  sorry
  /- simp [List.foldr]
  simp [cons]
  simp [cons]
  simp [glue] -/


/- # Exercicio 12.3 -/

def parts₃ {α : Type} : List α → List (Partition α) :=
  let step (x : α) : List (Partition α) → List (Partition α)
   | [[]] => [[[x]]]
   | ps => ps.map (cons x) ++ ps.map (glue x)
  List.foldr step [[]]

-- #eval parts₃ [1,2,3]


/- # Exercicio 12.4 -/

section
open List (filter all head!)

def ok (xs : List Nat) : Bool :=  xs.all (· > 0)

def okextendl (x : Nat) : Partition Nat → List (Partition Nat) :=
 filter (ok ∘ head!) ∘ extendl x

variable (h : ∀ x ps, filter (flip all ok) (concatMap (extendl x) ps) =
              concatMap (okextendl x) (filter (flip all ok) ps))

example
  : List.filter (flip List.all ok) ∘ parts₁ = List.foldr (concatMap ∘ okextendl) [[]] := by
  funext xs
  unfold parts₁
  simp [Function.comp]
  induction xs with
  | nil =>
    simp [List.foldr, flip]
  | cons a as ih =>
    have h1 := h a
    sorry

end

/- # Exercicio 12.5 -/

section
open List (range head! tail zipWith and)

def leftmin  (xs : List Nat) := xs.all (head! xs ≤ ·)
def rightmax (xs : List Nat) := xs.all (· ≤ last xs)
def ordered  (xs : List Nat) := and $ zipWith (· ≤ ·) xs (tail xs)
def nmatch   (xs : List Nat) := and $ zipWith (· ≠ ·) xs (range xs.length)

def suffixClosed (p : List Nat → Bool) : Prop :=
    ∀ xs ys, p (xs ++ ys) → p ys

def prefixClosed (p : List Nat → Bool) : Prop :=
    ∀ xs ys, p (xs ++ ys) → p xs

example : suffixClosed leftmin := by
   unfold suffixClosed
   intro xs ys
   unfold leftmin; simp
   intro h
   sorry


end


end Chapter12
