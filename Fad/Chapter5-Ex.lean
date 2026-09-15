import Fad.Chapter1
import Fad.Chapter3
import Fad.Chapter5

namespace Chapter5

/-
 # Exercicio 5.2 : qsort definitions
-/

section
open Quicksort

variable {a : Type} [h₁ : LT a] [h₂ : DecidableRel (α := a) (· < ·)]

-- trocar cases para induction?

theorem qsort₀_eq_qsort₁ (xs : List a) : qsort₀ xs = qsort₁ xs := by
  cases xs with
  | nil =>
    rw [qsort₀, Function.comp, mkTree, Tree.flatten]
    rw [qsort₁]
  | cons a as =>
    rw [qsort₀, Function.comp.eq_1 Tree.flatten mkTree]
    rw [mkTree, Tree.flatten]
    simp
    rw [← Function.comp.eq_1 Tree.flatten mkTree, ← qsort₀]
    rw [← Function.comp.eq_1 Tree.flatten mkTree, ← qsort₀]
    rw [qsort₁]
    simp
    have h₁ := qsort₀_eq_qsort₁ (List.filter (fun x => decide (x < a)) as)
    have h₂ := qsort₀_eq_qsort₁ (List.filter (not ∘ fun x => decide (x < a)) as)
    rw [h₁, h₂]
termination_by xs.length
decreasing_by
  all_goals simp
  all_goals grind

end


/- # Exercicio 5.6 -/

namespace Quicksort

partial def qsort₃ [LE α] [DecidableRel (α := α) (· ≤ ·)] (y : List α) : List α :=
  match y with
  | [] => []
  | x::xs => help x xs [] []
  where
   help  (x : α) (ys us vs: List α) : List α:=
    match ys with
    | []      => qsort₃ us ++ [x] ++ qsort₃ vs
    | y :: xs =>
      if x ≤ y then
       help x xs us (y::vs)
      else
       help x xs (y::us) vs

mutual
partial def help₄ [LE α] [DecidableRel (α := α) (· ≤ ·)]
 (x : α) (ys us vs: List α) : List α:=
 dbg_trace "help₄ {ys.length} {us.length} {vs.length}"
 match ys with
 | []      => qsort₄ us ++ [x] ++ qsort₄ vs
 | y :: xs =>
   if x ≤ y then
     help₄ x xs us (y::vs)
   else
     help₄ x xs (y::us) vs

partial def qsort₄ [LE α] [DecidableRel (α := α) (· ≤ ·)] : List α → List α
 | [] => []
 | x::xs => dbg_trace "qsort₄ {(x::xs).length}"; help₄ x xs [] []

end


mutual
def help₅ [LE α] [DecidableEq α] [DecidableRel (@LE.le α _)]
          (t : Nat) (x : α) (ys us vs: List α) : List α :=
  if t = 0 then x :: ys else
  if _ : ys = [] then
    qsort₅ (t - 1 - vs.length) us ++ [x] ++ qsort₅ (t- 1 - us.length) vs
  else
    match ys with
    | y :: xs =>
      if  x ≤ y then
       help₅ t x xs us (y::vs)
      else
       help₅ t x xs (y::us) vs
termination_by (t, ys)

def qsort₅ [LE α] [DecidableEq α] [DecidableRel (α := α) (· ≤ ·)]
           (n : Nat) (ys : List α) : List α :=
  if n = 0 then ys else
  if  _ : ys.length = 0 then []
   else
    match ys with
    | x :: xs => help₅ n x xs [] []
termination_by (n, ys)
end


end Quicksort


/- # Exercicio 5.7 : Provar que T(m,n) ≤ m + n -/

def T (m n : Nat) : Nat :=
  match m, n with
  | 0    , _     => 0
  | _    , 0     => 0
  | m + 1, n + 1 => 1 + max (T m (n + 1)) (T (m + 1) n)

example (a b : Nat) : T a b ≤ a + b := by
  induction a generalizing b with
  | zero =>
    rw [T, Nat.zero_add]
    exact Nat.zero_le b
  | succ a ha =>
    induction b with
    | zero =>
      rw [T, Nat.add_zero]
      exact Nat.zero_le (a+1)
      simp
    | succ b h2 =>
      rw [T]
      have h1 : T a (b + 1) ≤ a + b + 1 := by
        exact ha (b+1)
      rw [Nat.succ_add, Nat.succ_add, Nat.zero_add]
      rw [Nat.succ_le_succ_iff]
      rw [← Nat.add_assoc]
      rw [Nat.max_le]
      rw [Nat.add_assoc, Nat.add_comm 1 b, ← Nat.add_assoc] at h2
      exact And.intro h1 h2


/- # Exercicio 5.8 : see book -/


/- # Exercicio 5.9 -/

section

open Mergesort

example (xs : List Nat) : msort₂ xs = msort₃ xs := by
  induction xs with
  | nil => simp [msort₂, msort₃, mkPair, mkTree₁, mkTree₂]
  | cons x xs ih =>
    simp [msort₂, msort₃]
    sorry

end

/- # Exercicio 5.10 -/

def expression₁ {α : Type} : List α → List α :=
  flip (List.foldl (λ f x => (x :: ·) ∘ f) id) []

def expression₂ {α : Type} : List α → List α :=
  flip (List.foldr (λ x f => f ∘ (x :: ·)) id) []

def reverse {α : Type} : List α → List α :=
  List.foldl (flip List.cons) []

theorem expression₁_eq_reverse_aux (g : List α → List α) (xs ys : List α)
  : (xs.foldl (λ f x => (x :: ·) ∘ f) g) ys = xs.foldl (flip List.cons) (g ys) := by
  induction xs generalizing g with
  | nil => rfl
  | cons z zs ih =>
    exact ih ((fun x => z :: x) ∘ g)

theorem expression₂_eq_reverse_aux (xs ys : List α)
  : (xs.foldr (λ x f => f ∘ (x :: ·)) id) ys = xs.foldl (flip List.cons) ys := by
  induction xs generalizing ys with
  | nil => rfl
  | cons z zs ih =>
    exact ih (z :: ys)

example (xs : List ℕ) : expression₁ xs = reverse xs := by
  exact expression₁_eq_reverse_aux id xs []

example (xs : List ℕ) : expression₂ xs = reverse xs := by
  exact expression₂_eq_reverse_aux xs []


/-- # Exercise 5.11 -/

structure Card where
 suit : Char
 rank : Char
 deriving Repr

instance : Ord Card where
 compare a b :=
  let posn seq r := seq.toList.findIdx (· = r)
  (compareOn (posn "SHDC" ·.suit) a b).then
  (compareOn (posn "AKQJT98765432" ·.rank) a b)


/-- # Exercise 5.12

    sortBy é uma função de ordenação de listas parametrizada pela função de
    comparação. Precisamos adaptar merge para então basicamente renomear
    S52.msort₃ para sortBy parametrizando pela função de comparação.

    Como em Haskell, `compare` é definida para todo tipo instância de `Ord`.
    A função `compareOn` é equivalente a `comparing` do livro.

-/

def merge₁ (f : a → a → Ordering) : List a → List a → List a
 | [], ys => ys
 | xs, [] => xs
 | (x :: xs), (y :: ys) =>
   if f x y = Ordering.lt then
    x :: merge₁ f xs (y :: ys)
   else
    y :: merge₁ f (x :: xs) ys

open Chapter1 (wrap unwrap single until') in
open Mergesort in

def sortBy (f : a → a → Ordering) : List a → List a
 | []    => []
 | x::xs =>
   unwrap (until' single (pairWith (merge₁ f)) (List.map wrap (x::xs))) |>.getD []


def sortOn₁ [Ord b] (f : a → b) : List a → List a :=
  sortBy (compareOn f)

def sortOn₂ [Ord b] (f : a → b) (xs : List a) : List a :=
  sortBy (compareOn Prod.fst) ((xs.map f).zip xs) |>.map Prod.snd

def sortOn₃ [Ord b] (f : a → b) : List a → List a :=
  List.map Prod.snd ∘ sortBy (compareOn Prod.fst) ∘ List.map (λ x => (f x, x))

/-
#eval sortOn₁ String.length ["aaa", "a", "aa", "aaaaaa", "aaaa"]

#eval sortOn₂ (fun s => dbg_trace "fun {s}"
    match s.toList with
    | x :: y :: [] => Card.mk x y
    | _ => Card.mk ' ' ' ')
  ["H2","CA","CT","C7","C2", "SA","SQ","S9","S8",
   "S2","HK","H5","H3"]
-/

/- # Exercicio 5.13 -/

namespace Heapsort

def split [Inhabited a] [LE a] [DecidableRel (α := a) (· ≤ ·)]
 : List a → (a × List a × List a)
 | []      => (default, [], [])
 | x :: xs =>
   let op x acc :=
    if x ≤ acc.1
    then (x, acc.1 :: acc.2.2, acc.2.1)
    else (acc.1, x :: acc.2.2, acc.2.1)
   xs.foldr op (x, [], [])

/-- Nn `split₁` the `where` makes `op` visible from outside.
    In `split`, `let` is defined only in the second equation of
    the pattern match. `let rec` would make `op` also visible.

    If `op` is not visible, in the `split_left_le` we would need
    `lift_lets ; intro op` -/

def split₁ [Inhabited a] [LE a] [DecidableRel (α := a) (· ≤ ·)]
 : List a → (a × List a × List a)
 | []      => (default, [], [])
 | x :: xs =>
   xs.foldr op (x, [], [])
 where op x acc :=
  if x ≤ acc.1
  then (x, acc.1 :: acc.2.2, acc.2.1)
  else (acc.1, x :: acc.2.2, acc.2.1)


theorem split_left_le [Inhabited a] [LE a] [DecidableRel (α := a) (· ≤ ·)]
 (xs : List a) : (split₁ xs).2.1.length ≤ xs.length := by sorry

partial def mkHeap [Inhabited a] [LE a] [DecidableRel (α := a) (· ≤ ·)]
 : List a → Tree a
 | []      => Tree.null
 | x :: xs =>
   let p := split (x :: xs)
   Tree.node p.1 (mkHeap p.2.1) (mkHeap p.2.2)

end Heapsort


/- # Exercicio 5.15 -/

namespace Heapsort

def mkPair₀ : Nat → (List a) → (Tree a × List a)
  | _, [] => (Tree.null, [])
  | n, x :: xs =>
    if h₁ : n = 0 then
     (Tree.null, x :: xs)
    else
     let m := (n - 1) / 2
     let l_ys := mkPair₀ m xs
     let r_zs := mkPair₀ (n - 1 - m) l_ys.2
     (Tree.node x l_ys.1 r_zs.1, r_zs.2)

/-- this is not necessary. Keeping only to preserve the proofs. -/
def mkPair : Nat → (List a) → (Tree a × List a)
  | _, [] => (Tree.null, [])
  | n, x :: xs =>
    if h₁ : n = 0 then (Tree.null, x :: xs) else
      let m := (n - 1) / 2
      have h₂ : m < n := by
        have h₃ := Nat.ne_zero_iff_zero_lt.mp h₁
        rw [Nat.div_lt_iff_lt_mul Nat.zero_lt_two]
        calc
          n - 1 < n := Nat.sub_one_lt_of_lt h₃
          _ < n + n := Nat.lt_add_of_pos_right h₃
          _ = n * 2 := Eq.symm (Nat.mul_two n)
      let y := mkPair m xs
      have : (n - 1 - m) < n := by exact Nat.sub_one_sub_lt_of_lt h₂
      let z := mkPair (n - 1 - m) y.snd
      (Tree.node x y.fst z.fst, z.snd)

def mkTree (xs : List a) : Tree a := (mkPair₀ xs.length xs).1


end Heapsort


/- # Exercicio 5.17 : qual a complexidade? -/

open List (replicate) in
open Function (uncurry) in

def csort (m : Nat) (xs : List Nat) : List Nat :=
  let a := Chapter3.accumArray Nat.add 0 (0,m) (xs.map (·, 1))
  a.toList.flatMap (uncurry replicate)


/- # Exercicio 5.18

   Prova da propriedade de estabilidade do Bucketsort (5.3)

     map (bsort ds) (ptn d xs) = ptn d (bsort ds xs)

   usando a definição original de `bsort₀` como a função que achata
   uma árvore. As afirmações auxiliares do enunciado são (5.4), (5.5)
   e (5.6), provadas abaixo nessa ordem inversa de dependência.
-/

namespace Bucketsort

/- As mesmas hipóteses sobre `β` declaradas em `Chapter5.Bucketsort`:
   `ptn₀` e `mkTree` as exigem, embora as provas abaixo dependam
   apenas da igualdade. Daí os `omit` adiante. -/

variable {α : Type}
variable {β : Type} [BEq β] [LT β] [DecidableRel (α := β) (· < ·)]

/-- `tmap`, pedido no enunciado, necessário para (5.4) e (5.5). -/
def tmap {γ : Type} (f : α → γ) : Tree α → Tree γ
| .leaf x  => .leaf (f x)
| .node ts => .node (ts.map (tmap f))

/-- Filtros de predicados totais comutam. Assumido pelo enunciado,
    mas a prova é imediata. -/
theorem filter_comm (p q : α → Bool) (xs : List α) :
  (xs.filter p).filter q = (xs.filter q).filter p := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.filter_cons]
    split <;> split <;> simp_all

omit [LT β] [DecidableRel (α := β) (· < ·)] in
/-- (5.6) : `ptn₀ d ∘ filter p = map (filter p) ∘ ptn₀ d` -/
theorem ptn_filter_comm
  (rng : List β) (d : α → β) (p : α → Bool) (xs : List α) :
  List.map (List.filter p) (ptn₀ rng d xs) = ptn₀ rng d (xs.filter p) := by
  simp [ptn₀]
  intro a _
  apply List.filter_congr
  intro x _
  rw [Bool.and_comm]

omit [LT β] [DecidableRel (α := β) (· < ·)] in
/-- (5.4) : `mkTree ds ∘ filter p = tmap (filter p) ∘ mkTree ds` -/
theorem mkTree_filter_comm
  (rng : List β) (ds : List (α → β)) (p : α → Bool) :
  (mkTree rng ds) ∘ (List.filter p) = tmap (List.filter p) ∘ (mkTree rng ds) := by
  induction ds with
  | nil =>
    funext xs
    simp [mkTree, tmap]
  | cons d ds ih =>
    funext xs
    simp [mkTree]
    rw [← ptn_filter_comm]
    simp [ih, tmap, List.map_map]

theorem map_filter_flatten_eq_filter_flatten
  (p : α → Bool) (xss : List (List α)) :
  (List.map (List.filter p) xss).flatten = List.filter p xss.flatten := by
  simp [List.filter_flatten]

/-- Medida usada para a indução forte em (5.5): `Tree.flatten` e `tmap`
    recorrem sobre os filhos via `List.map`, e não estruturalmente. -/
def Tree.size : Tree α → Nat
| .leaf _  => 1
| .node ts => 1 + (ts.map Tree.size).sum

theorem size_lt_of_mem (t : Tree α) (ts : List (Tree α))
    (h : t ∈ ts) : t.size < (Tree.node ts).size := by
  simp only [Tree.size]
  induction ts with
  | nil => contradiction
  | cons t' ts ih =>
    simp only [List.map, List.sum_cons]
    simp [List.mem_cons] at h
    cases h with
    | inl h_eq =>
      simp [h_eq]
      rw [Nat.add_comm]
      apply Nat.lt_succ_of_le
      apply Nat.le_add_right
    | inr h_tail =>
      have h₁ : t.size < 1 + (ts.map Tree.size).sum := by simp [ih, h_tail]
      apply Nat.lt_of_lt_of_le h₁
      apply Nat.add_le_add_left
      exact Nat.le_add_left _ _

/-- (5.5) : `flatten ∘ tmap (filter p) = filter p ∘ flatten` -/
theorem flatten_tmap_filter (p : α → Bool) (t : Tree (List α)) :
  (tmap (List.filter p) t).flatten = List.filter p t.flatten := by
  induction h : t.size using Nat.strong_induction_on generalizing t with
  | h k ih =>
    cases t with
    | leaf xs => simp [Tree.flatten, tmap]
    | node ts =>
      simp only [Tree.flatten, tmap]
      rw [← map_filter_flatten_eq_filter_flatten]
      congr 1
      simp only [List.map_map]
      apply List.map_congr_left
      intro t' h'
      apply ih t'.size
      · rw [← h] ; exact size_lt_of_mem t' ts h'
      · rfl

theorem flatten_tmap_filter_comp (p : α → Bool) :
  Tree.flatten ∘ tmap (List.filter p) = List.filter p ∘ Tree.flatten (α := α) := by
  funext t ; exact flatten_tmap_filter p t

omit [LT β] [DecidableRel (α := β) (· < ·)] in
/-- (5.3) : a estabilidade do Bucketsort. -/
theorem bsort_ptn_comm
  (rng : List β) (ds : List (α → β)) (d : α → β) (xs : List α) :
  List.map (bsort₀ rng ds) (ptn₀ rng d xs) = ptn₀ rng d (bsort₀ rng ds xs) := by
  simp [bsort₀, ptn₀]
  intro a _
  rw [← Function.comp_apply (f := mkTree rng ds), mkTree_filter_comm,
      Function.comp_apply (g := mkTree rng ds), flatten_tmap_filter]

/-- `Chapter1.concatMap`, usado por `bsort₁`, é `flatten ∘ map`. -/
theorem concatMap_eq_flatten_map {γ : Type} (f : α → List γ) (xs : List α) :
  Chapter1.concatMap f xs = (xs.map f).flatten := by
  simp [Chapter1.concatMap, Chapter1.concat₁]
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

omit [LT β] [DecidableRel (α := β) (· < ·)] in
/-- `bsort₀`, que achata a árvore, e `bsort₁`, que se define por
    recursão direta, coincidem. -/
theorem bsort₀_eq_bsort₁ (rng : List β) (ds : List (α → β)) :
  bsort₀ rng ds = bsort₁ rng ds := by
  induction ds with
  | nil =>
    funext xs
    simp [bsort₀, bsort₁, mkTree, Tree.flatten]
  | cons d ds ih =>
    funext xs
    simp [bsort₀, mkTree, Tree.flatten, bsort₁, concatMap_eq_flatten_map]
    rw [← ih]
    congr 1

omit [LT β] [DecidableRel (α := β) (· < ·)] in
/-- O resultado central da seção 5.4: o Radixsort, que percorre os
    dígitos do menos significativo para o mais, calcula o mesmo que o
    Bucketsort. É aqui que (5.3) é usada. -/
theorem rsort₀_eq_bsort₁ (rng : List β) (ds : List (α → β)) :
  rsort₀ rng ds = bsort₁ rng ds := by
  induction ds with
  | nil =>
    funext xs
    simp [rsort₀, bsort₁]
  | cons d ds ih =>
    funext xs
    simp [rsort₀, bsort₁, concatMap_eq_flatten_map]
    rw [← bsort₀_eq_bsort₁] at ih
    rw [← bsort₀_eq_bsort₁, bsort_ptn_comm, ih]

end Bucketsort


/- # Exercicio 5.19 -/

def filter : (α → Bool) → List α → List α
  | _, [] => []
  | p, x::xs => if p x then (x :: filter p xs) else (filter p xs)

def remove_empty : List (List α) → List (List α)
  | [] => []
  | []::xs => remove_empty xs
  | x::xs => x :: remove_empty xs

def string_ptn : (String → Char) → List String → List (List String)
  | _, [] => []
  | f, x::xs =>
    let ms := "Aabcdefghijklmnopqrstuvwxyz".toList
    remove_empty (ms.map (fun m => filter (fun y => decide (f y = m)) (x::xs)))

-- #eval string_ptn (flip String.get ⟨0⟩) ["abc", "def", "ghi", "acb"]

def lists_concat : List (List α) → List α
  | [] => []
  | x::xs => x ++ (lists_concat xs)

def string_rsort : List (String → Char) → List String → List String
  | _, [] => []
  | [], xs => xs
  | f::fs, xs => lists_concat (string_ptn f (string_rsort fs xs))

def string_incresing_order : Nat → List (String → Char)
  | sz => ((List.range sz).map (fun x => flip String.Pos.Raw.get ⟨x⟩))


-- #eval string_rsort (string_incresing_order 3) ["abc", "ghi"]


end Chapter5
