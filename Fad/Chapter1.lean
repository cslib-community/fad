import Mathlib.Tactic.Cases         -- induction'
import Mathlib.Tactic.Use           -- use
import Mathlib.Tactic.Set           -- set
import Mathlib.Tactic.Conv          -- conv_lhs
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Induction  -- List.reverseRecOn
import Mathlib.Data.List.Infix      -- List.inits_append
import Mathlib.Data.List.MinMax     -- List.minimum / List.maximum
import Mathlib.Order.Defs.LinearOrder

namespace Chapter1

-- ## Section 1.1 Basic types and functions

def map₁ {a b} (f : a → b) (xs : List a) : List b :=
 match xs with
 | [] => []
 | (x :: xs) => f x :: map₁ f xs

def map {a b} (f : a → b) : List a → List b
| [] => []
| (x :: xs) => f x :: map f xs

example : map (· * 10) [1, 2, 3] = [10,20,30] :=
  rfl

theorem map_equal {α β} (a : List α) (f : α → β)
 : map f a = List.map f a := by
 induction a with
 | nil => rfl
 | cons a as ih =>
   simp [List.map, map]
   rw [ih]

def makeInc (n : Nat) : (Nat → Nat) :=
  fun x => x + n

/--
info: 55
-/
#guard_msgs in
#eval (makeInc 10) 45

def filter {a : Type} (p : a → Bool) : List a → List a
| [] => []
| x :: xs => if p x then x :: filter p xs else filter p xs

example : filter (· > 5) [1,4,5,8,6] = [8,6] := rfl

/--
info: [1, 3, 5, 7, 9]
-/
#guard_msgs in
#eval filter (· % 2 ≠ 0) (List.range 10)

def foldr {a b : Type} (f : a → b → b) (e : b) : List a → b
| []      => e
| x :: xs => f x (foldr f e xs)

/--
info: 6
-/
#guard_msgs in
#eval foldr (λ x y => x + y) 0 [1,2,3]

example : foldr Nat.add 0 [1,2,3] = 6 := by
 unfold foldr
 unfold foldr
 unfold foldr
 unfold foldr
 rw [Nat.add]


example {α} : ∀ xs : List α, foldr List.cons [] xs = xs := by
  intro xs
  induction xs with
  | nil =>
    rewrite [foldr.eq_1]
    rfl
  | cons a as ih =>
    rewrite [foldr]
    rewrite [ih]
    rfl


def label {α : Type} (xs : List α) : List (Nat × α) :=
  List.zip (List.range xs.length) xs

def length₁ (xs : List a) : Nat :=
  foldr (fun _ y => y + 1) 0 xs

def length₂ : List α → Nat :=
  let aux (_ : α) (n : Nat) : Nat := n + 1
  foldr aux 0

def sum (as : List Nat) : Nat :=
  foldr Nat.add 0 as

def sum₁ : List Nat → Nat :=
  foldr Nat.add 0

def foldl {a b : Type} (f : b → a → b) (e : b) : List a → b
| []      => e
| x :: xs => foldl f (f e x) xs

def foldl₀ {a b : Type} (f : b → a → b) (e : b) : List a → b :=
  foldr (flip f) e ∘ List.reverse

def foldl₁ {a b : Type} (f : b → a → b) (e : b) (xs : List a) : b :=
  foldr (flip f) e xs.reverse


example {a b : Type} (f : b → a → b) (e : b) (xs : List a)
 : foldl f e xs = foldl₁ f e xs := by
 unfold foldl₁
 induction xs generalizing e with
 | nil =>
   rw [List.reverse, foldl]; simp
   rw [foldr]
 | cons r rs ih₁ =>
   rw [List.reverse]
   simp
   rw [foldl]
   rw [ih₁ (f e r)]
   induction rs.reverse with
   | nil =>
     simp [foldr, flip]
   | cons z zs ih₂ =>
     simp [foldr, flip]
     simp [ih₂]


-- ## Section 1.2 Processing lists

structure Point where
  x : Float
  y : Float
deriving Repr

instance : Inhabited Point where
 default := Point.mk 0 0

def head {α : Type} [Inhabited α] : List α → α :=
  let f x _ := x
  List.foldr f default

def head₁ {α : Type} : List α → Option α :=
  let f x _ := some x
  List.foldr f none


def concat₁ {a : Type} : List (List a) → List a :=
 List.foldr List.append []

def concat₂ {a : Type} : List (List a) → List a :=
 List.foldl List.append []

example : concat₁ [[1,2], [5], [6]] = [1,2,5,6] := by
  unfold concat₁
  unfold List.foldr
  unfold List.foldr
  unfold List.foldr
  unfold List.foldr
  rw [List.append.eq_2]
  rw [List.append.eq_2]
  rw [List.append.eq_2]
  rw [List.append.eq_2]
  rw [List.append.eq_1]
  rw [List.append.eq_1]
  rw [List.append.eq_1]

example : concat₂ [[1,2], [5], [6]] = [1,2,5,6] := by
  unfold concat₂
  unfold List.foldl
  unfold List.foldl
  unfold List.foldl
  unfold List.foldl
  rw [List.append.eq_1]
  rw [List.append.eq_2]
  rw [List.append.eq_2]
  rw [List.append.eq_2]
  rw [List.append.eq_2]
  rw [List.append.eq_1]
  rw [List.append.eq_2]
  rw [List.append.eq_1]


def scanl {b a} (f : b → a → b ) : b → List a → List b
| e, [] => [e]
| e, (x :: xs) => e :: scanl f (f e x) xs


/-
ghci> foldl (+) 0 (take 5 [1..])
15
ghci> foldr (+) 0 (take 5 [1..])
15
ghci> take 5 (scanl (+) 0 [1..])
[0,1,3,6,10]

#eval scanl Nat.add 0 [1,2,3,4]
#eval scanl Nat.add 42 []
#eval scanl (λ r n => n :: r)
  "foo".toList ['a', 'b', 'c', 'd'] |>.map List.asString
-/

def scanr₀ {a b : Type} (f : a → b → b) (q₀ : b) (as : List a) : List b :=
 let rec aux : List a → {l : List b // l ≠ []}
  | [] => Subtype.mk [q₀] (by simp)
  | (x :: xs) =>
    let qs := aux xs
    Subtype.mk (f x (List.head qs qs.property) :: qs) (by simp)
 aux as

def scanr {a b} (f : a → b → b) : b → List a → List b
| e, [] => [e]
| e, (x :: xs) =>
  match scanr f e xs with
  | [] => []
  | qs@(q :: _) => f x q :: qs

/--
info: true
-/
#guard_msgs in
#eval scanr₀ Nat.add 0 [1,2,3] = [1, 2, 3].scanr Nat.add 0


-- ## Section 1.3 Inductive and recursive definitions

def inserts {a} (x : a) : List a → List (List a)
| []      => [[x]]
| y :: ys => (x :: y :: ys) :: map (y :: ·) (inserts x ys)

def concatMap {a b} (f : a → List b) : List a → List b :=
 concat₁ ∘ (List.map f)


/- Next, we have four recursive definitions of perm1. -/

def perms1₁ {a} : List a → List (List a)
 | [] => [[]]
 | x :: xs =>
   concat₁ <| (perms1₁ xs).map (inserts x ·)

def perms1₂ {a} : List a → List (List a)
 | [] => [[]]
 | (x :: xs) => (perms1₂ xs).flatMap (inserts x ·)

def perms1₃ {a} : List a → List (List a) :=
 foldr step [[]]
 where
  step x := List.flatMap (inserts x)

def perms1₄ {a} : List a → List (List a) :=
  foldr (List.flatMap ∘ inserts) [[]]


def picks {a} : List a → List (a × List a)
| []      => []
| x :: xs =>
  (x, xs) :: ((picks xs).map (λ p => (p.1, x :: p.2)))


/--
`partial` because Lean cannot verify termination: `p` comes from `concatMap`
with no proof that `p ∈ picks xs`, so `p.2.length < xs.length` is unknown.
-/
partial def perms2₁ {a : Type} : List a → List (List a)
  | [] => [[]]
  | xs =>
    let subperms p := (perms2₁ p.2).map (p.1 :: ·)
    concatMap subperms (picks xs)


theorem picks_decreases {a : Type} (xs : List a)
 : ∀ p, p ∈ picks xs → p.2.length < xs.length := by
 induction xs with
 | nil => intro p h; cases h
 | cons x xs ih =>
   intro p h
   simp [picks] at h
   rcases h with rfl | ⟨q, hq, hmem, rfl⟩
   · simp
   · simp [ih (q, hq) hmem]


/-- Uses `List.attach` to pair each element with its membership proof, then
    pattern-matches on `⟨p, hp⟩` to obtain `hp : p ∈ picks xs` inline. -/
def perms2₂ {a : Type} : List a → List (List a)
  | [] => [[]]
  | xs => concatMap (λ ⟨p, hp⟩ ↦
      have : p.2.length < xs.length := by
        apply picks_decreases xs
        exact hp
      (perms2₂ p.2).map (p.1 :: ·))
      (picks xs).attach
termination_by xs => xs.length


def picks₁ {a} : (xs : List a) → List { r : a × List a // r.2.length < xs.length }
| []      => []
| x :: xs =>
  let rs := picks₁ xs
  ⟨(x, xs), by grind⟩ :: (picks₁ xs).map
    (λ r => ⟨(r.val.1, x :: r.val.2), by grind⟩)

def perms2₄ {a : Type} : List a → List (List a)
  | [] => [[]]
  | xs => concatMap (λ ⟨p, _hp⟩ ↦
      (perms2₄ p.2).map (p.1 :: ·))
      (picks₁ xs)
termination_by xs => xs.length


/--
 Avoids `attach` by using an explicit helper `go` that threads the membership
 proof `∀ p, p ∈ ps → p.2.length < xs.length` through the recursion. Requires a
 lexicographic termination measure `(xs.length, ps.length)`.  -/
def perms2₅ {a : Type} : List a → List (List a)
  | [] => [[]]
  | xs =>
    let rec go : (ps : List (a × List a)) →
      (∀ p, p ∈ ps → p.2.length < xs.length) → List (List a)
     | [], _ => []
     | p :: ps, h =>
        have _hp := h p List.mem_cons_self
        (perms2₅ p.2).map (p.1 :: ·)
        ++ go ps (fun q hq => h q (List.mem_cons_of_mem _ hq))
      termination_by ps => (xs.length, ps.length)
    go (picks xs) (picks_decreases xs)
termination_by xs => (xs.length, (picks xs).length + 1)


partial def until' {a} (p : a → Bool) (f : a → a) (x : a) : a :=
  if p x then x
  else until' p f (f x)

partial def while' {a} (p : a → Bool) :=
  until' (not ∘ p)


-- ## Section 1.4 Fusion

theorem map_map {α β γ : Type} (f : β → γ) (g : α → β) :
  List.map f ∘ List.map g = List.map (f ∘ g) := by
  funext as
  induction as with
  | nil => rfl
  | cons x xs ih =>
    simp [List.map]


theorem concatMap_map {α β : Type} (f : α → List β) (g : β → α) :
  concatMap f ∘ List.map g = concatMap (f ∘ g) := by
  funext as
  induction as with
  | nil => rfl
  | cons x xs ih => simp [concatMap]


theorem foldr_map {α β : Type} (f : α → β → β) (e : β) (g : β → α) :
  List.foldr f e ∘ List.map g = List.foldr (f ∘ g) e := by
  funext as
  induction as with
  | nil => rfl
  | cons x xs ih =>
    simp [List.map, List.foldr]
    rw [← ih]
    rw [Function.comp]


theorem foldr_fusion {a b c : Type}
 (f : a → c → c) (e : c) (xs : List a)
 (g : a → b → b) (h : c → b)
 (h₁ : ∀ x y, h (f x y) = g x (h y))
 : h (List.foldr f e xs) = List.foldr g (h e) xs := by
 induction xs with
  | nil => rfl
  | cons x xs ih =>
    rewrite [List.foldr]
    rewrite [h₁ x (List.foldr f e xs)]
    rewrite [ih]
    rfl


example {a b : Type} (xs ys : List a) (f : a → b → b) (e : b)
 : List.foldr f e (xs ++ ys) = List.foldr f (List.foldr f e ys) xs
 := by
 have h₁ : xs ++ ys = List.foldr List.cons ys xs := by simp
 rw [h₁]
 let g := f
 let h := List.foldr f e
 let f₁ := List.cons (α := a)
 let e₁ := ys
 apply foldr_fusion f₁ e₁ xs g h
 intro z zs
 simp [h, g, f₁]


example {a b : Type} (f : a → b → b) (e : b)
  : List.foldr f e ∘ concat₁ = List.foldr (flip (List.foldr f)) e
  := by
  funext xss
  let f₁ := List.append (α := a)
  let e₁ : List a := []
  let g : List a → b → b := flip (List.foldr f)
  let h : List a → b := List.foldr f e
  rw [Function.comp, concat₁]
  apply foldr_fusion f₁ e₁ xss g h
  intro xs ys
  simp [f₁, h, g, flip]


example {α β} {f : α → β} {p : α → Bool}
  : List.map f ∘ List.filter p ∘ List.flatten = List.flatMap (List.map f ∘ List.filter p)
  := by
  funext xs
  induction' xs with a as ih
  all_goals grind

theorem foldl_comp {α β: Type} (y: α) (e : β) (f : β → α → β):
 List.foldl f e ∘ (fun x => y :: x) = List.foldl f (f e y) := by rfl


-- ## Seciton 1.5 Accumulating and tupling

-- `where` notation has some limitations ask-lean-fro

def collapse₀ (xss : List (List Int)) : List Int :=
  let rec help (xs : List Int) (xss : List (List Int)) : List Int :=
    if h : xs.sum > 0 ∨ xss.isEmpty
    then xs
    else
      have h₁ : xss ≠ [] := by
        simp at h
        intro contra
        exact h.right contra
      help (xs.append $ xss.head h₁) xss.tail
  termination_by xss.length
  decreasing_by
    simp
    refine Nat.sub_one_lt ?_
    grind
  help [] xss


def collapse₁ (xss : List (List Int)) : List Int :=
 help [] xss
 where
  help : List Int → List (List Int) → List Int
  | xs, [] => xs
  | xs, (as :: bss) =>
    if xs.sum > 0 then xs
    else help (xs.append as) bss

def collapse₂ (xss : List (List Int)) : List Int :=
  help (0, []) (labelsum xss)
  where
   labelsum (xss : List (List Int)) : List (Int × List Int) :=
     List.zip (map List.sum xss) xss
   help : (Int × List Int) → List (Int × List Int) → List Int
   | (_, xs), [] => xs
   | (s, xs), as :: bss =>
     if s > 0
     then xs
     else help (cat (s, xs) as) bss
   cat a b := (a.1 + b.1, a.2 ++ b.2)


def collapse₃ (xss : List (List Int)) : List Int :=
  let labelsum (xss : List (List Int)) :=
    List.zip (map List.sum xss) xss
  let tf := List Int → List Int
  let rec help : (Int × tf) → List (Int × List Int) → tf
    | (_, f), [] => f
    | (s, f), (as :: bs) =>
      if s > 0 then f
      else help (s + as.1, f ∘ (as.2 ++ ·)) bs
  help (0, id) (labelsum xss) []


private lemma collapse₀_eq_collapse₁ : collapse₀ = collapse₁ := by
  funext xss
  simp only [collapse₀, collapse₁]
  suffices h : ∀ xs, collapse₀.help xs xss = collapse₁.help xs xss by exact h []
  intro xs
  induction xss generalizing xs with
  | nil =>
    unfold collapse₀.help collapse₁.help
    simp
  | cons as bss ih =>
    unfold collapse₀.help collapse₁.help
    by_cases hpos : xs.sum > 0
    · simp [hpos]
    · simp only [hpos, ↓reduceIte, List.isEmpty, List.tail, List.head]
      exact ih _

-- The invariant needs f = (xs ++ ·) pointwise, not just f [] = xs,
-- because the recursive step applies f to `as` (not just []).
private lemma collapse₁_help_eq (xss : List (List Int))
  : ∀ (xs : List Int) (s : Int) (f : List Int → List Int),
      s = xs.sum → (∀ ys, f ys = xs ++ ys) →
      collapse₁.help xs xss =
        collapse₃.help (s, f) (List.zip (map List.sum xss) xss) [] := by
  induction xss with
  | nil =>
    intros xs s f _ hf
    simp [collapse₁.help, collapse₃.help, hf]
  | cons as bss ih =>
    intros xs s f hs hf
    simp only [collapse₁.help, collapse₃.help, map, List.zip, List.zipWith]
    by_cases hpos : xs.sum > 0
    · have hs2 : s > 0 := hs ▸ hpos
      simp [hpos, hs2, hf]
    · have hs2 : ¬ s > 0 := hs ▸ hpos
      simp only [hpos, hs2]
      apply ih
      · simp [hs, List.sum_append]
      · intro ys; simp [hf, List.append_assoc]

private lemma collapse₁_eq_collapse₃ : collapse₁ = collapse₃ := by
  funext xss
  simp only [collapse₁, collapse₃]
  exact collapse₁_help_eq xss [] 0 ([] ++ ·) (by simp) (by simp)

example : collapse₀ = collapse₃ := by
  rw [collapse₀_eq_collapse₁, collapse₁_eq_collapse₃]


end Chapter1
