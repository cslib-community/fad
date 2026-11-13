import Fad.Chapter6
import Fad.Chapter7

namespace Chapter7

/-!
# Exercises
-/

/-!
## Exercise 7.1
The `Data.List` library provides a function
  `minimumBy : (a → a → Ordering) → [a] → a`
Define `minWith` using `minimumBy`.
-/

def minimumBy {α : Type} (cmp : α → α → Ordering) : List α → Option α
  | []      => none
  | x :: xs =>
    some (xs.foldr (λ y r => cond (cmp y r = Ordering.lt) y r) x)

def minWith₁ {α β : Type} [Ord β] (f : α → β) (xs : List α) : Option α :=
  let helper (x y : α) : Ordering := compare (f x) (f y)
  minimumBy helper xs

def minWith₂ {α β : Type} [Ord β] (f : α → β) (xs : List α) : Option α :=
  let tuple (x : α) : β × α := (f x, x)
  let cmp (x y : β × α) := compare x.1 y.1
  minimumBy cmp (xs.map tuple) >>= (λ pair => some pair.2)

instance : Ord Float where
  compare x y :=
    if x < y then Ordering.lt
    else if x == y then Ordering.eq
    else Ordering.gt


/-!
## Exercise 7.2
Write down a definition of a function `minsWith f` that returns all the
elements of a finite nonempty list that minimise `f`. In particular the
statement `x ← MinWith f xs` can be read as `x ∈ minsWith f xs`.
-/

def minsWith {α β : Type} [Ord β] (f : α → β) (xs : List α) : List α :=
  let step (x : α) (ys : List α) : List α :=
    match ys with
    | [] => [x]
    | y :: ys =>
      match compare (f x) (f y) with
      | Ordering.lt => [x]
      | Ordering.eq => x :: y :: ys
      | Ordering.gt => y :: ys
  xs.foldr step []

def minsWith' {α β : Type} [Ord β] (f : α → β) (xs : List α) : List α :=
  let step (x : β × α) (ys : List (β × α)) :=
    match ys with
    | [] => [x]
    | y :: ys =>
      match compare (x.fst) (y.fst) with
      | Ordering.lt => [x]
      | Ordering.eq => x :: y :: ys
      | Ordering.gt => y :: ys
  xs.map tuple |>.foldr step [] |>.map (·.snd)
    where tuple x := (f x, x)


/-!
## Exercise 7.3
Prove that, if `f` is associative, then
  `foldr1 f (xs ++ ys) = f (foldr1 f xs) (foldr1 f ys)`
for all nonempty lists `xs` and `ys`. Hence show that
  `foldr1 f (concat xss) = foldr1 f (map (foldr1 f) xss)`
provided `xss` contains only nonempty lists. Finally, show that
  `minWith f (concat xss) = minWith f (map (minWith f) xss)`
provided `xss` contains only nonempty lists.
-/
section
open Chapter6 (foldr1)
open Chapter1 (concat₁)

theorem foldr1_append {a : Type} [Inhabited a]
  (xs ys : List a) (f : a → a → a) (h_assoc : ∀ x y z, f (f x y) z = f x (f y z))
  : xs ≠ [] ∧ ys ≠ [] → foldr1 f (xs ++ ys) = f (foldr1 f xs) (foldr1 f ys) := by
  intro ⟨h1, h2⟩
  induction xs with
  | nil => contradiction
  | cons b bs ih =>
    match ys with
    | [] => contradiction
    | z :: zs =>
      match bs with
      | [] => simp [foldr1]
      | w :: ws =>
        simp at ih
        simp [ih, foldr1, h_assoc]

theorem foldr1_concat₁ {a : Type} [Inhabited a]
  (xss : List (List a)) (f : a → a → a) (h_assoc : ∀ x y z, f (f x y) z = f x (f y z))
  : xss ≠ [] ∧ (∀ xs ∈ xss, xs ≠ []) →
    foldr1 f (concat₁ xss) = foldr1 f (xss.map (foldr1 f)) := by
  intro ⟨h1, h2⟩
  induction xss with
  | nil => contradiction
  | cons ys yss ih =>
    simp at h2
    obtain ⟨h2, h3⟩ := h2
    simp_all
    match yss with
    | [] => simp [concat₁, foldr1]
    | zs :: zss =>
      simp_all [concat₁, foldr1]
      obtain ⟨h3, h4⟩ := h3
      rw [foldr1_append _ _ _ h_assoc ⟨h2, (by simp_all)⟩, ih]

theorem minWith_concat₁ {a b : Type} [Inhabited a] [LinearOrder b]
  (xss : List (List a)) (f : a → b)
  : xss ≠ [] ∧ (∀ xs ∈ xss, xs ≠ []) →
    minWith f (concat₁ xss) = minWith f (xss.map (minWith f)) := by
  intro h
  simp_all [minWith]
  rw [foldr1_concat₁ xss _ (by intro a b c; grind) h]
  rfl

end

/-!
## Exercise 7.4
Write down a divide-and-conquer definition of `perms`.
-/

def interleave {α : Type} : List α → List α → List (List α)
| xs, []            => [xs]
| [], ys            => [ys]
| x :: xs, y :: ys  =>
  let l := interleave xs (y :: ys) |>.map (x :: ·)
  let r := interleave (x :: xs) ys |>.map (y :: ·)
  l ++ r

def cp {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=
 Chapter1.concatMap (λ x ↦ ys.map (λ y ↦ (x, y))) xs

def perms₁ {α : Type} : List α → List (List α)
| []  => [[]]
| [x] => [[x]]
| xs  =>
  let p := List.MergeSort.Internal.splitInTwo (Subtype.mk xs rfl)
  let yss := perms p.1
  let zss := perms p.2
  Chapter1.concatMap (Function.uncurry interleave) (cp yss zss)


/-!
## Exercise 7.5
Why is the law
  `minimum · map (x:) = (x:) · minimum`
not valid on empty lists?
-/

open Chapter6 (minimum)

example (x : Nat) : minimum [x] = x := by
  unfold minimum
  rewrite [Chapter6.foldr1]
  rfl

def min_list_list : List Nat → List Nat → List Nat
 | [], _  => []
 |  _, [] => []
 | xs@(a :: as), ys@(b :: bs) =>
   if      a < b then xs
   else if a > b then ys
   else
    a :: (min_list_list as bs)

instance : Min (List Nat) where
 min := min_list_list

example (x : Nat) : ∀ xs, xs ≠ [] →
 minimum (xs.map (x :: ·)) = (x :: ·) (minimum xs)
 := by
 intro xs h
 simp
 induction xs with
 | nil => contradiction
 | cons a as ih =>
   cases as with
   | nil => simp [minimum, Chapter6.foldr1]
   | cons z zs =>
     let f := min_list_list (x :: a)
     have h₁ : z :: zs ≠ [] := by simp
     have h₂ := ih h₁
     have h₃ := congrArg f h₂
     apply h₃.trans
     simp [f, min_list_list]
     rfl


/-!
## Exercise 7.6
Show that `minimum · map f = f · minimum` on nonempty lists if `f` is
monotonic. Is the monotonicity condition necessary?
-/

-- TODO

/-!
## Exercise 7.7
Given that `gstep x = minimum · extend x`, derive a recursive definition
of `gstep`.
-/

-- see Chapter7.lean

/-!
## Exercise 7.8
With `gstep` as defined in the previous question, show that
  `minimum (map (gstep x) xss) = gstep x (minimum xss)`
provided all lists in `xss` have the same length. Give an example to show the
condition fails if `xss` can contain lists of different length.
-/

-- TODO

/-!
## Exercise 7.9
Suppose `(x₁, ys₁)` and `(x₂, ys₂)` are two picks of the same list. Show
that
  `(x₁, ys₁) ≤ (x₂, ys₂) ⇒ x₁ : sort ys₁ ≤ x₂ : sort ys₂`
-/

-- TODO

/-!
## Exercise 7.10
Write down a linear-time algorithm for computing `pick`.
-/

def pick₂ : List Nat → Option (Nat × List Nat)
| []       => none
| [x]      => some (x, [])
| x :: xs  =>
  match pick₂ xs with
  | none => none
  | some (y, ys) =>
    if x ≤ y then some (x, xs) else some (y, x :: ys)


/-!
## Exercise 7.11
Consider evaluation of Insertion sort on the list `[3, 4, 2, 5, 1]`.
Keeping in mind that Haskell is a lazy language, continue the following sequence
of evaluation steps until the first element of the result is obtained:
  `gstep 3 (gstep 4 (gstep 2 (gstep 5 (gstep 1 []))))`
  `gstep 3 (gstep 4 (gstep 2 (gstep 5 (1 : []))))`
  `gstep 3 (gstep 4 (gstep 2 (1 : gstep 5 [])))`
Now answer the following questions. How long does it take to compute
`head · isort` on a nonempty list? What is the precise sequence of comparisons
made for sorting `[3, 4, 2, 5, 1]`? Does Insertion sort actually work by
inserting a new element into a sorted list at each step?
-/

-- TODO

/-!
## Exercise 7.12
Explain why `mkchange [7, 3, 1] 54 = [6, 4, 0]`, where
  `mkchange ds = minWith count · mktuples ds`
What change to the definition of `mktuples` would produce `[7, 1, 2]`?
-/

namespace S73

/- response: both have the same 'cost' (here 'sum') and
   'minWith' takes the first smallest from the list.
   If `mktuples` produces decreasing order, it would
   return the other `minimum`. -/

def mktuples' : List Denom → Nat → List Tuple
  | [1]    , n => [[n]]
  | []     , _ => panic! "mktuples: invalid empty list"
  | d :: ds, n =>
    let rs := List.range (n / d + 1)
    rs.flatMap (λ c => mktuples₀ ds (n - c * d) |>.map
     (λ cs => c :: cs))

def mkchange' (ds : List Denom) : Nat → Tuple :=
  minWith List.sum ∘ mktuples' ds

-- #eval mkchange₀ [7,3,1] 54
-- #eval mkchange' [7,3,1] 54

end S73

/-!
## Exercise 7.13
Here is the weight-based version of coin-changing:
  `type Weights = [Int]`
  `weight : Weights → Tuple → Int`
  `weight ws cs = sum (zipWith (×) ws cs)`
  `mkchangew : Weights → [Denom] → Nat → Tuple`
  `mkchangew ws ds = minWith (weight ws) · mktuples ds`
In the UK it is the case that minimising `count` also minimises `weight`. We
could prove this by simply carrying out an exhaustive test:
  `ukws = [1200, 950, 800, 500, 650, 325, 712, 356]`
  `test = [n | n ← [1..200], mkchange ukds n = mkchangew ukws ukds n]`
We only need to check amounts up to £2. But `test` returns a nonempty list
beginning with 2 because
  `mkchange ukds 2 = [0, 0, 0, 0, 0, 0, 1, 0]`
  `mkchangew ukws ukds 2 = [0, 0, 0, 0, 0, 0, 0, 2]`
One 2p coin weighs the same as two 1p coins. What has gone wrong, and how can
the test be corrected?
-/

-- TODO

/-!
## Exercise 7.14
Express the function `mktuples` as an instance of `foldr`. (Hint:
maintain a list of pairs, where a pair consists of a tuple and a residual
amount, and then at the end select the first component of a pair with a zero
residue.) Write down the associated greedy algorithm. We will use such a
definition when we come to discuss a thinning algorithm for the same problem.
-/

-- TODO

/-!
## Exercise 7.15
Consider the denominations `[5, 2, 1]` and a largest tuple
`[c₃, c₂, c₁]` with minimum count. Show that, if `2 c₂ + c₁ ≥ 5`, then there is
a larger tuple for the same amount but with a smaller count. If the
denominations were `[4, 3, 1]`, do we necessarily have `3 c₂ + c₁ < 4`?
-/

-- TODO

/-!
## Exercise 7.16
Consider the UR (United Region) currency whose denominations are
`[100, 50, 20, 15, 5, 2, 1]`. Explain carefully where the argument as to why the
greedy algorithm works for UK currency breaks down with UR currency. Does the
greedy algorithm work for UR currency?
-/

/-
   not clear how to prove formally
-/

namespace S73

def urds := [100, 50, 20, 15, 5, 2, 1]

/-
#eval mkchange₀ urds 30
#eval mkchange₁ urds 30
#eval mkchange  urds 30
#eval mkchange₀ [4,3,1] 6
#eval mkchange₁ [4,3,1] 6
-/

end S73

/-!
## Exercise 7.17
Prove that, if each denomination is a multiple of the next lower
denomination, then the greedy algorithm works.
-/

-- TODO

/-!
## Exercise 7.18
Prove (7.1) using the rule of floors.
-/

-- TODO

/-!
## Exercise 7.19
We calculated that
  `intern = halve · foldr shiftn 0`
Suppose `halve · foldr shiftn 0 = foldr op 0` for some function `op`. The
associated fusion condition is
  `halve (shiftn d n) = op d (halve n)`
for all `n` of the form `n = foldr shiftn 0 ds`. Using the rule of floors, we
have
  `halve (shiftn d n) = (2¹⁷ × d + n + 10) div 20`
Now, since `halve (2 × n) = halve (2 × n − 1)`, the fusion condition requires
that
  `(2¹⁷ × d + 2 × n + 10) div 20 = (2¹⁷ × d + 2 × n + 9) div 20`
Your task is to find a two-digit decimal `ds` with `n = foldr shiftn 0 ds` such
that the above statement is false for `d = 0`.
-/

-- TODO

/-!
## Exercise 7.20
Why can all but the first 17 digits of the input be ignored?
-/

-- TODO

/-!
## Exercise 7.21
Why does the first definition of `decimals` contain a bug? Hint: as we
said in the very first chapter, Haskell does not guarantee that the type `Int`
covers a greater range than `[−2²⁹, 2²⁹)`. Would the bug still occur if a
Haskell compiler allowed the range `[−2⁶³, 2⁶³)` for `Int`? Give the necessary
revisions of `decimals` and `externs` that solve the problem.
-/

-- TODO

/-!
## Exercise 7.22
For `n < 2¹⁶` the integer `D`, where
  `D = ⌊10⁵ × n / 2¹⁶ + 1/2⌋`
satisfies `D < 10⁵` and so has at most 5 digits. Using this fact, show that
`extern n` has at most 5 digits.
-/

-- TODO

/-!
## Exercise 7.23
To verify the distributive law for `MinWith cost`, we have to show that,
if `x ← MinWith (concat xss)`, then there exists a list `xs` such that
  `xs ← map (MinWith cost) xss  ∧  x ← MinWith cost xs`
Conversely, we also have to show
  `xs ← map (MinWith cost) xss  ∧  x ← MinWith cost xs`
  `    ⇒  x ← MinWith cost (concat xss)`
Prove these two claims.
-/

-- TODO

/-!
## Exercise 7.24
Suppose `MCC xs = MinWith cost (candidates xs)`. Show that
  `foldr gstep e xs ← MCC xs`
provided `e ← MCC []` and
  `c ← MCC xs ⇒ gstep x c ← MCC (x : xs)`
for all candidates `c`, components `x`, and lists of components `xs`.
-/

-- TODO

/-!
## Exercise 7.25
Define `Flip : Bool → Bool` by
  `Flip x = MinWith (const 0) [x, not x]`
Which of the following assertions are true?
  `id ← Flip`    `not ← Flip`    `not · not = not`    `Flip · Flip = Flip`
-/

-- TODO

end Chapter7
