
import Mathlib.Tactic
import Mathlib.Data.List.Sublists
import Fad.Chapter7

namespace Chapter10

open List
open Chapter7

-- ## Section 10.1 Theory

universe u

variable {a : Type u}
  [Inhabited a] [DecidableRel (α := a) (· = ·)]
  [Max a] [Min a]
  [LT a] [DecidableRel (α := a) (· < ·)]
  [LE a] [DecidableRel (α := a) (· ≤ ·)]

set_option linter.unusedSectionVars false

/-! ### Subsequences

`ys <+ xs` means that `ys` is a subsequence of `xs`.
The List.Sublist module will be really helpful.
-/

example : [1, 3] <+ [1, 2, 3] := by
  apply List.Sublist.cons_cons
  apply List.Sublist.cons
  apply List.Sublist.cons_cons
  apply List.Sublist.slnil


-- ### The predicate `ThinBy`

/-- `Dominates r ys xs` : every element of `xs` is dominated under `r` by some
    element of `ys`, i.e. `∀ x ∈ xs, ∃ y ∈ ys, y ⪯ x`. -/
def Dominates (r : a → a → Prop) (ys xs : List a) : Prop :=
  ∀ x ∈ xs, ∃ y ∈ ys, r y x

def ThinBy (r : a → a → Prop) (xs ys : List a) : Prop :=
  ys <+ xs ∧ Dominates r ys xs

@[simp] theorem mem_ThinBy {r : a → a → Prop} {xs ys : List a} :
    ThinBy r xs ys ↔ ys <+ xs ∧ Dominates r ys xs := by
    rfl

-- ### A linear-time implementation `thinBy`

/-- One step of `thinBy`, processing from the right. -/
def bump (le : a → a → Bool) (x : a) : List a → List a
  | []      => [x]
  | y :: ys =>
      match le x y, le y x with
      | true,  _     => x :: ys
      | false, true  => y :: ys
      | false, false => x :: y :: ys

/-- A sub-optimal, linear-time implementation of `ThinBy`. -/
def thinBy (le : a → a → Bool) : List a → List a :=
  List.foldr (bump le) []

theorem thinBy_nil (le : a → a → Bool) : thinBy le [] = [] := by
  rfl

theorem thinBy_cons (le : a → a → Bool) (z : a) (zs : List a) :
    thinBy le (z :: zs) = bump le z (thinBy le zs) := by
  rfl


-- ### Examples

/-- `(a,b) ⪯ (c,d) = (a ≥ c) ∧ (b ≤ d)`, as a `Bool` test on `ℕ × ℕ`. -/
def le₁ (p q : Nat × Nat) : Bool := decide (q.1 ≤ p.1 ∧ p.2 ≤ q.2)

/--
info: [(1, 2), (4, 3), (5, 4), (3, 1)]
-/
#guard_msgs in
#eval thinBy le₁ [(1,2),(4,3),(2,3),(5,4),(3,1)]

/--
info: [(3, 1), (4, 3), (5, 4)]
-/
#guard_msgs in
#eval thinBy le₁ [(1,2),(2,3),(3,1),(4,3),(5,4)]

/--
info: [(3, 1), (4, 3), (5, 4)]
-/
#guard_msgs in
#eval thinBy le₁ [(3,1),(1,2),(2,3),(4,3),(5,4)]


/-! ### `thinBy` refines `ThinBy` (correctness)

We prove that the concrete `thinBy` always returns a valid thinning, provided
the comparison is reflexive and transitive (i.e. a preorder). This splits into
the subsequence property and the domination property. -/

/-- `bump` preserves being a subsequence. -/
theorem bump_sublist (le : a → a → Bool) (z : a) {t zs : List a}
    (ht : t <+ zs) : bump le z t <+ z :: zs := by
  cases t with
  | nil =>
      simp only [bump]
      exact List.Sublist.cons_cons z (List.nil_sublist zs)
  | cons y ys =>
      have hys : ys <+ zs := (List.Sublist.cons y (List.Sublist.refl ys)).trans ht
      cases h1 : le z y <;> cases h2 : le y z <;> simp only [bump, h1, h2]
      · exact List.Sublist.cons_cons z ht     -- (false,false): z :: y :: ys
      · exact List.Sublist.cons z ht          -- (false,true):  y :: ys
      · exact List.Sublist.cons_cons z hys    -- (true,false):  z :: ys
      · exact List.Sublist.cons_cons z hys    -- (true,true):   z :: ys

/-- Every output of `thinBy` is a subsequence of the input. -/
theorem thinBy_sublist (le : a → a → Bool) :
    ∀ xs : List a, thinBy le xs <+ xs := by
  intro xs
  induction xs with
  | nil => exact List.Sublist.refl []
  | cons z zs ih =>
      rw [thinBy_cons]
      exact bump_sublist le z ih

/-- After a `bump`, the new element `z` is dominated by some element of the
    result. -/
theorem bump_dom_self (le : a → a → Bool) (hrefl : ∀ x, le x x = true)
    (z : a) (t : List a) : ∃ y ∈ bump le z t, le y z = true := by
  cases t with
  | nil => exact ⟨z, by simp [bump], hrefl z⟩
  | cons y ys =>
      cases h1 : le z y <;> cases h2 : le y z <;> simp only [bump, h1, h2]
      · exact ⟨z, by simp, hrefl z⟩       -- (false,false): z :: y :: ys
      · exact ⟨y, by simp, h2⟩            -- (false,true):  y :: ys
      · exact ⟨z, by simp, hrefl z⟩       -- (true,false):  z :: ys
      · exact ⟨z, by simp, hrefl z⟩       -- (true,true):   z :: ys

/-- A `bump` preserves domination of any element `w` that was already
    dominated by the accumulator. -/
theorem bump_dom_pres (le : a → a → Bool)
    (htrans : ∀ x y z, le x y = true → le y z = true → le x z = true)
    (z : a) (t : List a) (w : a) (h : ∃ y ∈ t, le y w = true) :
    ∃ y ∈ bump le z t, le y w = true := by
  obtain ⟨y₀, hy₀_mem, hy₀⟩ := h
  cases t with
  | nil => simp at hy₀_mem
  | cons y ys =>
      cases h1 : le z y <;> cases h2 : le y z <;> simp only [bump, h1, h2]
      · -- (false,false): bump = z :: y :: ys ⊇ (y :: ys)
        exact ⟨y₀, List.mem_cons_of_mem z hy₀_mem, hy₀⟩
      · -- (false,true): bump = y :: ys (unchanged)
        exact ⟨y₀, hy₀_mem, hy₀⟩
      · -- (true,false): bump = z :: ys ; the head y was dropped in favour of z
        rcases List.mem_cons.mp hy₀_mem with hy0y | hy0ys
        · subst hy0y
          exact ⟨z, by simp, htrans z y₀ w h1 hy₀⟩
        · exact ⟨y₀, List.mem_cons_of_mem z hy0ys, hy₀⟩
      · -- (true,true): bump = z :: ys (same reasoning)
        rcases List.mem_cons.mp hy₀_mem with hy0y | hy0ys
        · subst hy0y
          exact ⟨z, by simp, htrans z y₀ w h1 hy₀⟩
        · exact ⟨y₀, List.mem_cons_of_mem z hy0ys, hy₀⟩

/-- Every element of the input is dominated by some output of `thinBy`. -/
theorem thinBy_dominates (le : a → a → Bool)
    (hrefl : ∀ x, le x x = true)
    (htrans : ∀ x y z, le x y = true → le y z = true → le x z = true) :
    ∀ xs, Dominates (fun y x => le y x = true) (thinBy le xs) xs := by
  intro xs
  induction xs with
  | nil => intro x hx; cases hx
  | cons z zs ih =>
      rw [thinBy_cons]
      intro x hx
      rcases List.mem_cons.mp hx with hxz | hxzs
      · subst hxz
        exact bump_dom_self le hrefl x (thinBy le zs)
      · exact bump_dom_pres le htrans z (thinBy le zs) x (ih x hxzs)

/-- Correctness of `thinBy`: it always returns a valid thinning. -/
theorem thinBy_refines (le : a → a → Bool)
    (hrefl : ∀ x, le x x = true)
    (htrans : ∀ x y z, le x y = true → le y z = true → le x z = true) :
    ∀ xs, ThinBy (fun y x => le y x = true) xs (thinBy le xs) := by
  intro xs
  constructor
  · exact thinBy_sublist le xs
  · exact thinBy_dominates le hrefl htrans xs

/-- `le₁` is reflexive. -/
theorem le₁_refl (p : Nat × Nat) : le₁ p p = true := by
  simp [le₁]

/-- `le₁` is transitive. -/
theorem le₁_trans (p q s : Nat × Nat) :
    le₁ p q = true → le₁ q s = true → le₁ p s = true := by
  simp only [le₁, decide_eq_true_eq]
  rintro ⟨h1, h2⟩ ⟨h3, h4⟩
  exact ⟨le_trans h3 h1, le_trans h2 h4⟩

/-- Concrete capstone: the thinning computed for the book's example is indeed a
    valid member of the specification `ThinBy`. -/
example :
    ThinBy (fun y x => le₁ y x = true) [(1,2),(4,3),(2,3),(5,4),(3,1)]
      (thinBy le₁ [(1,2),(4,3),(2,3),(5,4),(3,1)]) := by
  -- apply thinBy_refines le₁ le₁_refl le₁_trans
  unfold thinBy
  simp [bump, le₁]
  constructor
  · apply List.Sublist.cons_cons
    apply List.Sublist.cons_cons
    apply List.Sublist.cons
    apply List.Sublist.refl
  · intro x h
    cases h
    use (1, 2)
    grind
    expose_names
    cases h
    use (4, 3)
    grind
    expose_names
    cases h
    use (4, 3)
    grind
    expose_names
    cases h
    use (5, 4)
    grind
    expose_names
    cases h
    use (3, 1)
    grind
    expose_names
    cases h


/-! ### The laws of thinning

  * identity              `id ← ThinBy r`
  * idempotence           `ThinBy r = ThinBy r · ThinBy r`
  * thin introduction     `MinWith cost = MinWith cost · ThinBy r`
  * thin elimination      `wrap · MinWith cost ← ThinBy r`
  * thin-map (one flavour)`map f · ThinBy r ← ThinBy r · map f`

The remaining laws (the distributive law and the thin-filter law) are stated in
comments; they are left as exercises. -/

/-- **Identity law.**  `id ← ThinBy r`, given reflexivity. -/
theorem thin_identity (r : a → a → Prop) (hrefl : ∀ x, r x x) :
    ∀ xs : List a, ThinBy r xs xs := by
  intro xs
  constructor
  · exact List.Sublist.refl xs
  · intro x hx
    use x
    constructor
    · assumption
    · exact hrefl x

/-- **Idempotence law.**  `ThinBy r = ThinBy r · ThinBy r`, for a preorder `r`. -/
theorem thin_idem (r : a → a → Prop)
    (hrefl : ∀ x, r x x)
    (htrans : ∀ x y z, r x y → r y z → r x z) :
    ∀ xs zs : List a, ThinBy r xs zs ↔ ∃ ys : List a,
    ThinBy r ys zs ∧ ThinBy r xs ys := by
  intro xs zs
  constructor
  · intro h
    use zs
    constructor
    · exact thin_identity r hrefl zs
    · assumption
  · intro h
    obtain ⟨ys, hys⟩ := h
    constructor
    · exact List.Sublist.trans (hys.1.1) (hys.2.1)
    · intro x hx
      have h₁ := hys.2.2
      obtain ⟨y, hy⟩ := h₁ x hx
      have h₂ := hys.1.2
      obtain ⟨z, hz⟩ := h₂ y hy.1
      use z
      constructor
      · exact hz.1
      · exact htrans z y x hz.2 hy.2

/-- Folding with `smaller cost` always returns an element of the list. -/
private lemma foldrSmaller_mem {α β : Type*} [LE β]
    [DecidableRel (α := β) (· ≤ ·)] (cost : α → β) (x : α) :
    ∀ ys : List α,
      List.foldr (fun u v => cond (cost u ≤ cost v) u v) x ys ∈ x :: ys := by
  intro ys
  induction' ys with z zs ih
  · simp
  · simp only [List.foldr_cons]
    by_cases h : cost z ≤ cost (List.foldr (fun u v => cond (cost u ≤ cost v) u v) x zs)
    · simp [h]
    · simp only [h, decide_false, cond_false]
      rcases List.mem_cons.1 ih with hx | hz
      · simp [hx]
      · exact List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inr hz)))


/-- Folding with `smaller cost` yields a cost-minimal element of the list. -/
private lemma foldrSmaller_le {α β : Type*} [LinearOrder β] (cost : α → β) (x : α) :
    ∀ (ys : List α) (z : α), z ∈ x :: ys →
      cost (List.foldr (fun u v => cond (cost u ≤ cost v) u v) x ys) ≤ cost z := by
  intro ys
  induction' ys with w ws ih
  · intro z hz
    simp at hz
    subst hz
    simp
  · intro z hz
    simp only [List.foldr_cons]
    set t := List.foldr (fun u v => cond (cost u ≤ cost v) u v) x ws with ht
    by_cases h : cost w ≤ cost t
    · simp only [h, decide_true, cond_true]
      rcases List.mem_cons.1 hz with hzx | hz'
      · rw [hzx]; exact le_trans h (ih x (by simp))
      · rcases List.mem_cons.1 hz' with hzw | hz''
        · rw [hzw]
        · exact le_trans h (ih z (by simp [hz'']))
    · simp only [h, decide_false, cond_false]
      have hwt : cost t ≤ cost w := le_of_lt (lt_of_not_ge h)
      rcases List.mem_cons.1 hz with hzx | hz'
      · rw [hzx]; exact ih x (by simp)
      · rcases List.mem_cons.1 hz' with hzw | hz''
        · rw [hzw]; exact hwt
        · exact ih z (by simp [hz''])

/-- `minWith cost` returns an element of the (non-empty) list. -/
theorem minWith_mem {α β : Type*} [Inhabited α] [LE β]
    [DecidableRel (α := β) (· ≤ ·)] (cost : α → β) :
    ∀ {xs : List α}, xs ≠ [] → minWith cost xs ∈ xs := by
  intro xs hxs
  match xs with
  | [] => exact absurd rfl hxs
  | x :: xs => exact foldrSmaller_mem cost x xs

/-- `minWith cost` returns a cost-minimal element of the list. -/
theorem minWith_le {α β : Type*} [Inhabited α] [LinearOrder β] (cost : α → β) :
    ∀ {xs : List α}, ∀ z ∈ xs, cost (minWith cost xs) ≤ cost z := by
  intro xs
  match xs with
  | [] => intro z hz; simp at hz
  | x :: xs => intro z hz; exact foldrSmaller_le cost x xs z hz

/-- **Thin introduction.**  `MinWith cost = MinWith cost · ThinBy r`,
    provided `x ⪯ y ⇒ cost x ≤ cost y`. This is the law that turns an
    optimisation problem into a thinning problem. -/
theorem thin_introduction [LinearOrder b]
    (r : a → a → Prop)
    (cost : a → b)
    (xs ys : List a)
    (hmono : ∀ x y, r x y → cost x ≤ cost y)
    (h : ThinBy r xs ys) :
  cost (minWith cost xs) = cost (minWith cost ys) := by
  obtain ⟨hsub, hdom⟩ := h
  by_cases hxs : xs = []
  · subst hxs
    rw [List.sublist_nil.1 hsub]
  · have hys : ys ≠ [] := by
      rintro rfl
      obtain ⟨y, hy, _⟩ := hdom _ (minWith_mem cost hxs)
      simp at hy
    have hmemx : minWith cost xs ∈ xs := minWith_mem cost hxs
    have hl : cost (minWith cost xs) ≤ cost (minWith cost ys) := by
      have hmy : minWith cost ys ∈ ys := minWith_mem cost hys
      exact minWith_le cost (minWith cost ys) (hsub.subset hmy)
    have hr : cost (minWith cost xs) ≥ cost (minWith cost ys) := by
      obtain ⟨y, hymem, hry⟩ := hdom _ hmemx
      exact le_trans (minWith_le cost y hymem) (hmono y (minWith cost xs) hry)
    grind

/-- `wrap x = [x]`. -/
def wrap (x : a) : List a := [x]

/-- **Thin elimination.**  `wrap · MinWith cost ← ThinBy r`,
    provided `cost x ≤ cost y ⇒ x ⪯ y`. Dual to thin introduction. -/
theorem thin_elimination {β : Type*} [LinearOrder β]
    (r : a → a → Prop) (cost : a → β)
    (hmono : ∀ x y, cost x ≤ cost y → r x y) :
    ∀ (xs : List a), xs ≠ [] → ThinBy r xs (wrap (minWith cost xs)) := by
  intro xs hxs
  constructor
  · have h₁ := minWith_mem cost hxs
    simpa [wrap]
  · intro x hx
    simp [wrap]
    have h₂ := minWith_le cost x hx
    apply hmono at h₂
    exact h₂

/-- **Thin-map law** (first flavour).  `map f · ThinBy r ← ThinBy r · map f`,
    provided `x ⪯ y ⇒ f x ⪯ f y`. -/
theorem thin_map (r : a → a → Prop) (f : a → a)
    (hmono : ∀ x y, r x y → r (f x) (f y))
    (xs ys : List a)
    (h : ThinBy r xs ys) :
    ThinBy r (map f xs) (map f ys) := by
  constructor
  · have h1 := h.1
    exact Sublist.map f h1
  · have h2 := h.2
    intro x hx
    simp at hx
    obtain ⟨z, hz⟩ := hx
    have h₀ := h2 z hz.1
    obtain ⟨w, hw⟩ := h₀
    use f w
    constructor
    · simp
      use w
      constructor
      · exact hw.1
      · rfl
    · have h₁ := hmono w z hw.2
      simp [hz] at h₁
      assumption

/-
  Remaining laws (exercises):

  * Distributive law:
        ThinBy r · concat = ThinBy r · concatMap (ThinBy r)
    with the weaker refinement
        concatMap (ThinBy r) ← ThinBy r · concat.

  * Thin-map law (second flavour):
        ThinBy r · map f ← map f · ThinBy r          if  f x ⪯ f y ⇒ x ⪯ y,
    giving the equality  map f · ThinBy r = ThinBy r · map f  when  x ⪯ y ⇔ f x ⪯ f y.

  * Thin-filter law:
        ThinBy r · filter p = filter p · ThinBy r     provided (x ⪯ y ∧ p y) ⇒ p x.
-/

-- ## Section 10.2 Paths in a layered network

namespace LayeredNetwork

/-! A layered network is given by a list of lists of edges, each list describing
the edges between two adjacent layers. Each edge is a triple `(u,v,w)`, where
`u` is the source, `v` the target and `w` a numerical weight, not necessarily
positive. The problem is to find a path from the top layer to the bottom layer
with minimum total weight. -/

abbrev Vertex := Nat
abbrev Weight := Int
abbrev Edge := Vertex × Vertex × Weight
abbrev Path := List Edge
abbrev Net := List (List Edge)

def source (e : Edge) : Vertex := e.1
def target (e : Edge) : Vertex := e.2.1
def weight (e : Edge) : Weight := e.2.2

def cost (p : Path) : Weight := (p.map weight).sum

/- `thinBy` drags along the instances of the section variable `a` -/
instance : Max Path := ⟨fun p q => if cost p ≤ cost q then q else p⟩
instance : Min Path := ⟨fun p q => if cost p ≤ cost q then p else q⟩

@[simp] theorem cost_nil : cost [] = 0 := rfl

@[simp] theorem cost_cons (e : Edge) (p : Path) : cost (e :: p) = weight e + cost p := by
  simp [cost]


/-! ### The network of Figure 10.1

Four layers of four vertices each: `1..4`, `5..8`, `9..12` and `13..16`.  There
are 27 paths from the top layer to the bottom one. -/

def layer₁ : List Edge := [(1,5,2), (1,6,7), (2,6,1), (3,6,4), (3,7,5), (4,7,2), (4,8,3)]
def layer₂ : List Edge := [(5,9,5), (6,9,3), (6,10,9), (6,11,8), (7,11,2), (8,11,7), (8,12,1)]
def layer₃ : List Edge := [(9,13,4), (9,14,8), (10,14,2), (10,15,5), (11,15,6), (11,16,3), (12,16,7)]

/-- The network of Figure 10.1. Note that each list of edges is sorted so that
    edges with the same source vertex appear together: this is what makes the
    thinning step below produce just one path per source vertex. -/
def net₁ : Net := [layer₁, layer₂, layer₃]


/-! ### The specification -/

/-- The Cartesian-product function `cp`. -/
def cp {γ : Type u} : List (List γ) → List (List γ) :=
  List.foldr (fun xs yss => xs.flatMap (fun x => yss.map (x :: ·))) [[]]

theorem cp_nil {γ : Type u} : cp ([] : List (List γ)) = [[]] := rfl

theorem cp_cons {γ : Type u} (xs : List γ) (xss : List (List γ)) :
    cp (xs :: xss) = xs.flatMap (fun x => (cp xss).map (x :: ·)) := rfl

#guard cp [["a","b","c"],["d","e"],["f"]] =
  [["a","d","f"],["a","e","f"],["b","d","f"],["b","e","f"],["c","d","f"],["c","e","f"]]

def linked (e₁ : Edge) : Path → Bool
  | []      => true
  | e₂ :: _ => target e₁ == source e₂

def connected : Path → Bool
  | []      => true
  | e :: es => linked e es && connected es

/-- `paths = filter connected · cp`. -/
def paths₀ (net : Net) : List Path := (cp net).filter connected

/-- `mcp ← MinWith cost · paths` -/
def mcp₀ (net : Net) : Path := minWith cost (paths₀ net)


/-! ### Fusing `filter connected` and `cp`

`paths = foldr step [[]]` where `step es ps = [e : p | e ← es, p ← ps, linked e p]`,
which we write in the equivalent form `step es ps = concat [cons e ps | e ← es]`. -/

def cons (e : Edge) (ps : List Path) : List Path :=
  (ps.filter (linked e)).map (e :: ·)

def step (es : List Edge) (ps : List Path) : List Path :=
  es.flatMap (fun e => cons e ps)

def paths (net : Net) : List Path := net.foldr step [[]]

private lemma filter_connected_map (e : Edge) :
    ∀ ps : List Path, (ps.map (e :: ·)).filter connected = cons e (ps.filter connected) := by
  intro ps
  induction ps with
  | nil => rfl
  | cons q qs ih =>
      by_cases h₁ : linked e q = true <;> by_cases h₂ : connected q = true <;>
        simp_all [cons, connected]

/-- The fusion step: `filter connected · cp = foldr step [[]]`. -/
theorem paths₀_eq_paths : ∀ net : Net, paths₀ net = paths net := by
  intro net
  induction net with
  | nil => rfl
  | cons es net ih =>
      simp only [paths₀] at ih ⊢
      have h : ∀ e : Edge,
          ((cp net).map (e :: ·)).filter connected = cons e (paths net) := by
        intro e
        rw [filter_connected_map, ih]
      rw [cp_cons, filter_flatMap]
      simp only [h]
      rfl

#guard (paths net₁).length = 27
#guard (paths net₁) = (paths₀ net₁)


/-! ### Introducing thinning

A greedy algorithm is not possible: the source of a minimum-cost path at one
level may not be among the target vertices of the edges at the next level up.
The thin-introduction law says we may rewrite the specification as

  `mcp ← MinWith cost · ThinBy (⪯) · paths`

provided `p₁ ⪯ p₂ ⇒ cost p₁ ≤ cost p₂`.  The appropriate choice is the *partial*
preorder below: there is no point in keeping a path if there is another path
with the same source vertex and lower cost. -/

def le₂ (p₁ p₂ : Path) : Bool :=
  decide (p₁.head?.map source = p₂.head?.map source ∧ cost p₁ ≤ cost p₂)

/-- `le₂` is reflexive. -/
theorem le₂_refl (p : Path) : le₂ p p = true := by simp [le₂]

/-- `le₂` is transitive. -/
theorem le₂_trans (p q r : Path) : le₂ p q = true → le₂ q r = true → le₂ p r = true := by
  simp only [le₂, decide_eq_true_eq]
  rintro ⟨h₁, h₂⟩ ⟨h₃, h₄⟩
  exact ⟨h₁.trans h₃, h₂.trans h₄⟩

/-- The proviso of thin introduction: `p₁ ⪯ p₂ ⇒ cost p₁ ≤ cost p₂`. -/
theorem le₂_cost (p q : Path) (h : le₂ p q = true) : cost p ≤ cost q := by
  simp only [le₂, decide_eq_true_eq] at h
  exact h.2

/-- The proviso of the **thin-filter law**: `p₁ ⪯ p₂ ∧ linked e p₂ ⇒ linked e p₁`. -/
theorem linked_of_le₂ (e : Edge) (p₁ p₂ : Path)
    (h : le₂ p₁ p₂ = true) (h₂ : linked e p₂ = true) : linked e p₁ = true := by
  simp only [le₂, decide_eq_true_eq] at h
  obtain ⟨hs, -⟩ := h
  cases p₁ with
  | nil => rfl
  | cons f fs =>
      cases p₂ with
      | nil => simp at hs
      | cons g gs =>
          simp only [List.head?_cons, Option.map_some] at hs
          have hs' : source f = source g := by simpa using hs
          simp only [linked, beq_iff_eq] at h₂ ⊢
          rw [hs']
          exact h₂

/-- The proviso of the **thin-map law**: `p₁ ⪯ p₂ ⇒ e : p₁ ⪯ e : p₂`.
    Note that no context is needed in this direction. -/
theorem cons_mono (e : Edge) (p₁ p₂ : Path) (h : le₂ p₁ p₂ = true) :
    le₂ (e :: p₁) (e :: p₂) = true := by
  simp only [le₂, decide_eq_true_eq] at h ⊢
  refine ⟨rfl, ?_⟩
  simp only [cost_cons]
  exact Int.add_le_add_left h.2 _

/-- The converse direction of the thin-map law *relies on context*: it holds for
    paths `p₁` and `p₂` that are both linked to `e` (and are both empty, or both
    non-empty, which in the fold is automatic since all candidates have the same
    length). -/
theorem cons_mono' (e : Edge) (p₁ p₂ : Path)
    (h₁ : linked e p₁ = true) (h₂ : linked e p₂ = true) (hne : p₁ = [] ↔ p₂ = [])
    (h : le₂ (e :: p₁) (e :: p₂) = true) : le₂ p₁ p₂ = true := by
  simp only [le₂, decide_eq_true_eq, cost_cons] at h ⊢
  refine ⟨?_, le_of_add_le_add_left h.2⟩
  cases p₁ with
  | nil =>
      have : p₂ = [] := hne.mp rfl
      subst this; rfl
  | cons f fs =>
      cases p₂ with
      | nil => exact absurd (hne.mpr rfl) (by simp)
      | cons g gs =>
          simp only [linked, beq_iff_eq] at h₁ h₂
          simp [h₁ ▸ h₂]


/-! ### The algorithm

`tstep es ps ← ThinBy (⪯) (step es ps)`, so that

  `foldr tstep [[]] ← ThinBy (⪯) · foldr step [[]]`

The claim justifying the fusion is `ThinBy (⪯) (cons e ps) = cons e (ThinBy (⪯) ps)`,
proved with the thin-map and thin-filter laws whose provisos are the three
lemmas above. -/

def tstep (es : List Edge) (ps : List Path) : List Path :=
  thinBy le₂ (step es ps)

def mcp (net : Net) : Path := minWith cost (net.foldr tstep [[]])

-- The first step produces exactly one singleton path per source vertex,
-- just as in the book.
/--
info: [[(9, 13, 4)], [(10, 14, 2)], [(11, 16, 3)], [(12, 16, 7)]]
-/
#guard_msgs in
#eval tstep layer₃ [[]]

-- Each additional step also produces exactly four paths, because each layer
-- has four vertices.
/--
info: 4
-/
#guard_msgs in
#eval (net₁.foldr tstep [[]]).length

#guard mcp net₁ = [(4,7,2), (7,11,2), (11,16,3)]
#guard cost (mcp net₁) = 7
#guard mcp net₁ = mcp₀ net₁

end LayeredNetwork

-- ## Section 10.3 Coin-changing revisited

/-- Merging two lists that are ordered according to `cmp`. -/
def merge2By {α : Type*} (cmp : α → α → Bool) : List α → List α → List α
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
      if cmp x y then x :: merge2By cmp xs (y :: ys)
      else y :: merge2By cmp (x :: xs) ys
  termination_by xs ys => xs.length + ys.length

/-- `mergeBy :: (a → a → Bool) → [[a]] → [a]`
    Merging sublists at each step is what lets us *maintain* the order of the
    candidates, which is what makes `thinBy` effective. -/
def mergeBy {α : Type*} (cmp : α → α → Bool) : List (List α) → List α :=
  List.foldr (merge2By cmp) []

namespace CoinChanging

/-! The greedy algorithm of Chapter 7 is not guaranteed to produce the smallest
number of coins for all denominations; in particular it fails for the United
Regions. Thinning gives an algorithm that works for *any* set of denominations.

Denominations are taken in increasing order, so that `foldr` considers them in
decreasing order of value. -/

abbrev Denom := Nat
abbrev Coin := Nat
abbrev Residue := Nat
abbrev Count := Nat

/-- A tuple consists of a list of coin counts `[cₖ,...,c₁]` for the
    denominations considered so far, the residual amount, and the number of
    coins used. -/
abbrev Tuple := List Coin × Residue × Count

def coins   (t : Tuple) : List Coin := t.1
def residue (t : Tuple) : Residue   := t.2.1
def count   (t : Tuple) : Count     := t.2.2

instance : Max Tuple := ⟨fun x y => if count x ≤ count y then y else x⟩
instance : Min Tuple := ⟨fun x y => if count x ≤ count y then x else y⟩

def ukds : List Denom := [1,2,5,10,20,50,100,200]
def urds : List Denom := [1,2,5,15,20,50,100]

/-- At each step the next lower denomination is considered, and every possible
    choice for a number of coins of this denomination is considered. -/
def extend (d : Denom) (t : Tuple) : List Tuple :=
  (List.range (residue t / d + 1)).map
    (fun c => (coins t ++ [c], residue t - c * d, count t + c))

def mktuples (n : Nat) (ds : List Denom) : List Tuple :=
  ds.foldr (fun d ts => ts.flatMap (extend d)) [([], n, 0)]

-- Unlike Chapter 7, `mktuples` returns all the *partial* tuples, including
-- those with a non-zero residue: `(mktuples 256 ukds).length = 10640485`.

/--
info: 293
-/
#guard_msgs in
#eval (mktuples 20 ukds).length

/-- `cost t = (residue t, count t)`, ordered lexicographically: a candidate with
    minimum cost is one whose residue is as small as possible and, among such
    candidates, one with minimum count. Since there is a denomination of value
    1, a minimum-cost candidate has zero residue and minimum count. -/
def cost (t : Tuple) : Residue ×ₗ Count := toLex (residue t, count t)

/-- `mkchange n ← coins · MinWith cost · mktuples n` -/
def mkchange₀ (n : Nat) (ds : List Denom) : List Coin :=
  coins (minWith cost (mktuples n ds))

/-! ### Introducing thinning

`mkchange n ← coins · MinWith cost · ThinBy (⪯) · mktuples n`, where `⪯` must
satisfy `t₁ ⪯ t₂ ⇒ cost t₁ ≤ cost t₂`. There is no point in keeping a tuple in
play if there is another tuple whose residue is the same but whose count is
smaller.

It might be thought that the stronger `residue t₁ ≤ residue t₂ ∧ count t₁ ≤
count t₂` would do, but that statement is false; see Exercise 10.16. -/

def le₃ (t₁ t₂ : Tuple) : Bool :=
  decide (residue t₁ = residue t₂ ∧ count t₁ ≤ count t₂)

theorem le₃_refl (t : Tuple) : le₃ t t = true := by simp [le₃]

theorem le₃_trans (t₁ t₂ t₃ : Tuple) :
    le₃ t₁ t₂ = true → le₃ t₂ t₃ = true → le₃ t₁ t₃ = true := by
  simp only [le₃, decide_eq_true_eq]
  rintro ⟨h₁, h₂⟩ ⟨h₃, h₄⟩
  exact ⟨h₁.trans h₃, h₂.trans h₄⟩

/-- The proviso of thin introduction: `t₁ ⪯ t₂ ⇒ cost t₁ ≤ cost t₂`. -/
theorem le₃_cost (t₁ t₂ : Tuple) (h : le₃ t₁ t₂ = true) : cost t₁ ≤ cost t₂ := by
  simp only [le₃, decide_eq_true_eq] at h
  obtain ⟨hr, hk⟩ := h
  simp only [cost, Prod.Lex.toLex_le_toLex, hr]
  right
  simpa

/-! ### Why the usual calculation breaks down

The distributive law rewrites `ThinBy (⪯) (step d ts)` into
`ThinBy (⪯) (concatMap (ThinBy (⪯) · extend d) ts)`, but the calculation can
proceed no further, because `ThinBy (⪯) · extend d = extend d`: the tuples in
`extend d t` have *different* residues, so thinning can never eliminate any of
them. -/

-- Exercise: no two tuples in `extend d t` are comparable under `le₃`.
theorem thin_extend_useless (d : Denom) (t : Tuple) :
    thinBy le₃ (extend d t) = extend d t := by
  sorry

/-! Instead we back up and prove the *key fact* (10.2) directly: if `t₁ ⪯ t₂`,
then every extension of `t₂` is dominated by some extension of `t₁`. This is
exactly the hypothesis needed by the general fusion theorem of Section 10.5. -/

/-- **Key fact (10.2)**: `t₁ ⪯ t₂ ⇒ ∀ e₂ ∈ extend d t₂, ∃ e₁ ∈ extend d t₁, e₁ ⪯ e₂`. -/
theorem key_fact (d : Denom) (t₁ t₂ : Tuple) (h : le₃ t₁ t₂ = true) :
    ∀ e₂ ∈ extend d t₂, ∃ e₁ ∈ extend d t₁, le₃ e₁ e₂ = true := by
  simp only [le₃, decide_eq_true_eq] at h
  obtain ⟨hr, hk⟩ := h
  intro e₂ he₂
  simp only [extend, List.mem_map, List.mem_range] at he₂
  obtain ⟨c, hc, rfl⟩ := he₂
  refine ⟨(coins t₁ ++ [c], residue t₁ - c * d, count t₁ + c), ?_, ?_⟩
  · simp only [extend, List.mem_map, List.mem_range]
    exact ⟨c, by rw [hr]; exact hc, rfl⟩
  · -- strip the `decide` first; unfolding the projections in the same `simp`
    -- call blocks `decide_eq_true_eq` from firing
    simp only [le₃, decide_eq_true_eq]
    refine ⟨?_, ?_⟩
    · simp only [residue] at hr ⊢
      rw [hr]
    · exact Nat.add_le_add_right hk c


/-! ### The algorithm

`tstep d ← ThinBy (⪯) · concatMap (extend d)`.  The thinning step is more
effective if tuples with the same residue are brought together, which is
achieved by keeping tuples in decreasing order of residue; since `extend`
already produces tuples in that order, it suffices to merge. -/

def cmp₃ (t₁ t₂ : Tuple) : Bool := decide (residue t₂ ≤ residue t₁)

def tstep (d : Denom) (ts : List Tuple) : List Tuple :=
  thinBy le₃ (mergeBy cmp₃ (ts.map (extend d)))

def mkchange (n : Nat) (ds : List Denom) : List Coin :=
  coins (minWith cost (ds.foldr tstep [([], n, 0)]))

-- `256 = 200 + 50 + 5 + 1`, four coins.
/--
info: [1, 0, 1, 0, 0, 1, 0, 1]
-/
#guard_msgs in
#eval mkchange 256 ukds

-- The greedy algorithm gives `20 + 5 + 5`; thinning finds `15 + 15`.
#guard mkchange 30 urds = [0,0,0,2,0,0,0]

#guard mkchange 20 ukds = [0,0,0,1,0,0,0,0]

end CoinChanging

-- ## Section 10.4 The knapsack problem

namespace Knapsack

/-! The 0/1 knapsack problem: either an item is chosen or it is not.  There is
no greedy algorithm for it — packing by decreasing value, by ascending weight,
or by decreasing value/weight ratio all fail in general. The dynamic
programming solution of Chapter 13 is more restrictive, in that it depends on
certain quantities being integers; here we give a thinning algorithm. -/

abbrev Name := String
abbrev Value := Nat
abbrev Weight := Nat
abbrev Item := Name × Value × Weight
abbrev Selection := List Name × Value × Weight

def name (i : Item) : Name := i.1

/-- Polymorphic: applies both to items and to selections. -/
def value {γ : Type} (x : γ × Value × Weight) : Value := x.2.1

/-- Polymorphic: applies both to items and to selections. -/
def weight {γ : Type} (x : γ × Value × Weight) : Weight := x.2.2

instance : Max Selection := ⟨fun x y => if value x ≤ value y then y else x⟩
instance : Min Selection := ⟨fun x y => if value x ≤ value y then x else y⟩

/-- The items in the thief's room. -/
def items₁ : List Item :=
  [("Laptop", 30, 14), ("Television", 67, 31), ("Jewellery", 19, 8), ("CD collection", 50, 24)]

def add (i : Item) (sn : Selection) : Selection :=
  (name i :: sn.1, value i + value sn, weight i + weight sn)

@[simp] theorem value_add (i : Item) (sn : Selection) :
    value (add i sn) = value i + value sn := rfl

@[simp] theorem weight_add (i : Item) (sn : Selection) :
    weight (add i sn) = weight i + weight sn := rfl

def within (w : Weight) (sn : Selection) : Bool := decide (weight sn ≤ w)

/-- `selections` returns all `2^n` subsequences of the given list of items. -/
def selections (its : List Item) : List Selection :=
  its.foldr (fun i sns => sns.flatMap (fun sn => [sn, add i sn])) [([], 0, 0)]

/-- `maxWith cost` is dual to `minWith cost`: it selects an element of maximum,
    rather than minimum, cost. -/
def maxWith {γ δ : Type*} [LE δ] [Inhabited γ] [DecidableRel (α := δ) (· ≤ ·)]
    (f : γ → δ) (as : List γ) : γ :=
  Chapter7.foldr1 (fun x y => cond (f y ≤ f x) x y) as

/-- `swag w ← MaxWith value · filter (within w) · selections` -/
def swag₀ (w : Weight) (its : List Item) : Selection :=
  maxWith value ((selections its).filter (within w))

#guard (selections items₁).length = 16

/-! ### Fusing `filter` with `selections`

`choices` generates only those selections whose total weight is at most the
carrying capacity of the knapsack. This step alone significantly reduces the
number of selections to consider. -/

def extend (w : Weight) (i : Item) (sn : Selection) : List Selection :=
  [sn, add i sn].filter (within w)

def choices (w : Weight) (its : List Item) : List Selection :=
  its.foldr (fun i sns => sns.flatMap (extend w i)) [([], 0, 0)]

#guard (choices 50 items₁).length = 11

/-! ### Introducing thinning

`swag w ← MaxWith value · ThinBy (⪯) · choices w`, where there is no point in
keeping a selection if there is another selection from the same list of items
with a greater value and a smaller weight. Note `sn₁ ⪯ sn₂ ⇒ value sn₁ ≥ value
sn₂`, which is the proviso of thin introduction in the case of `MaxWith`. -/

def le₄ (sn₁ sn₂ : Selection) : Bool :=
  decide (value sn₂ ≤ value sn₁ ∧ weight sn₁ ≤ weight sn₂)

theorem le₄_refl (sn : Selection) : le₄ sn sn = true := by simp [le₄]

theorem le₄_trans (s₁ s₂ s₃ : Selection) :
    le₄ s₁ s₂ = true → le₄ s₂ s₃ = true → le₄ s₁ s₃ = true := by
  simp only [le₄, decide_eq_true_eq]
  rintro ⟨h₁, h₂⟩ ⟨h₃, h₄⟩
  exact ⟨h₃.trans h₁, h₂.trans h₄⟩

/-- The proviso of thin introduction for `MaxWith`. -/
theorem le₄_value (s₁ s₂ : Selection) (h : le₄ s₁ s₂ = true) : value s₂ ≤ value s₁ := by
  simp only [le₄, decide_eq_true_eq] at h
  exact h.1

/-- **Key fact (10.2)** for the knapsack: every good extension of `sn₂` is
    dominated by a good extension of `sn₁`.  Note that the `filter (within w)`
    is harmless precisely because `sn₁` is no heavier than `sn₂`. -/
theorem key_fact (w : Weight) (i : Item) (sn₁ sn₂ : Selection) (h : le₄ sn₁ sn₂ = true) :
    ∀ e₂ ∈ extend w i sn₂, ∃ e₁ ∈ extend w i sn₁, le₄ e₁ e₂ = true := by
  simp only [le₄, decide_eq_true_eq] at h
  obtain ⟨hv, hw⟩ := h
  intro e₂ he₂
  simp only [extend, List.mem_filter, List.mem_cons,
    List.not_mem_nil, or_false, within, decide_eq_true_eq] at he₂
  obtain ⟨hmem, hin⟩ := he₂
  rcases hmem with rfl | rfl
  · refine ⟨sn₁, ?_, by simp [le₄, hv, hw]⟩
    rw [extend, List.mem_filter]
    refine ⟨by simp, ?_⟩
    simp only [within, decide_eq_true_eq]
    exact hw.trans hin
  · refine ⟨add i sn₁, ?_, ?_⟩
    · rw [extend, List.mem_filter]
      refine ⟨by simp, ?_⟩
      simp only [within, decide_eq_true_eq]
      simp only [weight_add]
      calc weight i + weight sn₁ ≤ weight i + weight sn₂ := Nat.add_le_add_left hw _
        _ ≤ w := by simpa using hin
    · simp only [le₄, decide_eq_true_eq]
      simp only [value_add, weight_add]
      exact ⟨Nat.add_le_add_left hv _, Nat.add_le_add_left hw _⟩

/-! ### The algorithm

The thinning step is more effective if the selections are kept in order; since
`extend` produces selections in increasing order of weight, we choose that. -/

def cmp₄ (s₁ s₂ : Selection) : Bool := decide (weight s₁ ≤ weight s₂)

def tstep (w : Weight) (i : Item) (sns : List Selection) : List Selection :=
  thinBy le₄ (mergeBy cmp₄ (sns.map (extend w i)))

def swag (w : Weight) (its : List Item) : Selection :=
  maxWith value (its.foldr (tstep w) [([], 0, 0)])

-- The best haul is `Jewellery + Laptop + CDs`, of value 99 and weight 46 —
-- beating `Television + Laptop` (97) and `Jewellery + Television` (86).
#guard swag 50 items₁ = (["Laptop", "Jewellery", "CD collection"], 99, 46)

#guard swag 50 items₁ = swag₀ 50 items₁

end Knapsack

-- ## Section 10.5 A general thinning algorithm

/-! The last two examples are very similar, so we end by solving an abstract
problem that captures all of the essential ideas behind thinning when
`candidates` is expressed as

  `candidates = foldr (concatMap · extend) [anon]`

and the specification has the form

  `best ← MinWith cost · filter good · candidates`

There are four ritual steps in calculating a thinning algorithm. We use the
section variable `a` for the type of candidates. -/

section General

variable {D : Type}

def candidates (ext : D → a → List a) (anon : a) (ds : List D) : List a :=
  ds.foldr (fun d xs => xs.flatMap (ext d)) [anon]

/-- `goodext d x = filter good (extend d x)`. -/
def goodext (good : a → Bool) (ext : D → a → List a) (d : D) (x : a) : List a :=
  (ext d x).filter good

def gstep (ge : D → a → List a) (d : D) (xs : List a) : List a :=
  xs.flatMap (ge d)

/-- Filtering before a `flatMap` changes nothing when every filtered-out element
    already maps to the empty list. -/
theorem flatMap_filter {α β : Type*} (good : α → Bool) (f : α → List β)
    (hbad : ∀ x, good x = false → f x = []) (l : List α) :
    l.flatMap f = (l.filter good).flatMap f := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      by_cases hx : good x = true
      · simp [List.flatMap_cons, hx, ih]
      · simp only [Bool.not_eq_true] at hx
        simp [List.flatMap_cons, hx, hbad x hx, ih]

/-- **Step 1.** Fuse `filter good` with `candidates`.  This is possible if a bad
    candidate has no good extension; and `anon` has to be good, otherwise there
    are no good candidates at all. -/
theorem filter_good_candidates (good : a → Bool) (ext : D → a → List a) (anon : a)
    (hgood : ∀ (d : D) (x y : a), y ∈ ext d x → good y = true → good x = true)
    (hanon : good anon = true) :
    ∀ ds : List D, (candidates ext anon ds).filter good
      = ds.foldr (gstep (goodext good ext)) [anon] := by
  intro ds
  induction ds with
  | nil => simp [candidates, hanon]
  | cons d ds ih =>
      have hbad : ∀ x : a, good x = false → (goodext good ext d) x = [] := by
        intro x hx
        simp only [goodext, List.filter_eq_nil_iff]
        intro y hy hgy
        rw [hgood d x y hy hgy] at hx
        exact Bool.noConfusion hx
      show ((candidates ext anon ds).flatMap (ext d)).filter good = _
      rw [filter_flatMap]
      show (candidates ext anon ds).flatMap (goodext good ext d) = _
      rw [flatMap_filter good (goodext good ext d) hbad, ih]
      rfl

/-- **Step 2** is thin introduction: with `x ⪯ y ⇒ cost x ≤ cost y` for all good
    candidates, `thin_introduction` refines the specification to

      `best ← MinWith cost · ThinBy (⪯) · foldr step [anon]`

    **Step 3** is to fuse `ThinBy (⪯)` with the `foldr`.  With
    `tstep d ← ThinBy (⪯) · step d`, this needs the fusion condition

      `ThinBy (⪯) · step d · ThinBy (⪯) ← ThinBy (⪯) · step d`

    which is (10.1) of Section 10.3.  It follows from the assumption below,
    which is the abstract form of the key fact (10.2). -/
def KeyFact (r : a → a → Prop) (ge : D → a → List a) : Prop :=
  ∀ (d : D) (x y : a), r x y → ∀ v ∈ ge d y, ∃ u ∈ ge d x, r u v

/-- **(10.1)**.  If `us` is a thinning of `ts` and `vs` is a thinning of
    `step d us`, then `vs` is a thinning of `step d ts`.  Thinning before a step
    loses nothing. -/
theorem thin_step_fusion (r : a → a → Prop)
    (htrans : ∀ x y z, r x y → r y z → r x z)
    (ge : D → a → List a) (hkey : KeyFact r ge)
    (d : D) (ts us vs : List a)
    (hus : ThinBy r ts us)
    (hvs : ThinBy r (gstep ge d us) vs) :
    ThinBy r (gstep ge d ts) vs := by
  obtain ⟨hsub, hdom⟩ := hus
  obtain ⟨hsub', hdom'⟩ := hvs
  constructor
  · -- `vs <+ step d us <+ step d ts`, since `xs <+ ys ⇒ step d xs <+ step d ys`
    exact hsub'.trans (hsub.flatMap (ge d))
  · -- `∀ w ∈ step d ts, ∃ v ∈ vs, v ⪯ w`
    intro w hw
    simp only [gstep, List.mem_flatMap] at hw
    obtain ⟨t, ht, hwt⟩ := hw
    obtain ⟨u, hu, hru⟩ := hdom t ht
    obtain ⟨e, he, hre⟩ := hkey d u t hru w hwt
    have hemem : e ∈ gstep ge d us := List.mem_flatMap.2 ⟨u, hu, he⟩
    obtain ⟨v, hv, hrv⟩ := hdom' e hemem
    exact ⟨v, hv, htrans v e w hrv hre⟩

/-- **Step 4.** Make thinning more effective by keeping the candidates in order,
    merging sublists at each step rather than sorting.  This is the general
    algorithm:

      `best = minWith cost · foldr step [anon]`
      `  where step d = thinBy (⪯) · mergeBy cmp · map (filter good · extend d)`
      `        cmp x y = value x ≤ value y`

    It is possible, with more or less effort, to reformulate the three problems
    of this chapter as instances of this scheme; what matters is that the
    derivation of a thinning algorithm follows a more or less standard path. -/
def best {β : Type} [LE β] [DecidableRel (α := β) (· ≤ ·)]
    (cost : a → β) (le cmp : a → a → Bool) (good : a → Bool)
    (ext : D → a → List a) (anon : a) (ds : List D) : a :=
  minWith cost
    (ds.foldr (fun d xs => thinBy le (mergeBy cmp (xs.map (goodext good ext d)))) [anon])

end General

end Chapter10
