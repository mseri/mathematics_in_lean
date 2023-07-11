import Mathlib.Tactic

open Set

section Sets

/-
The word "set" from standard mathematics is
translated to lean in two ways.
-/

-- One way is "Let A be a set" and is usually
-- translated like this:
variable (α : Type)

-- The other way is "let S ⊆ A" and is
-- translated like this:
variable (S : Set α)

-- `set α` is the type of all subsets of a
-- type α.
-- It is defined as `α → Prop`:
#reduce Set α

-- which means we can actually write sets
-- using lambdas like this:

example : Set α := fun x ↦ True
example : Set α := fun x ↦ x ≠ x
example : Set α := fun x ↦ ¬S x

-- This is really just set comprehension,
-- and we prefer that notation:
example : Set α := {x : α | True}
example : Set α := {x | x ≠ x}
example : Set α := {x | ¬x ∈ S}

-- The usual set operations exist:

variable (T : Set α)
#check S ⊆ T           -- Set.Subset
#check S ∩ T           -- Set.inter
#check S ∪ T           -- Set.union
#check S \ T           -- Set.diff
#check Sᶜ              -- Set.compl
#check (univ : Set α)  -- Set.univ
#check (∅ : Set α)     -- empty set

variable (x : α)
#check x ∈ S -- Set.Mem
#check x ∉ S -- notation for ¬ x ∈ S

-- If we want to prove that one set is a
-- subset of another,
-- we can use the definition:

example : S ⊆ T ↔ ∀ x, x ∈ S → x ∈ T :=
  .rfl -- lean knows this is a
       -- definitional equality

example : S ∩ T ⊆ T := by
  -- The goal is actually just
  -- ∀ x, x ∈ S ∩ T → x ∈ T, so we can intro x
  intro x
  intro x_in_ST

  -- Lean also knows that x ∈ S ∩ T means
  -- x ∈ S ∧ x ∈ T:
  have : x ∈ S ∧ x ∈ T := x_in_ST

  exact And.right this

-- If we want to unfold the definitions,
-- we can use rw to unfold the definitions
example : S ∩ T ⊆ S := by
  rw [subset_def]
  intro x x_in_ST
  rw [mem_inter_iff] at x_in_ST
  have := And.left x_in_ST
  exact this

-- This is of course also a theorem in the
-- library, so we can use that:
example : S ∩ T ⊆ S := by apply?

example : S ∩ T ⊆ S := inter_subset_left _ _


variable (U : Set α)

example : S ∩ (T ∪ U) ⊆ S ∩ T ∪ S ∩ U := by
  intro x
  simp
  intro hs htu
  cases htu with
  | inl ht =>
    left
    exact ⟨hs, ht⟩
  | inr hu =>
    right
    exact ⟨hs, hu⟩

example : S ∩ (T ∪ U) ⊆ S ∩ T ∪ S ∩ U := by
  intro x
  simp
  intro hs htu
  cases' htu with ht hu
  · left
    exact ⟨hs, ht⟩
  · right
    exact ⟨hs, hu⟩

example : S ∩ (T ∪ U) ⊆ S ∩ T ∪ S ∩ U := by
  intro x
  simp
  intro hs htu
  rcases htu with ht | hu
  · left
    exact ⟨hs, ht⟩
  · right
    exact ⟨hs, hu⟩

example : S ∩ (T ∪ U) ⊆ S ∩ T ∪ S ∩ U := by
  intro x
  simp
  tauto

-- Problem
example : (S ∩ T) ∪ (S ∩ U) ⊆ S ∩ (T ∪ U) := by
  sorry

      -- hover your cursor here! v
-- The set difference operator S \ T is
-- using a unicode character written \\.
example : (S \ T) \ U ⊆ S \ (T ∪ U) := by
  intro x
  simp
  tauto

-- To prove sets are equal, we show that
-- every element of one is an element of the
-- other. There are a couple ways to say this:

#check @Set.ext
#check @Set.Subset.antisymm

-- There is also a *tactic* called `ext` to
-- simplify uses of Set.ext:
example : S ∩ T = T ∩ S := by
  ext x
  simp
  exact And.comm

-- applies Set.ext and then introduces x
-- We can do intersections and unions of
-- arbitrarily many sets using
-- ⋃ "\bigcup" and ⋂ "\bigcap"
-- ^               ^ (also mouse over for other input options)

variable (β : Type)
variable (f : α → Set β)
#check ⋃ i, f i  -- indexed union, Set.Union
#check ⋃ i : α, f i -- same thing
#check ⋂ i, f i  -- indexed intersection, Set.Inter

-- There are also two other versions of the
-- union operator:

-- * "bounded union" = union over the
--   elements of S
#check ⋃ i ∈ S, f i -- Set.biUnion

-- * "set union" = union over a set of sets
variable (𝒜 : Set (Set α))
#check ⋃₀ 𝒜 -- Set.sUnion

-- and similarly for intersections
#check ⋂ i ∈ S, f i -- Set.biInter
#check ⋂₀ 𝒜 -- Set.sInter

-- Here's an interesting example using
-- indexed unions:
example :
    (⋃ (p) (hp : Nat.Prime p), {x | p ∣ x}) =
      {1}ᶜ := by
  ext n
  simp
  constructor
  · intro ⟨p, pp, pn⟩ n1
    rw [n1] at pn
    rw [Nat.dvd_one] at pn
    rw [pn] at pp
    exact Nat.not_prime_one pp
  · intro n1
    have := Nat.exists_prime_and_dvd n1
    exact this

end Sets

section Functions
open Function

variable (α β : Type)

-- Any function has a domain and a range.
-- In lean, functions always have a specified
-- domain and codomain:

variable (f : α → β)

-- But we can get the range as a set:
#check range f

variable (S : Set α)

-- Given a set in the domain we can get the
-- image of that set in the codomain:
#check f '' S

variable (T : Set β)

-- The preimage is written with a mashup of
-- ⁻¹ and '' symbols:
#check f ⁻¹' T

example : f '' S ⊆ range f := by
  intro x
  simp
  rintro y ys rfl
  use y

-- Good files to import and/or peruse for
-- theorems about sets include
-- Data.Set.Basic and Data.Set.Lattice
#check @image_preimage_subset
-- https://leanprover-community.github.io/mathlib_docs/data/set/basic.html#set.image_preimage_subset
#check @inter_union_distrib_left
-- https://leanprover-community.github.io/mathlib_docs/data/set/basic.html#set.inter_union_distrib_left
#check @sUnion_empty
-- https://leanprover-community.github.io/mathlib_docs/data/set/lattice.html#set.sUnion_empty

end Functions

section Induction

-- Lean has a mechanism for defining
-- "inductive types". Nat is one of them:

#print Nat -- <- ctrl-click on Nat

-- inductive Nat where
--   | zero : Nat
--   | succ (n : Nat) : Nat

-- So Nat is defined as having a zero,
-- a successor function, and "nothing else".

-- Formally we express this using proof by
-- induction:

example (P : Nat → Prop)
    (H0 : P 0)
    (Hsucc : ∀ n, P n → P (n+1)) :
    ∀ n, P n := by
  intro n
  induction n
  case zero =>
    exact H0
  case succ n' ih =>
    exact Hsucc n' ih

example (P : Nat → Prop)
    (H0 : P 0)
    (Hsucc : ∀ n, P n → P (n+1)) :
    ∀ n, P n := by
  intro n
  induction' n with n' ih
  · exact H0
  · exact Hsucc n' ih


-- You can also define functions by
-- recursion on Nat:

def fac : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fac n

-- You can write proofs by induction
-- in the style of recursive functions:

theorem fac_pos : ∀ n, fac n > 0
  | 0 => by decide
  | n + 1 => by
    rw [fac]
    apply Nat.mul_pos
    · apply Nat.succ_pos
    · apply fac_pos

theorem foo'' : Nat → True
  | 0 => trivial
  | n + 1 => foo'' ((n + 1) / 2)

theorem foo : Nat → True
  | 0 => trivial
  | n + 1 =>
    foo ((n + 1) / 2)
termination_by foo n => n

theorem foo : Nat → True
  | 0 => trivial
  | n + 1 =>
    foo ((n + 1) / 2)
termination_by foo n => n

theorem foo' : Nat → True
  | 0 => trivial
  | n + 1 =>
    have : (n + 1) / 2 < n + 1 :=
      Nat.div_lt_self' n 0
    foo' ((n + 1) / 2)
termination_by foo' n => n

-- theorem fac_pos' : ∀ n, fac n > 0
--   | 0 => by decide
--   | n + 1 => fac_pos' _

-- Let's do a more interesting theorem,
-- Euclid's theorem on infinitely many primes

theorem exists_prime_factor
    {n : Nat} (h : 2 ≤ n) :
    ∃ p : Nat, p.Prime ∧ p ∣ n := by
  by_cases np : n.Prime
  · use n, np
  induction' n using Nat.strong_induction_on
    with n ih
  dsimp at ih
  rw [Nat.prime_def_lt] at np
  push_neg at np
  let ⟨m, mltn, mdvdn, mne1⟩ := np h
  have mgt2 : 2 ≤ m := by
    match m with
    | 0 =>
      rw [zero_dvd_iff] at mdvdn
      linarith
    | 1 =>
      contradiction
    | n+2 =>
      apply Nat.le_add_left
  by_cases mp : m.Prime
  · use m, mp
    exact mdvdn
  · let ⟨p, pp, pdvd⟩ := ih m mltn mgt2 mp
    use p, pp
    apply pdvd.trans mdvdn

theorem primes_infinite :
    ∀ n, ∃ p > n, Nat.Prime p := by
  intro n
  have : 2 ≤ Nat.factorial (n + 1) + 1 := by
    sorry
  let ⟨p, pp, pdvd⟩ :=
    exists_prime_factor this
  refine ⟨p, ?_, pp⟩
  show p > n
  by_contra ple
  push_neg at ple
  have : p ∣ Nat.factorial (n + 1) := by
    sorry
  have : p ∣ 1 := by
    sorry
  show False
  sorry

end Induction
