import Mathlib.Tactic

open Set
section Sets

variable (α : Type) -- this is a set A

variable (S : Set α) -- S ⊆ A, Set α is the type of all subsets of α
#reduce Set α

-- Since sets are just α → Prop one can define sets as
example : Set α := fun _x ↦ True
example : Set α := { _x : α | True }

example : Set α := fun x ↦ x ≠ x
example : Set α := {x | x ≠ x}

--The usual opeartions on sets are defined
variable (T : Set α)

#check S ⊆ T -- Set.Subset
#check S ∩ T -- Set.inter
#check S ∪ T
#check S \ T
#check Sᶜ
#check (univ : Set α)
#check (∅ : Set α)

example : S ⊆ T ↔ ∀ x, x ∈ S → x ∈ T :=
  .rfl -- Iff.rfl definitional equality,
       -- otherwise uses Eq.rfl by default
       -- If we go in tactic mode (with `by`)
       -- then the `rfl` tactic will use the
       -- appropriate reflexivity lemma

example : S ∩ T ⊆ T := by
  intro x
  intro x_in_ST
  -- lean knows that x ∈ T ∩ S ↔ x ∈ T ∧ x ∈ S
  have : x ∈ S ∧ x ∈ T := x_in_ST
  exact this.right
  done

example : S ∩ T ⊆ S := by
  rw [subset_def]
  intro x x_in_ST
  rw [mem_inter_iff] at x_in_ST
  have := And.left x_in_ST
  exact this
  done

variable (U : Set α)
example : S ∩ (T ∪ U) ⊆ S ∩ T ∪ S ∩ U := by
  intro x
  simp
  intro hs htu
  -- case' produces subgoals, while cases wants pattern matching
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
  rcases htu with ht | hu
  . left
    exact ⟨hs, ht⟩
  . right
    exact ⟨hs, hu⟩

-- example : S ∩ (T ∪ U) ⊆ S ∩ T ∪ S ∩ U := by
--   intro x
--   simp
--   intro hs htu
--   case' htu with ht | hu
--   . left
--     exact ⟨hs, ht⟩
--   . right
--     exact ⟨hs, hu⟩

-- Hover over the parenthesis here below!
example : (S \ T) \ U ⊆ S \ (T ∪ U) := by
  intro x
  simp
  tauto -- splits the goals at ∧, ∨, ∃, ↔ and
        -- applies reflexivity to each bit

#check @Set.ext -- @ makes the type more explicit since it does not hide inferred parameters
#check @Set.Subset.antisymm

example : S ∩ T = T ∩ S := by
  ext x -- Simplifies use of Set.ext: introduces x that belong to the set
  simp
  exact and_comm -- or And.comm
  done

variable (β : Type)
variable (f : α -> Set β)
#check ⋃ i, f i     -- indexed union (\bigcup)
#check ⋃ i : α, f i -- same as above
#check ⋂ i : α, f i

-- bounded union
#check ⋃ i ∈ S, f i

-- operations on sets of sets
variable (A : Set (Set α))
#check ⋂₀ A
#check ⋃₀ A
example :
  (⋃ (p) (hp : Nat.Prime p), {x | p ∣ x}) = {1}ᶜ := by
  ext n
  simp
  constructor
  . intro ⟨p,pp,pn⟩ n1
    rw [n1] at pn
    -- have p1 := Nat.dvd_one.1 pn
    rw [Nat.dvd_one] at pn
    --rw [p1] at pp
    rw [pn] at pp
    exact Nat.not_prime_one pp
  . intro n1
    have := Nat.exists_prime_and_dvd n1
    exact this

end Sets

section Functions
open Function

variable (α β : Type)
variable (f : α → β)

#check range f

variable (S : Set α)
variable (T : Set β)

#check f '' S -- image of S after applying f
#check f ⁻¹' T -- preimage of T after applying f

example : f '' S ⊆ range f := by
  intro x
  simp
  -- rintro y ys h
  -- use y
  -- exact h
  rintro y _ rfl
  -- rfl uses subst and will substitute things around,
  -- so it is a better choice to use it in general
  use y

-- also
example : f '' S ⊆ range f := by
  intro x
  simp
  rintro y _ ⟨⟩
  use y

-- Data.Set.Image and Data.Set.Basic
-- have the most useful theorems for sets

end Functions

section Induction

-- You can use inductive types, Nat is one such type
#print Nat

-- inductive Nat where
--  | zero : ℕ
--  | succ (n: ℕ) → ℕ

example (P : Nat -> Prop)
  (H0 : P 0)
  (Hsucc : ∀ n, P n -> P (n+1)) :
  ∀ n, P n := by
  intro n
  induction n
  case zero =>
    exact H0
  -- the succ case includes successor and induction hypothesis
  case succ n' ih =>
    exact Hsucc n' ih
  done

example (P : Nat -> Prop)
  (H0 : P 0)
  (Hsucc : ∀ n, P n -> P (n+1)) :
  ∀ n, P n := by
  intro n
  induction' n with n' ih
  . exact H0
  . exact Hsucc n' ih
  done

-- you can use recursion with inductive types
def fac : Nat -> Nat
  | 0 => 1
  | n + 1 => (n + 1) * fac n

-- we can write proofs by induction in recursive style
theorem fac_pos : ∀ n, fac n > 0
  | 0 => by decide -- it is a decidable inequality on natural numbers
  | n+1 => by
    rw [fac]
    apply Nat.mul_pos
    . apply Nat.succ_pos
    . apply fac_pos

theorem foo : Nat -> True
  | 0 => trivial
  | n + 1 =>
    -- have is both a term and a tactic
    have : ((n+1) / 2) < n + 1 := by
      exact Nat.div_lt_self' n 0
    foo ((n+1) / 2)
termination_by foo n => n

-- theorem fac_pos' : ∀ n, fac n > 0
--   | 0 => by decide
--   | n+1 => fac_pos' _
-- Fails due to termination issues

theorem exists_prime_factor
    {n : Nat} (h : 2 ≤ n) :
    ∃ p : Nat, p.Prime ∧ p ∣ n := by
  sorry
