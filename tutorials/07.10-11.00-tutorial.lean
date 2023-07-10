import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

section fae

namespace Nat

open NNReal Real

-- This works because typechecks as Proposition,
-- aka an understandable mathematical statement
#check Prime 4
#check 4 ≤ 5
#check ∀ n m : ℕ, n <= m ∧ m ≤ n -> m = 2 * n

-- Sometimes truth values can be checked using the eval #command

#eval Prime 4 -- false
#eval 4 ≤ 5 -- true
#eval ∀ n m : ℕ, n <= m ∧ m ≤ n -> m = 2 * n -- failed to synthesize Decidable Prop

-- So eval evaluates numerical experessions, it is not really made to prove stuff

#check 36 + 1
#eval 36 + 1 -- note that ℕ is gone now
#check (37 : ℝ) -- there is a lot going on behind curtains here, 37 : ℕ is mapped via Cauchy sequences to 37 : ℝ
#check (π : ℕ) -- type mismatch

#check ℝ
#check Prop
#check Type -- there is a hyerarchy of types
#check Type 2

-- Prop : Type = Type 0 : Type 1 : Type 2 : ...

#eval sqrt 2 -- 1
#eval (sqrt 2 : ℝ) -- Real.ofCauchy (sorry /- 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, ... -/)

#check ℝ → ℕ
#check π
#check exp
#check (exp)
#check Real.sqrt
#check exp = (exp) -- Prop: it is just a type denoting an equality relation
-- proof means showing that the Prop type contains a term, if it does not then the result is false
-- the statement below is also of type Prop but we expect it will not contain a term
#check exp = (sin)

-- the two arrows (dash greater) and (latex to) mean the same thing although
-- have different appearences
#check (ℝ≥0->Type 4)
#check (ℝ≥0→Type 4)

#check (π : ℝ≥0) -- terms belonging to different types cannot be equal!
#check (NNReal.pi)
#check NNReal.pi = π

-- let us to Euclid theorem step by step

-- def: define a term of some type
def int : Type 12 := sorry -- here you should put some definition

-- So we can use def to define the statement of the theorem
def Euclid_statement_n (n : ℕ) := ∃ p, n≤p ∧ Prime p
#check Euclid_statement_n -- ℕ -> Prop
#check Euclid_statement_n 37 -- Prop


def Euclid_statement_Forall := ∀ n : ℕ, ∃ p, n≤p ∧ Prime p
#check Euclid_statement_Forall
#check Euclid_statement_Forall = Euclid_statement_n -- they belong to different types so they cannot be equal

-- [] <- to endow types with special structure
example (X Y Z : Type 0) [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {f : X → Y} {g : Y → Z} (hf : Continuous f) (hg : Continuous g)
  : Continuous (g ∘ f) := by
  -- rewrite using continuous_def : preimage of opens are open
  rw [continuous_def] at hf hg |-
  -- introduce hypotheses, seems like in coq
  -- from the previous row we have ∀ (s : Set Z), IsOpen s -> IsOpen (g ∘ f⁻¹ ' s )
  intro U hU
  -- let adds hypothesis to the goals
  let φ_U := hg U hU
  let ψ_U := hf (g⁻¹' U) φ_U
  exact ψ_U

-- clearly this is cumbersome and somewht standard, lean provides a way
-- to search for relevant tactics with 'apply?'
example (X Y Z : Type 0) [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {f : X → Y} {g : Y → Z} (hf : Continuous f) (hg : Continuous g)
  : Continuous (g ∘ f) := by
  apply?
-- this will answer with Try this: exact Continuous.comp hg hf
-- which does actually work!
example (X Y Z : Type 0) [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {f : X → Y} {g : Y → Z} (hf : Continuous f) (hg : Continuous g)
  : Continuous (g ∘ f) := by
  exact Continuous.comp hg hf

-- on errors. I made a mistake when typing the hypotheses on g
example (X Y Z : Type 0) [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {f : X → Y} {g : X → Y} (hf : Continuous f) (hg : Continuous g)
  : Continuous (g ∘ f) := sorry
-- with this it fails with
-- typeclass instance problem is stuck, it is often due to metavariables TopologicalSpace ?m.198368
