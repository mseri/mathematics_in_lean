-- this is a simplified version of C03

import Mathlib.Tactic
import Mathlib.Data.Real.Basic

namespace Leiden
section
-- universal quantifiers, then ifttt

variable (α : Type) (P : α -> Prop)
#check ∀ x, P x

variable (P Q: Prop)
#check P → Q

-- the arrow allows us to chain multiple implications together
-- the arrow associates right
-- you could use ∧ but by currying you don't need to split over the and's
#check ∀ x y ε : ℝ, 0 < ε -> ε ≤ 1 -> |x| < ε -> |y| < ε ->  |x * y| < ε

theorem my_lemma : ∀ x y ε : ℝ, 0 < ε -> ε ≤ 1 -> |x| < ε -> |y| < ε ->  |x * y| < ε := by
  sorry

-- curly braces make the argument optional (inferrable)
theorem my_lemma2 : ∀ {x y ε : ℝ}, 0 < ε -> ε ≤ 1 -> |x| < ε -> |y| < ε ->  |x * y| < ε := by
  sorry

section
variable (a b δ : ℝ)
variable (h0 : 0 < δ) (h1 : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

#check my_lemma2 h0 h1 ha hb

end

theorem my_lemma3 : ∀ {x y ε : ℝ}, 0 < ε -> ε ≤ 1 -> |x| < ε -> |y| < ε ->  |x * y| < ε := by
  intro epos ele1 xlt ylt
  sorry


theorem my_lemma4 : ∀ {x y ε : ℝ}, (epos: 0 < ε) -> (ele1: ε ≤ 1) -> (xlt: |x| < ε) -> (ylt: |y| < ε) ->  |x * y| < ε := by
  sorry

-- quantifiers can be hidden in definitions
def FnUb (f: ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

section
variable ( f g : ℝ → ℝ ) ( a b : ℝ )


-- dsimp, simplifies using defnitions
example (hfa: FnUb f a) (hgb: FnUb g b) : FnUb ( fun x ↦ f x + g x ) (a + b) := by
  intro y
  dsimp
  apply add_le_add
  . apply hfa
  apply hgb

theorem fnUb_add (hfa: FnUb f a) (hgb: FnUb g b) : FnUb ( fun x ↦ f x + g x ) (a + b) :=
  fun x ↦ add_le_add (hfa x) (hgb x)

end

example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  use 5/2
  norm_num

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
  ⟨5 / 2, by norm_num⟩

end

variable {f g : ℝ → ℝ}
variable {a b : ℝ}

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

-- example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
--   rcases ubf with ⟨a, ubfa⟩
--   rcases ubg with ⟨b, ubgb⟩
--   use a + b
--   apply fnUb_add ubfa ubgb



-- example : FnHasUb f -> FnHasUb g -> FnHasUb fun x ↦ f x + g x := by
--   rintro ⟨a, ubfa⟩ ⟨b, ubgb⟩
--   apply fnUb_add ubfa ubgb

end Leiden