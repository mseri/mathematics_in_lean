import Mathlib.Analysis.Complex.Liouville

set_option quotPrecheck false
set_option autoImplicit false

open Set

local notation "ℍ" => { z : ℂ | 0 < z.im }

example {f : ℂ → ℂ}
    (h₁ : Differentiable ℂ f)
    (h₂ : range f ⊆ ℍ) (z w : ℂ) :
    f z = f w := by
  -- Your proof here
  sorry
