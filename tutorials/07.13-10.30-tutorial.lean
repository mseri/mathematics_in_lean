import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.NormedSpace.BanachSteinhaus
import Mathlib.Analysis.NormedSpace.FiniteDimension
import Mathlib.Analysis.Calculus.Inverse
import Mathlib.Analysis.Calculus.ContDiff
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

open Set Filter Topology Classical Real MeasureTheory intervalIntegral Interval

example {f : ℝ → ℝ} {a : ℝ} (h : IsLocalMin f a) : deriv f a = 0 :=
  h.deriv_eq_zero

example {f : ℝ → ℝ} {a : ℝ} (h : IsLocalMin f a) : deriv f a = 0 :=
  IsLocalMin.deriv_eq_zero h

example : deriv (fun x : ℝ ↦ x ^ 5) 6 = 5 * 6 ^ 4 := by simp

example : deriv sin π = -1 := by simp

example : ∀ n : ℕ, sin (n * π) = sin 0 := by simp

example : ∀ n : ℕ, cos (2 * n * π) = cos 0 := by
  intro n
  rw [mul_comm, mul_comm 2, mul_comm,
      <-add_zero (n * 2 * π), add_comm, mul_assoc]
  apply cos_add_nat_mul_two_pi 0 n

example {a b : ℝ} (h : (0 : ℝ) ∉ ([a,b])) : (∫ x in a..b, 1 / x) = Real.log (b/a) :=
  integral_one_div h

example : (∫ x in (-1 : ℝ)..(-2), 1/x) = Real.log 2 := by
  rw [integral_one_div] ⟨;⟩ norm_num

example : (∫ x in (-2 : ℝ)..(-1), 1/x) = -Real.log 2 := by
  rw [integral_one_div]
  rw [ <-log_inv ]
  . norm_num
  . norm_num