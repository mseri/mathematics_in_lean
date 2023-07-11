import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

section
variable (R : Type _) [Ring R]

#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
#check (add_comm : ∀ a b : R, a + b = b + a)
#check (zero_add : ∀ a : R, 0 + a = a)
#check (add_left_neg : ∀ a : R, -a + a = 0)
#check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
#check (mul_one : ∀ a : R, a * 1 = a)
#check (one_mul : ∀ a : R, 1 * a = a)
#check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
#check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)

end

section
variable (R : Type _) [CommRing R]
variable (a b c d : R)

example : c * b * a = b * (a * c) := by ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring

end

namespace MyRing
variable {R : Type _} [Ring R]

theorem add_zero (a : R) : a + 0 = a := by rw [add_comm, zero_add]

theorem add_right_neg (a : R) : a + -a = 0 := by rw [add_comm, add_left_neg]

#check MyRing.add_zero
#check add_zero

end MyRing

namespace MyRing
variable {R : Type _} [Ring R]

theorem neg_add_cancel_left (a b : R) : -a + (a + b) = b := by
  rw [← add_assoc, add_left_neg, zero_add]

-- Prove these:
theorem add_neg_cancel_right (a b : R) : a + b + -b = a := by
  rw [add_assoc, add_comm, add_right_neg, zero_add]
  done

theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  rw [<-neg_add_cancel_left a b, h, neg_add_cancel_left]
  done

theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c := by
  rw [<-add_neg_cancel_right a b, h, add_neg_cancel_right]
  done

theorem mul_zero (a : R) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← mul_add, add_zero, add_zero]
  rw [add_left_cancel h]

theorem zero_mul (a : R) : 0 * a = 0 := by
  have h : 0 * a + 0 * a = 0 * a + 0 := by
    rw [<-add_mul, add_zero, add_zero]
  rw [add_left_cancel h]
  done
  -- We could equally well have closed the proof with
  -- apply add_left_cancel h or exact add_left_cancel h.
  -- The exact tactic takes as argument a proof term which
  -- completely proves the current goal, without creating
  -- any new goal. The apply tactic is a variant whose
  -- argument is not necessarily a complete proof. The
  -- missing pieces are either inferred automatically by
  -- Lean or become new goals to prove. While the exact
  -- tactic is technically redundant since it is strictly
  -- less powerful than apply, it makes proof scripts
  -- slightly clearer to human readers and easier to maintain
  -- when the library evolves.

theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  have h1 : a + b = a + -a := by
    rw [<-add_right_neg a] at h
    rw [h]
  rw [add_left_cancel h1]
  done

theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b := by
  have h1 : a + b = b + -b := by
    rw [<-add_right_neg b] at h
    rw [h]
  rw [add_comm] at h1
  rw [add_left_cancel h1]
  done

-- We had to use the annotation (-0 : R) instead of
-- 0 in the third theorem because without specifying
-- R it is impossible for Lean to infer which 0 we
-- have in mind, and by default it would be interpreted
-- as a natural number.
theorem neg_zero : (-0 : R) = 0 := by
  apply neg_eq_of_add_eq_zero
  rw [add_zero]

theorem neg_neg (a : R) : - -a = a := by
  rw [<-add_zero (- -a), <- add_right_neg a, add_comm,
      add_assoc, add_right_neg (-a), add_zero]
  done

end MyRing

-- Examples.
section
variable {R : Type _} [Ring R]

example (a b : R) : a - b = a + -b :=
  sub_eq_add_neg a b

end

-- no `by` here, it is the definition!
example (a b : ℝ) : a - b = a + -b :=
  rfl -- constructor of equality type
  -- Presenting it as a proof of a - b = a + -b
  -- forces Lean to unfold the definition and
  -- recognize both sides as being the same.

example (a b : ℝ) : a - b = a + -b := by
  rfl -- there is a `by` so this is a tactic

namespace MyRing
variable {R : Type _} [Ring R]

theorem self_sub (a : R) : a - a = 0 := by
  rw [<-add_right_neg a, sub_eq_add_neg a a]
  done

theorem one_add_one_eq_two : 1 + 1 = (2 : R) := by
  norm_num

theorem two_mul (a : R) : 2 * a = a + a := by
  have h : a + a = (1 + 1) * a := by
    nth_rw 1 [<- one_mul a]
    nth_rw 2 [<- one_mul a]
    rw [<-add_mul]
  rw [h, one_add_one_eq_two]
  done

end MyRing

section
variable (A : Type _) [AddGroup A]

#check (add_assoc : ∀ a b c : A, a + b + c = a + (b + c))
#check (zero_add : ∀ a : A, 0 + a = a)
#check (add_left_neg : ∀ a : A, -a + a = 0)

end

section
variable {G : Type _} [Group G]

#check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
#check (one_mul : ∀ a : G, 1 * a = a)
#check (mul_left_inv : ∀ a : G, a⁻¹ * a = 1)

namespace MyGroup

theorem mul_inv_cancel_left (a b : G) : b⁻¹ * b * a = a := by
  rw [mul_left_inv b, one_mul]
  done

theorem mul_right_inv (a : G) : a * a⁻¹ = 1 := by
  have h : (a * a⁻¹)⁻¹ * (a * a⁻¹ * (a * a⁻¹)) = 1 := by
    rw [mul_assoc, ← mul_assoc a⁻¹ a, mul_left_inv, one_mul, mul_left_inv]
  rw [← h, ← mul_assoc, mul_left_inv, one_mul]

theorem mul_one (a : G) : a * 1 = a := by
  rw [<-mul_left_inv a, <-mul_assoc,
      mul_right_inv, one_mul]
  done

theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  rw [ <-one_mul (a*b)⁻¹, <-mul_left_inv (a*b) ]

end MyGroup

end
