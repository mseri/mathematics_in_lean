import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Real.Basic

noncomputable section

namespace Structures

-- this creates a new type Point
@[ext] -- the extensionality annotation allows one to derive equality properties
structure Point where
  x : ℤ
  y : ℤ
  z : ℤ
deriving Repr -- curently Repr is broken for reals

#check Point.ext -- this ext in practice contains equality

def myPoint1 : Point where
  x := 1
  y := -2
  z := 4

def myPoint2 :=
  Point.mk 1 (-2) 4 -- the constructor is defined with Point

def myPoint3 : Point :=
  ⟨1, -2, 4⟩ -- the ⟨ ⟩ pattern match over the constructor arguments

#check myPoint3.x
#eval myPoint3.x

namespace Point

-- to define functions it is convenent to use the syntactic sugar
def add (a b : Point) : Point :=
  ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

#check Point.add myPoint1 myPoint2
#eval Point.add myPoint1 myPoint2

#check Point.add
#check myPoint1.add
#check myPoint1.add myPoint2
#eval myPoint1.add myPoint2

end Point
--some proofs

namespace Point

protected theorem add_comm (a b : Point) : add a b = add b a := by
  unfold add
  ext <;> dsimp -- Look at the individual fields
  repeat' apply add_comm -- Use add_comm from the integers
  done

example (a b : Point) : add a b = add b a := by simp [add, add_comm]

-- you can do defs with pattern matching
theorem addAlt : Point -> Point -> Point
  | ⟨x₁, y₁, z₁⟩, ⟨x₂, y₂, z₂⟩ => ⟨x₁ + x₂, y₁ + y₂, z₁ + z₂⟩

theorem addAlt_eq_add : add = addAlt := by rfl

end Point

structure StandardTwoSimplex where
  x : ℝ
  y : ℝ
  z : ℝ
  x_nonneg : 0 ≤ x
  y_nonneg : 0 ≤ y
  z_nonneg : 0 ≤ z
  sum_eq : x + y + z = 1

namespace StandardTwoSimplex

def midpoint (a b : StandardTwoSimplex) : StandardTwoSimplex where
  x := (a.x + b.x) / 2
  y := (a.y + b.y) / 2
  z := (a.z + b.z) / 2
  x_nonneg := by
    apply div_nonneg
    . apply add_nonneg
      . exact a.x_nonneg
      . exact b.x_nonneg
    . norm_num
  y_nonneg := by linarith [a.y_nonneg, b.y_nonneg]
  z_nonneg := by linarith [a.z_nonneg, b.z_nonneg]
  sum_eq := by field_simp; linarith [a.sum_eq, b.sum_eq]

end StandardTwoSimplex

-- We can do the same with // subtyping:
def StandardTwoSimplex' :=
  { p : ℝ × ℝ × ℝ // 0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.1 + p.2.1 + p.2.2 = 1 }
-- you can see that this really reads like a set definition, but since we are in
-- type theory we don't talk about types but about sets

open BigOperators

-- structures can depend on parameters
structure StandardSimplex (n : ℕ) where
  V : Fin n -> ℝ -- {0 ... n-1}
  NonNeg : ∀ i : Fin n, 0 ≤ V i
  sum_eq_one : (∑ i, V i) = 1

namespace StandardSimplex

def midpoint (n : ℕ) (a b : StandardSimplex n) : StandardSimplex n
    where
  V i := (a.V i + b.V i) / 2
  NonNeg := by
    intro i
    apply div_nonneg
    · linarith [a.NonNeg i, b.NonNeg i]
    norm_num
  sum_eq_one := by
    simp [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_add_distrib,
      a.sum_eq_one, b.sum_eq_one]
    field_simp

end StandardSimplex