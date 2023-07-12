/-
Tutorial: Structures (Mathematics in Lean Chapter 6)
https://leanprover-community.github.io/mathematics_in_lean/C06_Structures.html

Adapted by Anne Baanen
-/

import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Real.Basic

/-
We have seen a few algebraic structures in Lean: groups and rings.
Today we're going to define our own structures,
and add an extra type of bracket to our arsenal: `[Group G]`.
-/

noncomputable section

namespace Structures

/-
In Lean, a `structure` specifies objects consisting of several pieces
of data bundled together, possibly with constraints on the data.
-/
@[ext] -- Generates `Point.ext`
structure Point where
  x : ℤ
  y : ℤ
  z : ℤ
deriving Repr

/-
This creates a new type `Point`, whose terms ("instances") are tuples
of the specified form.

Lean offers multiple ways of creating instances of structures.
-/
def myPoint1 : Point where
  x := 2
  y := -1
  z := 4

def myPoint2 :=
  Point.mk 2 (-1) 4

def myPoint3 : Point :=
  ⟨2, -1, 4⟩
/-
Recall the ⟨⟩ syntax in `rcases`.
-/

/- The fields of the tuple are accessed by name. -/
#check myPoint1.x
#eval myPoint1.x

#check Point.ext

namespace Point

/-
To define functions involving structures:
-/
def add (a b : Point) : Point :=
  ⟨Point.x a + b.x, a.y + b.y, a.z + b.z⟩

def add' (a b : Point) : Point where
  x := a.x + b.x
  y := a.y + b.y
  z := a.z + b.z

/-
These definitions are in the `Point` namespace.
When we `def add`, the namespace is prefixed:
the full name is `Point.add`.
While the namespace is open, we do not have to write this prefix.
-/

#check add myPoint1 myPoint2
#eval (add myPoint1 myPoint2)

end Point

/-
Outside of the namespace, we need to use the full name.
-/

#check Point.add myPoint1 myPoint2

/-
Recall anonymous projection notation:
-/
#check Point.x
#check myPoint1.x
#check Point.add
#check myPoint1.add myPoint2

namespace Point

/-
To prove equality of structure instances, the `ext` tactic is helpful:
-/
protected theorem add_comm (a b : Point) : add a b = add b a := by
  unfold add -- Unfold the definition
  ext <;> dsimp -- Look at the individual fields
  repeat' apply add_comm -- This is a fact about integer numbers

#check add_comm

example (a b : Point) : add a b = add b a := by simp [add, add_comm]

/- Lean can compute with structures, so many equalities hold instantly. -/
theorem add_x (a b : Point) : (a.add b).x = a.x + b.x :=
  rfl

/- You can also use pattern-matching to define functions. -/
def addAlt : Point → Point → Point
  | ⟨x₁, y₁, z₁⟩, ⟨x₂, y₂, z₂⟩ => ⟨x₁ + x₂, y₁ + y₂, z₁ + z₂⟩

/- The drawback is you often need to do the same pattern-match in
proofs: -/
theorem addAlt_eq_add : add = addAlt := rfl

/- The drawback is you often need to do the same pattern-match in
proofs: -/
theorem addAlt_x (a b : Point) : (a.addAlt b).x = a.x + b.x := by
  rfl

example (a b : Point) : addAlt a b = addAlt b a := by
  simp [addAlt, add_comm]

/- Actually, Lean 4 allows you to omit the `cases` above. -/

end Point

/- Lean treats data and proofs the same way, so we can put them in the
same structure. -/
structure StandardTwoSimplex where
  x : ℝ
  y : ℝ
  z : ℝ
  x_nonneg : 0 ≤ x
  y_nonneg : 0 ≤ y
  z_nonneg : 0 ≤ z
  sum_eq : x + y + z = 1

namespace StandardTwoSimplex

noncomputable section

/- To define an instance of a structure with proofs, we can use `by`
notation. -/
def midpoint (a b : StandardTwoSimplex) : StandardTwoSimplex
    where
  x := (a.x + b.x) / 2
  y := (a.y + b.y) / 2
  z := (a.z + b.z) / 2
  x_nonneg := by
    apply div_nonneg
    · apply add_nonneg
      · exact a.x_nonneg
      · exact b.x_nonneg
    · norm_num
  y_nonneg := by
    apply div_nonneg
    · exact add_nonneg a.y_nonneg b.y_nonneg
    · norm_num
  z_nonneg := by linarith [a.z_nonneg, b.z_nonneg]
    /- div_nonneg (add_nonneg a.z_nonneg b.z_nonneg)
    (by norm_num) /- Or term-mode proofs. -/ -/
  sum_eq := by field_simp; linarith [a.sum_eq, b.sum_eq]

end

end StandardTwoSimplex

open BigOperators

/- Structures can depend on parameters. -/
structure StandardSimplex (n : ℕ) where
  V : Fin n → ℝ -- `Fin n` has exactly `n` elements `0, ..., n-1`.
  NonNeg : ∀ i : Fin n, 0 ≤ V i
  sum_eq_one : (∑ i, V i) = 1

namespace StandardSimplex

def midpoint (n : ℕ) (a b : StandardSimplex n) : StandardSimplex n
    where
  V i := (a.V i + b.V i) / 2
    -- Equivalent: V := fun i ↦ (a.V i + b.V i) / 2
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

/- Structures can also bundle together properties without the data. -/
structure IsLinear (f : ℝ → ℝ) where
  is_additive : ∀ x y, f (x + y) = f x + f y
  preserves_mul : ∀ x c, f (c * x) = c * f x

section

variable (f : ℝ → ℝ) (linf : IsLinear f)

#check linf.is_additive

#check linf.preserves_mul

end

/- You can imagine a structure containing only data is a
cartesian product: -/
def Point'' :=
  ℝ × ℝ × ℝ

/- A structure containing only proofs is a conjunction: -/
def IsLinear' (f : ℝ → ℝ) :=
  (∀ x y, f (x + y) = f x + f y) ∧ ∀ x c, f (c * x) = c * f x

/- A structure combining data and proofs is like a subset: -/
def PReal :=
  { y : ℝ // 0 < y }
  -- But we're in type theory, not set theory,
  -- so the name is `Subtype`

section

variable (x : PReal)

#check x.val

#check x.property

#check x.1

#check x.2

end

/- Not using structures gets messy very quickly. -/
def StandardTwoSimplex' :=
  { p : ℝ × ℝ × ℝ //
    0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.1 + p.2.1 + p.2.2 = 1 }

def StandardSimplex' (n : ℕ) :=
  { v : Fin n → ℝ // (∀ i : Fin n, 0 ≤ v i) ∧ (∑ i, v i) = 1 }

/- When taking a product, the type of the second component can depend
on the first. -/
def StdSimplex := (n : ℕ) × StandardSimplex n
/- This is also called the `Σ` type. -/
def StdSimplex' := Σ (n : ℕ), StandardSimplex n

section

variable (s : StdSimplex)

#check s.fst
#check s.snd

#check s.1
#check s.2

end

end Structures










namespace Algebraic

/-
Mathlib defines algebraic structures using Lean `structure`s.
This should make sense: a group is a binary operator, an identity and
inverse operator (data)
such that these satisfy some properties (proofs).

We are used to writing `(G, *, 1, ⁻¹)` is a group.
In Lean it is generally nicer to make the carrier a parameter to the
structure.
`Group₁ α` is the collection of all group structures on `α`.
-/
structure Group₁ (α : Type _) where
  mul : α → α → α
  one : α
  inv : α → α
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  mul_one : ∀ x : α, mul x one = x
  one_mul : ∀ x : α, mul one x = x
  mul_left_inv : ∀ x : α, mul (inv x) x = one

/-
On the other hand, category theory prefers to make the carrier part of
the structure.
-/
structure Group₁Cat where
  α : Type _
  str : Group₁ α

/-
Let's define a group.
The type `Equiv α β`, notation `α ≃ β`,
contains equivalences between `α` and `β`:
the functions `f : α → β` that are bijections.

`Equiv.Perm α` are the permutations on a type `α`:
equivalences between
`α` and itself.
-/
example (α : Type _) : Equiv.Perm α = (α ≃ α) :=
  rfl

/-
These form a group under composition.
-/
def permGroup {α : Type _} : Group₁ (Equiv.Perm α)
    where
  mul f g := Equiv.trans g f
    -- Watch out for the order! `Equiv` is used like an
    -- "equivalence relation".
  one := Equiv.refl α
  inv := Equiv.symm
  mul_assoc f g h := by ext; simp
  one_mul := Equiv.trans_refl
  mul_one := Equiv.refl_trans
  mul_left_inv := Equiv.self_trans_symm

/- Lean tightly links the notation to the structure,
so `(G, *, 1, ⁻¹)` is different from `(G, +, 0, -)`. -/
structure AddGroup₁ (α : Type _) where
  (add : α → α → α)
  -- fill in the rest
section

/-
Lean knows about the `*` operator, and how to apply it to permutations.
It also knows about the fields of the `Group` structure.
-/
variable {α : Type _} (f g : Equiv.Perm α) (n : ℕ)

#check f * g
#check mul_assoc f g g⁻¹

#check @HMul.hMul

end

/-
How does Lean know this? When we write `f * g`, Lean needs to figure
out:
 1. The type of `f` and `g` is `Equiv.Perm α`
 2. Therefore we need a multiplication operator
    `· * · : Equiv.Perm α → Equiv.Perm α → Equiv.Perm α`
 3. A suitable choice for this operator comes from the group structure
    on `Equiv.Perm`

Step 1 and 2 are done using implicit parameters.
Step 3 uses the type class system.

A parameter between [square brackets] signals Lean to look in a big
database of `instance`s.
To register an instance in the database we need two changes.
-/

/-
`class` allows the structure to participate in the type class system
-/
class Group₂ (α : Type _) where
  mul : α → α → α
  one : α
  inv : α → α
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  mul_one : ∀ x : α, mul x one = x
  one_mul : ∀ x : α, mul one x = x
  mul_left_inv : ∀ x : α, mul (inv x) x = one

/- `instance` registers a fact into Lean's database. -/
instance {α : Type _} : Group₂ (Equiv.Perm α) where
  mul f g := Equiv.trans g f
  one := Equiv.refl α
  inv := Equiv.symm
  mul_assoc f g h := (Equiv.trans_assoc _ _ _).symm
  one_mul := Equiv.trans_refl
  mul_one := Equiv.refl_trans
  mul_left_inv := Equiv.self_trans_symm

/- Now we can use `Group₂.mul` to compose permutations. -/
#check Group₂.mul

def mySquare {α : Type _} [Group₂ α] (x : α) :=
  Group₂.mul x x

#check mySquare

section
variable {β : Type _} (f g : Equiv.Perm β)

example : Group₂.mul f g = g.trans f :=
  rfl

example : mySquare f = f.trans f :=
  rfl

end

open Structures

/- Lean's built in notation works using classes.
`x + y` abbreviates `Add.add x y`, and `Add` is a class. -/
instance : Add Point where add := Point.add

section
variable (x y : Point)

#check x + y

example : x + y = Point.add x y :=
  rfl

end

/-
A group structure implies a multiplication operator.
We tell Lean this fact by defining an instance.
-/
instance hasMulGroup₂ {α : Type _} [Group₂ α] : Mul α :=
  ⟨Group₂.mul⟩

#check @hasMulGroup₂

instance hasOneGroup₂ {α : Type _} [Group₂ α] : One α :=
  ⟨Group₂.one⟩

instance hasInvGroup₂ {α : Type _} [Group₂ α] : Inv α :=
  ⟨Group₂.inv⟩

section

variable {α : Type _} (f g : Equiv.Perm α)

#check f * 1 * g⁻¹

def foo : f * 1 * g⁻¹ = g.symm.trans ((Equiv.refl α).trans f) :=
  rfl

end

/-
We don't need to set this hierarchy up manually.
The `extends` keyword defines a structure based on another structure,
and does the right thing for `class`es.
-/

#check Semigroup
#check CommRing

end Algebraic

/-
Exercise: Gaussian integers
-/

end
