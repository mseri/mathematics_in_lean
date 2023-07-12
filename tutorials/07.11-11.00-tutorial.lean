-- this is a simplified version of C03

import Mathlib.Tactic
import Mathlib.Data.Real.Basic

/- Yesterday you learnt about tactics for manipulating equalities and
inequalities, like `rw`, `apply`, `exact`, `ring` and `calc` (and maybe more).

To make more complicated statements, we need to patch together
simpler expressions, like equalities and inequalities, using logical
connectives.

Today we're going to learn how to use expressions involving logical
terms, and prove them. -/
namespace Leiden
section
/- We start with universal quantifiers and implication statements.
These are kind of similar.

The universal quantifier is "for all", denoted `∀`, typed with \all
or \forall (well, or \al or \fo).

An implication statement is an "if... then... " statement. We can
express "`P` implies `Q`" with `P → Q`, typed \to or \r.

A proof of either kind of statement is a bit like a function. -/

variable (α : Type) (P : α → Prop)
#check ∀ x, P x

/- A term of type `∀ x, P x` is a function that eats a term `x : α`
and outputs a term of type `P x` - aka a proof of `P x`. -/

variable (P Q : Prop)
#check P → Q
end
/- A term of type `P → Q` is a function that eats a term (aka proof)
of type `P` and outputs a term/proof of `Q.` -/

/- So using a `∀` statement or a `→` statement is going to be like
applying a function, and proving a `∀` statement or a `→` statement
is going to be like defining a function. -/

/- We can chain multiple implications together; `→` associates to the
right. -/
#check ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε

theorem my_lemma : ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
  sorry
/- `my_lemma` is a function with 7 arguments. -/

section
variable (a b δ : ℝ)
variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

/- We can partially apply a function. -/
#check my_lemma a b δ
#check my_lemma a b δ h₀ h₁
#check my_lemma a b δ h₀ h₁ ha hb
/- 7 is a big number. Some of these arguments we can replace with
underscores. -/

end

/- When Lean can always infer earlier arguments from later ones, we
can indicate this with curly brackets, and declare the inferable
arguments implicit. -/
theorem my_lemma2 : ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
  sorry

section
variable (a b δ : ℝ)
variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

/- Now we don't even have to give underscores for `a, b, δ`. -/
#check my_lemma2 h₀ h₁ ha hb

end

/- So let's see how to prove a `∀` statement. -/
theorem my_lemma3 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
-- Now there's more information in the local context.
  sorry

theorem my_lemma4 {x y ε : ℝ} (epos : 0 < ε) (ele1 : ε ≤ 1) (xlt : |x| < ε)
  (ylt : |y| < ε) : |x * y| < ε := by
  sorry

/- Sometimes quantifiers are hidden under definitions. -/
def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

section
variable (f g : ℝ → ℝ) (a b : ℝ)

/- Let's prove a `∀` statement using some `∀` hypotheses. Note how we
define a function in the theorem statement. -/
example (hfa : FnUb f a) (hgb : FnUb g b) :
    FnUb (fun x ↦ f x + g x) (a + b) := by
  intro y
  dsimp
  apply add_le_add
  -- Now we have two goals; it's good practice to delineate them.
  · exact hfa y -- apply hfa or exact hfa _
  . exact hgb y -- apply hgb or exact hgb _
  done

/- Here's a proof in term mode. -/
theorem fnUb_add {f g : ℝ → ℝ} {a b : ℝ} (hfa : FnUb f a) (hgb : FnUb g b) :
    FnUb (fun x ↦ f x + g x) (a + b) :=
  fun y ↦ add_le_add (hfa y) (hgb y)

end

section
/- Next up is the existential quantifier: "there exists", denoted `∃`.
You can type it with \exists or just \ex. -/

variable (α : Type) (P : α → Prop)
#check ∃ x, P x

/- Again, we need to know how to prove an existence statement - how to
supply a witness `x` and a proof `P x` - and how to use one to add a
witness and hypothesis to the local context. -/
end

/- In tactic mode we can use the `use` tactic. -/
example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  use 5 / 2
  norm_num

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
  Exists.intro (5 / 2) (by norm_num)

/- In term mode, we use "anonymous constructor" notation. This lets us
create terms of a certain class of types concisely; Lean works out
from the declaration type what we mean by `⟨_, ..., _⟩` in each case. -/
example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
  ⟨5 / 2, by norm_num⟩

/- We can hide an existential under a definition. -/
def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

section

variable {f g : ℝ → ℝ}

/- To extract an `x` and a hypothesis `P x` from the statement
`∃ x, P x`, we can use the `rcases` tactic. Like `intro`, it can see
under definitions. -/
example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  rcases ubf with ⟨a, ubfa⟩
  rcases ubg with ⟨b, ubgb⟩
  -- use a + b
  -- apply fnUb_add ubfa ubgb
  exact Exists.intro (a+b) (fnUb_add ubfa ubgb)
  done

/- The tactic `rintro` is a combination of `intro` and `rcases`. -/
example : FnHasUb f → FnHasUb g → FnHasUb fun x ↦ f x + g x := by
  rintro ⟨a, ubfa⟩ ⟨b, ubgb⟩
  exact ⟨a + b, fnUb_add ubfa ubgb⟩

example : FnHasUb f → FnHasUb g → FnHasUb fun x ↦ f x + g x :=
  fun ⟨a, ubfa⟩ ⟨b, ubgb⟩ ↦ ⟨a + b, fnUb_add ubfa ubgb⟩

example : FnHasUb f → FnHasUb g → FnHasUb fun x ↦ f x + g x :=
  fun ⟨a, ubfa⟩ ⟨b, ubgb⟩ ↦ ⟨a + b, fnUb_add ubfa ubgb⟩

end

section

variable {α : Type _} [CommRing α]

/- We can apply an `∃` to multiple objects. -/
def SumOfSquares (x : α) :=
  ∃ a b, x = a ^ 2 + b ^ 2

theorem sumOfSquares_mul {x y : α} (sosx : SumOfSquares x)
  (sosy : SumOfSquares y) :
    SumOfSquares (x * y) := by
  rcases sosx with ⟨a, b, xeq⟩
  rcases sosy with ⟨c, d, yeq⟩
  rw [xeq, yeq] -- you can get rid of this with rfl
  -- When using `use` to provide multiple witnesses, we just separate them with a comma.
  -- use a * c - b * d, a * d + b * c
  -- ring
  exact ⟨a * c - b * d, a * d + b * c, by ring⟩

/- Often we want to extract a hypothesis `x = y` from `∃ x y, x = y` and
then rewrite `x = y` in the goal. An efficient way to do this is to name
the hypothesis `rfl : x = y`. -/
theorem sumOfSquares_mul' {x y : α} (sosx : SumOfSquares x) (sosy : SumOfSquares y) :
    SumOfSquares (x * y) := by
  rcases sosx with ⟨a, b, rfl⟩
  rcases sosy with ⟨c, d, rfl⟩
  exact ⟨a * c - b * d, a * d + b * c, by ring⟩

end


/- Now we'll discuss negation: statements of the form "not `P`".
We express this as `¬P`, and type `¬` with \not or just \n.
There's also the notation `A ≠ B`, meaning `¬(A = B)`, and typed using \ne.

The definition of `¬P` is `P → False`. Thus a proof of negation is a
function that eats a proof of `P` and gives a proof of `False`:
assuming `P` leads to a contradiction. Since we can view `¬P` as a
function type, this section might remind you of Section 1. -/
section
variable (a b : ℝ)

-- ¬(b < a) = ¬b < a
example (h : a < b) : ¬b < a := by
  intro h'
  have : a < a := lt_trans h h'
  -- apply lt_irrefl a this
  linarith

/- We can define an object in the local context using `let`. It's like
`have`, but for data. -/
example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  let f : ℝ → ℝ := fun _ ↦ 0
  -- We create a subgoal of `Monotone f` here; its proof must be indented.
  have monof : Monotone f := by
    intro a b _aleb
    -- dsimp -- to see why
    exact Eq.le rfl
  have h' : f 1 ≤ f 0 := by exact Eq.le rfl
  have h'' : 1 ≤ 0 := h monof h'
  linarith
end

section
variable {α : Type _} (P : α → Prop) (Q : Prop)

/- Implicitly in the earlier proofs we've been using statements like these: -/
example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  sorry

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  sorry

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  sorry

example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  sorry

/- But to prove the third one, we need an extra axiom. The axiom of choice
implies the law of excluded middle: that for all propositions `P`, either
`P` holds or `¬P` does.

From the law of excluded middle we can deduce that `¬¬P → P.` -/

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  by_contra h''
  exact h' ⟨x, h''⟩

end

section
variable (f : ℝ → ℝ)

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  sorry

/- It can be annoying to work with negation statements which contain
quantifiers. By applying the lemmas above, we can move the `¬` inside
the quantifiers and get a simpler statement. The tactic `push_neg` does
this for us. -/
example (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
  push_neg at h
  exact h

/- But `push_neg` can't see under definitions. -/
example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  unfold FnHasUb FnUb at h
  push_neg at h
  exact h

/- The tactic `contrapose` lets us prove a proposition by proving its
contrapositive. The tactic `contrapose!` does this too, but also calls
`push_neg`. -/
example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  contrapose! h
  exact h

end

section
variable (a : ℕ)

/- Now we've seen how to deal with propositions of the form `P → False`.
We sometimes also want to use the fact that `False → P`; this is true for
any `P`. -/

example (h : 0 < 0) : a > 37 := by
  exfalso
  apply lt_irrefl 0 h

end

/- Next let's learn about conjunction: "and", denoted `∧`.
We can type this with \and (or \an).

We'll see how to prove an "and" statement, and how to access the
lefthand and righthand side of an `∧` hypothesis. -/

/- As with `∃`, to prove an `∧` statement we need to provide two pieces
of information. The `constructor` tactic splits the goal into two new
goals: the lefthand proposition and the righthand one. -/
example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y := by
  constructor
  · assumption
  intro h
  apply h₁
  rw [h]

/- The `constructor` tactic is like the tactic mode version of an
anonymous constructor: -/
example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y :=
  ⟨h₀, fun h ↦ h₁ (by rw [h])⟩

/- Meanwhile, to split an `∧` hypothesis into two hypotheses, we
can use `rcases` again, as with `∃.` -/
example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  rcases h with ⟨h₀, h₁⟩
  contrapose! h₁
  exact le_antisymm h₀ h₁

/- We don't have to deconstruct an ∧ statement: we can still
access the left and right sides of `h` (unlike `∃`). -/
example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  intro h'
  apply h.right
  exact le_antisymm h.left h'

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x :=
  fun h' ↦ h.right (le_antisymm h.left h')

/- We can deal with an `∧` within a `∃` all in one anonymous constructor
(although `norm_num` can handle `∧`). -/
example : ∃ x : ℝ, 2 < x ∧ x < 4 :=
  ⟨5 / 2, by norm_num, by norm_num⟩

/- Prefixing a tactic with `<;>` calls it on all remaining goals. -/
example : ∃ x : ℝ, 2 < x ∧ x < 4 := by
  use 5 / 2
  constructor <;> norm_num

/- The `∧` symbol associates to the right. -/
example : ∃ m n : ℕ, 4 < m ∧ m < n ∧ n < 10 ∧ Nat.Prime m ∧ Nat.Prime n := by
  use 5
  use 7
  norm_num

/- We can also use `use` to prove an `∧` statement; we don't
have to provide both statements at once. -/
example {x y : ℝ} : x ≤ y ∧ x ≠ y → x ≤ y ∧ ¬y ≤ x := by
  rintro ⟨h₀, h₁⟩
  use h₀
  exact fun h' ↦ h₁ (le_antisymm h₀ h')

/- Next let's learn about bi-implication, "if and only if", and denoted
`↔`, which we can type \iff (or \if).
It isn't quite defined as an `∧` statement, but it's pretty close,
and `↔` can be treated the same. -/

example {x y : ℝ} (h : x ≤ y) : ¬y ≤ x ↔ x ≠ y := by
  constructor
  · contrapose!
    rintro rfl
-- Lean knows `≤` is reflexive, so `rfl` closes the goal `x ≤ x`.
    rfl
  contrapose!
  exact le_antisymm h

example {x y : ℝ} (h : x ≤ y) : ¬y ≤ x ↔ x ≠ y :=
  ⟨fun h₀ h₁ ↦ h₀ (by rw [h₁]), fun h₀ h₁ ↦ h₀ (le_antisymm h h₁)⟩

section


/- However, bi-implication leads a double life in Lean. Whilst it behaves
like `∧`, it also behaves like `=`.

Just like `rw` can replace `A` with `B` given a lemma `A = B`, it can
replace a proposition `P` with `Q` given a lemma `P ↔ Q.`-/

example (x : ℝ) : |x + 3| < 5 → -8 < x ∧ x < 2 := by
  rw [abs_lt]
  intro h
  constructor <;> linarith

end

/- Finally, let's learn about disjunction: "or" statements.
We denote it `∨` and type this \v or \or.

"Or" behaves a little differently to the connectives we've seen
so far. -/
section

variable {x y : ℝ}

/- There are two ways to prove `P ∨ Q` we can either prove `P`, or `Q`.
The tactics `left` and `right` let us tell Lean which of the two we
want to prove. -/
example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  nlinarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

/- `Or.inl` and `Or.inr` are the term mode versions of `left`
and `right`. -/
example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

/- Meanwhile, to deconstruct an `∨` hypothesis, we can use `rcases`.
This time, `rcases` creates multiple goals: it case-splits on whether
the lefthand side holds or the righthand side.

Notice we use different syntax than for `∧`. Basically, there are two ways
`P ∨ Q` can be true, and they both involve one piece of information; on
the other hand there is one way `P ∧ Q` can be true, and it involves two
pieces of information. -/
example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  . rw [abs_of_neg h]
    intro h; right; exact h

end

/- We can case split on a chain of `∨` statements too.
(Again, `∨` associates to the right). -/
example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  . right; exact xgt

/- Now we can see the power of `rcases`: if we have some `∃` statements
within an `∨` statement, we can case-split, extract witnesses and rewrite
hypotheses all in one line. -/
example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  . rw [mul_comm, mul_assoc]
    apply dvd_mul_right

/- Assuming the law of excluded middle, we can case-split on whether a
propsition is true. The theorem `em` stands for excluded middle. -/
example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  . contradiction

/- The tactic `by_cases` achieves the same thing. -/
example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

end Leiden

namespace Leiden_mio
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

end Leiden_mio