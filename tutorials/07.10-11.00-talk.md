# Basic interaction with Lean4
## 1. Playing with prime numbers

```lean
theorem Euclid_Thm (n : ℕ) : ∃ p, n ≤ p ∧ Prime p := by
  let p := minFac (n ! + 1)
  have f1 : n ! + 1 ≠ 1 := Nat.ne_of_gt <| succ_lt_succ <| factorial_pos _
  have pp : Prime p :=  minFac_prime f1
  have np : n ≤ p :=
    le_of_not_ge fun h =>
      have h₁ : p ∣ n ! := dvd_factorial (minFac_pos _) h
      have h₂ : p ∣ 1 := (Nat.dvd_add_iff_right h₁).2 (minFac_dvd _)
      pp.not_dvd_one h₂
  exact ⟨p, np, pp⟩
```

+++ What does `Prime p` really mean?
We can use the command `#check` to... _check_ anything:
```lean
#check Prime 2
```
This only says that the _statement_ "2 is a prime number" is a `Prop`osition, it does not say anything about it being _true_ or _false_:

+++  let' s try
```lean
#check Prime 4
#check 4 ≤ 5
#check ∀ n m : ℕ, n ≤ m ∧ m ≤ n → m = 2 * n
```
The first and the third are false, the second is true, they all are `Prop`ositions.

Of course, we rather care about _truth_ values, and about distinguishing true from false `Prop`ositions.
+++ This we can sometimes achieve with the `#eval` command, although it's got its limits:
```lean
#eval 4 ≤ 5
#eval 1 + 1
#eval 2023^2023
#eval Prime 4
#eval Prime 2
#eval ∀ n m : ℕ, n ≤ m ∧ m ≤ n → m = 2 * n
+++
As its name suggests, `#eval` is primarly meant to *evaluate* numerical expressions, so it is **not** the main tool we will use to *prove* statements.

+++ Now we know `Prop`, but what are the _objects_ (like `2, n, 4`...) themselves? They are surely not `Prop`...
They are not, and this we can also check:

```lean
#check 36 + 1
#eval 36 + 1 -- the ℕ disappears
#check (37 : ℝ)
#check (π : ℕ)
```
+++ Isn't there an **obsession** with this character `:` ?
Sure there is. We will say more on this later; for the time being, if you are a mathematician, think that `:` means `∈`
+++

+++ OK for `Prop` and numbers; what about `ℝ` or `ℕ`?
Again, we can `#check`:
```lean
#check ℝ
#check Type
#check Type 1
#check Type 2
#check Prop
````
Ah, so perhaps we have a clue! There are really two levels of "containement" in the logical framework used by Lean: one is `x : A` and the other is `A : Type n` (or `A : Prop`). Terms/elements belong to **t**ypes, and **t*ypes belong to **T**ypes (or to `Prop`).

Indeed, there is a _hierarchy_ of the form
```lean
Prop : Type = Type 0 : Type 1 : Type 2 : Type 3 : ....
```
* `Prop` is the collection of **t**ypes that represent/are statements. A **t**ype `P : Prop` is a statement. It will have **one** term if it is true, and **no** terms if it is false: if it is true, all proofs carry the same truth value and produce the *same* term, while no proof ↔ no term.

* `Type n` is the collection of **t**ypes that represent mathematical objects. A **t**ype `A : Type n` (for some 0 ≤ n) is a collection of mathematical objects of "universe level `n`":
```lean
#check ℝ → ℕ
#check π
#check exp
#check (exp)
#check exp = (exp)
#check exp = (sin)
#check (ℝ≥0 → Type 4)
```
### One term cannot belong to two types!
+++

And now, let's go back to Euclid's theorem:
```lean
#check Euclid_Thm
```

+++ WHAT?
This is not a `Prop`? No, it is not:
* `Prop` are (represent... ) *statements*
* Their terms/elements are (represent... ) proof thereof.
* `Euclid_Thm` was a proof: it _belonged_ to something (of type `Prop`). To what?
+++
## 2. Theorems and definitions
+++ Definitions:
Using `def` you can define a *term* of some type (this term could also be a type in `Type n`...).
You do not need to specify the type if Lean is able to come up with it automatically.
```lean
def Euclid_Statement_n (n : ℕ) := ∃ p, n ≤ p ∧ Prime p
```
This is the _statement_ of Euclid's theorem.

+++It should belong to...
```lean
#check (Euclid_Statement_n 37)
#check (Euclid_Thm 37)
#check (Euclid_Thm 37 : (Euclid_Statement_n 37))
#check (Euclid_Thm 59 : (Euclid_Statement_n 37))
```

### Question
   Why `37`?! Can't we keep `n` as a variable?
### Answer
   _Yes, We Can_ (... ©)

+++ Another definition:
```lean
def Euclid_Statement_Forall := ∀ n : ℕ, ∃ p, n ≤ p ∧ Prime p
```
This is not really the same thing as `Euclid_Statement_n`, because `Euclid_Statement_Forall`
is `Prop` while `Euclid_For_n` is a _function_ that assigns to each `n : ℕ` a `Prop`:
```lean
#check Euclid_Statement_Forall
#check (Euclid_Statement_n)
#check Euclid_Statement_Forall = Euclid_Statement_n
#check (Euclid_Thm : Euclid_Statement_Forall)
#check ((fun n => Euclid_Thm n) : Euclid_Statement_Forall)

```

+++ Something harder:
Can you produce a term of the follwing type ?
```lean
(x y z : ℤ) (n : ℕ) (hn : 3 ≤ n)
  (H : x^n + y^n = z^n) : x * y * z = 0
```
If yes, you have done something nice.

+++If not
you can always write
```lean
theorem Fermat_Last_Theorem (x y z : ℤ) (n : ℕ) (hn : 3 ≤ n)
  (H : x^n + y^n = z^n) : x * y * z = 0 := sorry

def sqrt_2 : ℚ := sorry

#print axioms Fermat_Last_Theorem
```
So, `sorry` means: _I have a truly marvelous proof of this theorem which this VSCode Editor is too
narrow to contain._ (... ©).

You can use it to cheat!
+++

## 3. An experiment
+++ Let's try something easy:
```lean
example (X Y Z : Type 0) [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {f : X → Y}
    {g : Y → Z} (hf : Continuous f) (hg : Continuous g) : Continuous (g ∘ f) := by
```

+++ Really? Again with the `:` **obsession**?
It shows up
1. `X Y Z : Type 0`
2. `f : X → Y` and `g : Y → Z`
3. `hf : Continuous f` and `hg : Continuous g`
4. _TheWholeBlaBla_ `: Continuous (g ∘ f)`
* There is also a `:=` at the end, exactly as at the end of `Euclid_Statement_n` or of
`Euclid_Statement_Forall`

They all mean _the same thing!_ The gadget on the left is a term of the type on the right. In
particular the `example` is a/the term of type `Continuous (g ∘ f)`: how is it constructed?
Through the proof, after the `:=`, as in `def` (as it should be!).
+++

+++ As it should be?
```lean
example (X Y Z : Type 0) [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {f : X → Y}
    {g : Y → Z} (hf : Continuous f) (hg : Continuous g) : Continuous (g ∘ f) :=
  continuous_def.mpr fun U hU ↦ continuous_def.mp hf (g⁻¹' U) (continuous_def.mp hg U hU)
```
`continuous_def.mpr fun U hU => continuous_def.mp hf (g⁻¹' U) (continuous_def.mp hg U hU)` is the
term of type `Continuous (g ∘ f)` that we called `example` above, and
whose existence is guaranteed in the _context_ ( = under the assumptions)
1. `X Y Z : Type`
2. `f : X → Y` and `g : Y → Z`
3. `hf : Continuous f` and `hg : Continuous g`


### Question
   All this is very nice, but is it really a good idea to reinvent the wheel?

### Answer
*Yond Cassius has a `lean` and hungry look;*\
*He thinks too much, such men are dangerous* (... ©)
```lean
example (X Y Z : Type _) [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {f : X → Y}
    {g : Y → Z} (hf : Continuous f) (hg : Continuous g) : Continuous (g ∘ f) := by
  sorry
```
