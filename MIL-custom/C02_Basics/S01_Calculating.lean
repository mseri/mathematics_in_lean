-- An example.
import Mathlib.Tactic
import Mathlib.Data.Real.Basic

example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]

-- Try these.
example (a b c : ℝ) : c * b * a = b * (a * c) := by
  rw [mul_assoc]
  rw [mul_comm]
  rw [mul_assoc]
  done

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  -- you can use
  -- apply mul_left_comm
  -- or rewrite
  rw [<-mul_assoc] -- without arguments, the rewrite tactic tries to match the left-hand side with an expression in the goal, using the first pattern it finds.
  rw [mul_comm a b] -- now I need to specify a and b, otherwise it goes to the wrong place
  rw [mul_assoc]
  done

-- An example.
example (a b c : ℝ) : a * b * c = b * c * a := by
  rw [mul_assoc]
  rw [mul_comm]

/- Try doing the first of these without providing any arguments at all,
   and the second with only one argument. -/
example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  rw [mul_comm]
  rw [mul_assoc]
  done

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [<-mul_assoc]
  rw [mul_comm a]
  rw [mul_assoc]
  done

-- Using facts from the local context.
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h']
  rw [← mul_assoc]
  rw [h]
  rw [mul_assoc]

example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  rw [mul_assoc a, h, <-mul_assoc]
  -- with commas I can group tactics

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  rw [mul_comm] at hyp
  rw [hyp'] at hyp
  rw [sub_self] at hyp
  exact hyp
  done

-- can be done also simpler
example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  rw [hyp] -- this rewrite in c instead
  rw [hyp']
  rw [mul_comm]
  rw [sub_self]

-- Examples.
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]

-- We can delimit the scope of the declaration by putting it
-- in a section ... end block
section

variable (a b c d e f : ℝ)
-- we can declare variables once and for all outside
-- an example or theorem

example (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]

end

section
variable (a b c : ℝ)

#check a
#check a + b
#check (a : ℝ)
#check mul_comm a b
#check (mul_comm a b : a * b = b * a)
#check mul_assoc c a b
#check mul_comm a
#check mul_comm

end

section
variable (a b : ℝ)

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  rw [mul_add, add_mul, add_mul]
  rw [← add_assoc, add_assoc (a * a)]
  rw [mul_comm b a, ← two_mul]

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    -- _ stands for rhs of previous calc term
    _ = a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc, add_assoc (a * a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]

#check two_mul

-- an expression that begins with calc is a proof term.
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [<-add_assoc, add_assoc (a * a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm a b, ← two_mul]

end

-- Try these. For the second, use the theorems listed underneath.
section
variable (a b c d : ℝ)

example : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  rw [add_mul, mul_add, mul_add, <-add_assoc]

example : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  calc
    (a + b) * (c + d) = a * (c + d) + b * (c + d) := by
      rw [add_mul]
    _ = a * c + a * d + (b * c + b * d) := by
      repeat rw [mul_add]
    _ = a * c + a * d + b * c + b * d := by
      rw [<- add_assoc]
  done

example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  calc
    (a + b) * (a - b) = a ^ 2 - a * b + b * a - b ^ 2 := by
      rw [add_mul, mul_sub, mul_sub, add_sub]
      rw [pow_two a, pow_two b]
    _ = a^2 - b^2 := by
      rw [mul_comm b a, sub_add_cancel]
  done

example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  rw [add_mul, mul_sub, mul_comm a b, mul_sub] -- a * a - b * a + (b * a - b * b) = a ^ 2 - b ^ 2
  rw [<-add_sub_assoc, sub_add_comm, sub_self (b * a)] -- 0 + a * a - b * b = a ^ 2 - b ^ 2
  rw [add_comm, add_zero] -- a * a - b * b = a ^ 2 - b ^ 2
  repeat rw [pow_two]
  done

#check sub_add_comm
#check pow_two a
#check mul_sub a b c
#check add_mul a b c
#check add_sub a b c
#check sub_sub a b c
#check add_zero a
end

-- Examples.

section
variable (a b c d : ℝ)

example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp'] at hyp
  rw [mul_comm d a] at hyp
  rw [← two_mul (a * d)] at hyp
  rw [← mul_assoc 2 a d] at hyp
  exact hyp
  -- the exact tactic can use hyp to solve the goal because
  -- at that point hyp matches the goal exactly

example : c * b * a = b * (a * c) := by
  ring
  -- the ring tactic is designed to prove identities in any commutative ring
  -- as long as they follow purely from the ring axioms, without using any
  -- local assumption.

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring

end

example (a b c : ℕ) (h : a + b = c) : (a + b) * (a + b) = a * c + b * c := by
  nth_rw 2 [h]
  rw [add_mul]
