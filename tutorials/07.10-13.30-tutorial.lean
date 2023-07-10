import Mathlib.GroupTheory.Commutator
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

-- mathematics in lean, chapter 2
-- two tactics:
-- * rewriting, and
-- * applying (reducing goal to something that implies it)
--
-- There are helper tactics suggesting names to you (rw?, apply?)
-- this also helps getting the gist of the name conventions.
--
-- ⁅ ⁆ to disambiguate, written with "backslash square bracket minus minus"
example {G : Type} [Group G] (g h : G) : ⁅g,h⁆⁻¹=⁅h,g⁆ := by
  -- rw? solves it in one shot
  -- rw applies to the first thing that matches
  -- you can specify symbols that should be in the matched
  -- statement, e.g. later on you could ask rw [mul_assoc h g]
  -- to require that h then g need to be part of the statement
  -- or use nth_rw N rw ... to force the nth matching
  rw [commutatorElement_def] -- expands the LHS
  rw [commutatorElement_def] -- expands the RHS
  -- rw? gives lots of suggestions
  rw [mul_inv_rev]
  rw [mul_inv_rev]
  rw [mul_inv_rev]
  -- you can use
  -- repeat rw [mul_inv_rev]
  -- to avoid rewriting it mulitple times
  -- You want to use @ to make all things explicit:
  -- rw [@mul_inv_rev G]
  -- allows you to specify the structures
  rw [inv_inv] -- remove inverses of inverses
  rw [inv_inv]
  -- now we have brackets all over the place, we need to get rid of them
  -- and for that we need associativity
  rw [mul_assoc]
  -- rw [mul_assoc]
  -- note rw automatically also try reflexivity,
  -- to make that explicitly type "rewrite" instead
  rewrite [mul_assoc]
  exact rfl
  -- concluding the proof
  done

-- All of this can be done by using the group
example {G : Type} [Group G] (g h : G) : ⁅g,h⁆⁻¹=⁅h,g⁆ := by
  group
  done

-- Moving on to applying

open Real

example : Continuous (fun x ↦ (sin (x ^ 2) )^3 + cos ( 5 * x )) := by
  apply Continuous.add
  -- seems equivalent to
  -- refine Continuous.add ?hf ?hg
  apply Continuous.pow
  -- seems equivalent to
  -- refine Continuous.pow ?hf.h 3

  -- apply Continuous.comp
  -- this seems to make everyting complex
  -- then you need exact Complex.continuous_re

  -- you can make the proof clearer using bullet points
  -- like in coq:
  . apply Continuous.comp (_ : Continuous sin)
    . exact continuous_pow 2 -- then you need to specify which one
    . exact continuous_sin

  . apply Continuous.comp (_ : Continuous cos)
    . exact continuous_mul_left 5
    . exact continuous_cos
  done

example : Continuous (fun x ↦ (sin (x ^ 2) )^3 + cos ( 5 * x )) := by
  -- this is super super slow and proves it in a dumb way but works
  continuity?
  done