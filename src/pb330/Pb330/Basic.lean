-- Lecture 1 18.330
-- Introduction to Numerical Analysis Spring 2012 For information about citing
-- these materials or our Terms of Use, visit: http://ocw.mit.edu/terms
--
-- Remixed for use with the lean proof assistant by Derek A. Rhodes in 2024.

import Mathlib.Tactic.GCongr
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.EReal
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Basic
import Mathlib.Algebra.Group.Basic


-- A sequence is a function that maps the naturals to any type `α`.

def Sequence α := ℕ → α

-- Definition 1.
--
-- A sequence (a) is said to be ε-close to a number b if there
-- exists a number N ≥ 0, such that for all n ≥ N , |(a j) − b| ≤ ε.

-- That definition specialized for the rational numbers looks like this:

def εclose_rational (f: Sequence ℚ) (b ε: ℚ) := ∃ N, ∀ n ≥ N, |(f n) - b| ≤ ε

-- εclose_rational is a function that accepts three arguments. The first argument is a sequence. The
-- next two arguments are rationals b and ε. The function returns a proposition with S, b
-- and ε replaced with values of you choosing.

-- That definition only works for rational sequences, but we can make it more general for any
-- (Field α) by including some square bracketed terms to the definition. Here's the diff.

def εclose_rational₁                (f: Sequence ℚ) (b ε: ℚ) := ∃ N, ∀ n ≥ N, |(f n) - b| ≤ ε
--        +++++++++++++++++++++++++              +        +
def εclose' [Lattice α] [Field α] [LE α] (f: Sequence α) (b ε: α) := ∃ N, ∀ n ≥ N, |(f n) - b| ≤ ε
def εclose (f: Sequence ℝ) (b ε: ℝ) := ∃ N, ∀ n ≥ N, |(f n) - b| ≤ ε

-- The [Lattice α] says that all numbers of type α need to support Lattice axioms.
-- The [Field α] says that all numbers of type α need to support the Field axioms.
-- The [LE α] says that all numbers of type α need to support the (≤) operation.

-- Notice that the `ℚ` symbols have be replaced with `α` in the general definition. For now, imagine
-- `α` is, in some sense referring to any one of ℝ, ℂ, ℚ, ....

-- (If you have some other objects, such as: `cups of tea`, and you've endowed them with the
-- necessary axioms, then you could use `cups of tea` in place of numbers in this definition)

-- A sequence s₁ is said to converge to b if it is ε-close to b for all ε > 0 (however small).

-- here is a sequence s₁ : ℕ ↦ ℚ.

def s₁ (n:ℕ): ℚ := n / (n+2)

-- show that s₁ is εclose to 1 with ε = 1/22

-- example : εclose s₁ 1 (1/22) := by
--   unfold εclose
--   use 42 -- this was determined by inspecting the plot n/(n+2)
--   intro n hn
--   rw [s₁, abs_le]
--   constructor
--   · induction_from_starting_point n, hn with k hk IH
--     · norm_num
--     · norm_num at *
--       have h₁ : (k/(k+2)) ≤ ((k+1)/(k+3):ℚ) := by
--         rw [div_le_div_iff]
--         · calc k * (k + (3:ℚ))
--             _= k^2 + 3*k := by ring
--             _≤ k^2 + 3*k + 2 := by extra
--             _= (k+1)*(k+2) := by ring
--         · linarith
--         · linarith

--       calc (1:ℚ)
--         _≤  (k/(k+2)) + 1/22 := IH
--         _≤ (k+1)/(k+3) + (1/22) := by rel [h₁]
--         _= ((k+1)/(k + 1 + 2)) + 1/22 := by ring

--   · induction_from_starting_point n, hn with k hk IH
--     · norm_num
--     · norm_num at *
--       rw [div_le_div_iff] -- cross multiply
--       · linarith
--       · extra
--       · numbers
--   done



lemma div_self_add (a:ℝ) (h: 0 < a) : (1 + a) / (1 + a) = (1:ℝ) := by
  rw [div_self]
  linarith

lemma div_self_add_one_lt (a: ℝ) (h: 0 < a) : a / (1 + a) < a := by
  have h₀ : 1 < 1 + a := by linarith
  calc a / (1 + a)
    _= a / (1 + a) * 1 := by ring
    _< (a / (1 + a)) * (1 + a) := by rel [h₀]
    _= a * ((1 + a) / (1 + a)) := by ring
    _= a * (1:ℝ) := by conv => lhs; rhs; rw [div_self_add a h];
    _= a := by ring


noncomputable
def s₂ (n:ℕ): ℝ := 1 / n

--------------------------------------
-- !Definition!
--
-- A sequence converges to b when εclose holds for all ε > 0.

def converges_to (S: Sequence ℝ) (b: ℝ) := ∀ ε > 0, εclose S b ε

example : converges_to (s₂) 0 := by
  unfold converges_to
  intro ε hε
  unfold εclose
  use ⌈1/ε + 1⌉₊
  intro n hn
  rw [abs_le]

  norm_num at *
  unfold s₂
  have h₁ : 0 < ε⁻¹ := by exact inv_pos_of_pos hε

  constructor
  · -- case: -ε ≤ s₂ n - 0
    rw [le_div_iff']
    have h₄ : ↑n * -ε = - (↑n * ε) := by exact mul_neg (↑n) ε
    rw [h₄]
    nlinarith

    calc 0
      _< ε⁻¹ := h₁
      _< ε⁻¹ + 1 := by linarith
      _≤ n := hn

  · -- case s₂ n - 0 ≤ ε
    apply one_div_le_one_div_of_le at hn
    have h₀ : ε⁻¹ = 1/ε := by exact inv_eq_one_div ε
    have h₁ : ε / ε = 1 := by rw [div_eq_one_iff_eq]; exact Ne.symm (ne_of_lt hε)
    have h₄ : ε / (1 + ε) < ε := by exact div_self_add_one_lt ε hε

    have h₂ :=
      calc ε⁻¹ + (1:ℝ)
        _= (1/ε + 1) := by conv => rhs; lhs; rw [←h₀]
        _= (1/ε + ε/ε) := by exact congrArg (HAdd.hAdd (1 / ε)) (id (Eq.symm h₁))
        _= (1 + ε)/ε := by exact div_add_div_same 1 ε ε

    have h₃ :=
      calc (1:ℝ) / ↑n
        _≤ 1 / (ε⁻¹ + 1) := hn
        _= 1 / ((1 + ε) / ε) := by conv => lhs; rhs; rw [h₂]
        _= ε / (1 + ε) := by exact one_div_div (1 + ε) ε
        _< ε := by exact h₄
    · linarith
    · linarith
