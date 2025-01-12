import Mathlib



-- The following is an autoformalization provide by our model. It is `wrong` and the annotator shall correct it

/- The positive integers a and b are such that the numbers (15a + 16b) and (16a - 15b) are both squares of positive integers. What is the least possible value that can be taken on by the smaller of these two squares?-/
theorem number_theory_9019_incorrect:
    IsLeast {x : ℕ | ∃ a b : ℤ, a > 0 ∧ b > 0 ∧ x = min (15 * a + 16 * b) (16 * a - 15 * b)} 256 := by sorry

/- The positive integers a and b are such that the numbers (15a + 16b) and (16a - 15b) are both squares of positive integers. What is the least possible value that can be taken on by the smaller of these two squares?-/
theorem number_theory_9019_correct:
    IsLeast {x : ℕ | ∃ a b : ℤ, a > 0 ∧ b > 0 ∧ x = min (15 * a + 16 * b) (16 * a - 15 * b) ∧
    IsSquare (15 * a + 16 * b) ∧ IsSquare (16 * a - 15 * b)} (481 ^ 2) := by sorry
