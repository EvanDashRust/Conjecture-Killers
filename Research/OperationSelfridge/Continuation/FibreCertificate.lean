import Mathlib.Tactic
import Mathlib.Data.Rat.Defs

namespace Selfridge

/-- Arithmetic check for the two directed-rounding distortion budgets. -/
theorem fibre_distortion_margins :
    (49430035371464777 : ℚ) / 200000000000000000 +
        3414799652875517 / 1000000000000000000 +
        1948 / 1000000000 < 1 - 7494 / 10000 ∧
    (155215858847967653 : ℚ) / 200000000000000000 +
        14170653052843397 / 1000000000000000000 +
        8082310506662 / 1000000000000000000 < 1 - 2097 / 10000 := by
  norm_num

/-- The single projected class and double-intersection bounds used for 5. -/
theorem five_fibre_margins :
    (10 : ℚ) / 49 < 2097 / 10000 ∧
    (2 : ℚ) / 27 < 2097 / 10000 ∧
    (20 : ℚ) / 441 < 2 / 27 ∧
    (4 : ℚ) / 27 < 2097 / 10000 := by
  norm_num

/-- Conditional union bounds and the last two-row intersection margin. -/
theorem five_pair_margins :
    (2 : ℚ) / 27 + 40 / 441 < 2097 / 10000 ∧
    (2 : ℚ) / 3 * (10 / 49 + (1 - 10 / 49) * (10 / 77)) < 2097 / 10000 ∧
    (2 : ℚ) / 27 + (2 / 3 - 2 / 27) * (10 / 49) < 2097 / 10000 ∧
    (20 : ℚ) / 147 + 20 / 441 < 2097 / 10000 ∧
    (40 : ℚ) / 231 < 2097 / 10000 ∧
    (2320 : ℚ) / 33957 + 20 / 147 < 2097 / 10000 := by
  norm_num

/-- The forced 5-fibre count profile in the remaining seven-token case. -/
theorem five_fibre_profile (a b c d e : ℕ)
    (pos : 1 ≤ a) (ab : a ≤ b) (bc : b ≤ c) (_cd : c ≤ d)
    (de : d ≤ e) (two : 2 ≤ d) (total : a + b + c + d + e ≤ 7) :
    a = 1 ∧ b = 1 ∧ c = 1 ∧ d = 2 ∧ e = 2 := by
  omega

theorem five_fibre_at_most_nine (a b c d e : ℕ)
    (apos : 1 ≤ a) (bpos : 1 ≤ b) (cpos : 1 ≤ c)
    (two : 2 ≤ d) (total : a + b + c + d + e ≤ 9) :
    e ≤ 4 := by
  omega

/-- The rounded finite 3-adic volume budgets under small-modulus exclusions. -/
theorem conditional_volume_margins :
    ∀ x ∈ ([747680281, 740921499, 746882288, 746153578, 749352364,
      742838116, 748994712] : List ℕ), (x : ℚ) / 1000000000 < 7494 / 10000 := by
  norm_num

#print axioms fibre_distortion_margins
#print axioms five_fibre_margins
#print axioms five_pair_margins
#print axioms five_fibre_profile
#print axioms five_fibre_at_most_nine
#print axioms conditional_volume_margins
end Selfridge
