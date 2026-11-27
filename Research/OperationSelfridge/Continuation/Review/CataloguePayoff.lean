import Mathlib.Tactic

namespace Selfridge

/-- Quadratic majorant used after the scalar convex comparison at a catalogue stage. -/
theorem centred_positive_part_majorant (x d a : ℝ) (ha : a < d) :
    max 0 (x - d) ≤ (x - a)^2 / (4 * (d - a)) := by
  have h : 0 < 4 * (d - a) := by linarith
  apply (le_div_iff₀ h).2
  rcases le_total x d with hx | hx
  · rw [max_eq_left (by linarith : x - d ≤ 0)]
    nlinarith [sq_nonneg (x-a)]
  · rw [max_eq_right (by linarith : 0 ≤ x - d)]
    nlinarith [sq_nonneg (x + a - 2*d)]

#print axioms centred_positive_part_majorant
end Selfridge
