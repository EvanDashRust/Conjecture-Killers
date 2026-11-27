import Mathlib.Tactic

namespace Selfridge.Tail

/-- Aggregating all depths after the last fixed prefix preserves the capacity sum. -/
theorem exit_capacity_sum (h : ℕ) (r : ℝ) (hr : r ≠ 1) :
    (∑ j ∈ Finset.range h, r^(j+1)) + r^(h+1) / (1-r) = r / (1-r) := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [← ih, Finset.sum_range_succ]
    have hd : 1-r ≠ 0 := by intro he; apply hr; linarith
    rw [show h.succ + 1 = (h+1)+1 from rfl, pow_succ r (h+1)]
    field_simp
    ring

/-- The upper mass of two independent support events is monotone in either cap. -/
theorem pair_union_le (x y a b : ℝ) (hx : x ≤ a) (hy : y ≤ b)
    (hy1 : y ≤ 1) (ha1 : a ≤ 1) : x+y-x*y ≤ a+b-a*b := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy1),
             mul_nonneg (sub_nonneg.mpr hy) (sub_nonneg.mpr ha1)]

/-- Quadratic charge controlling the bad mass after reweighting an entire fibre. -/
theorem clipped_loss (x d : ℝ) (hd : 0 < d) (hu : d < 1) :
    max 0 (x-d) / (1-d) ≤ x^2 / (4*d*(1-d)) := by
  have h1 : 0 < 1-d := by linarith
  have h4 : 0 < 4*d := by positivity
  rw [div_mul_eq_div_div]
  apply (div_le_div_iff_of_pos_right h1).2
  apply (le_div_iff₀ h4).2
  rcases le_total x d with h | h
  · rw [max_eq_left (by linarith : x-d ≤ 0)]
    nlinarith [sq_nonneg x]
  · rw [max_eq_right (by linarith : 0 ≤ x-d)]
    nlinarith [sq_nonneg (x-2*d)]

#print axioms exit_capacity_sum
#print axioms pair_union_le
#print axioms clipped_loss
end Selfridge.Tail
