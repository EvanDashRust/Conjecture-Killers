import Mathlib.Tactic

namespace OperationSelfridge.HeadQuantile

/-- The fractional-restriction inequality at a single atom. Summing with the
ambient probability measure bounds the hinge on any chosen submeasure. -/
theorem restrict_hinge (b y u w : ℝ) (hy : y ≤ u) (hw : 0 ≤ w) (hw1 : w ≤ 1) :
    w * max (b-y) 0 ≤ w * (u-y) + max (b-u) 0 := by
  have h : max (b-y) 0 ≤ (u-y) + max (b-u) 0 := by
    apply max_le
    · linarith [le_max_left (b-u) (0:ℝ)]
    · linarith [le_max_right (b-u) (0:ℝ)]
  calc
    _ ≤ w * ((u-y) + max (b-u) 0) := mul_le_mul_of_nonneg_left h hw
    _ = w * (u-y) + w * max (b-u) 0 := by ring
    _ ≤ _ := by
      have := mul_le_mul_of_nonneg_right hw1 (le_max_right (b-u) (0:ℝ))
      linarith

/-- The analytic and Python outputs are inputs to this arithmetic check. -/
theorem orbit_two_missing_23_margin :
    (45 : ℚ) / 68 -
      (65797962514143156449 / 100000000000000000000 +
       56096830242012333 / 50000000000000000000 +
       142785430665193108280065077439 / 14812546567897096200000000000000000)
    > 26535 / 10000000 := by norm_num

theorem no29_phase_margin :
    (1 : ℚ)/135 + 1/75 - 1/675 > 53/200 - 1/4 := by norm_num

#print axioms restrict_hinge
#print axioms orbit_two_missing_23_margin
#print axioms no29_phase_margin
end OperationSelfridge.HeadQuantile
