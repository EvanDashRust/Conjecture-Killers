import Mathlib.Tactic

namespace Selfridge

/-- Number of pairs of head exponents in a divisor that is coprime to 3
or coprime to 5. The maximal exponents in the comparison integer are a and b. -/
theorem joint_head_count (a b : Nat) :
    (∑ i ∈ Finset.range (a + 1),
        ∑ j ∈ Finset.range (b + 1), (if i = 0 ∨ j = 0 then 1 else 0 : Nat))
      = 1 + a + b := by
  induction a with
  | zero => simp [Nat.add_comm]
  | succ a ih =>
    rw [Finset.sum_range_succ, ih]
    simp; omega

theorem joint_distortion_margins :
    (39615689492392598063 : ℚ) / 50000000000000000000 +
        316429597374516867 / 100000000000000000000 +
        6754 / 1000000000 < 1 - 204515 / 1000000 ∧
    (24715174747441069111 : ℚ) / 25000000000000000000 +
        200162657855850601 / 50000000000000000000 +
        8544 / 1000000000 < 1 - 7381 / 1000000 := by norm_num

#print axioms joint_head_count
#print axioms joint_distortion_margins
end Selfridge
