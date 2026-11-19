import GySecond.Basic
import GySecond.Monotone

namespace GySecond

/-- Specialize cap monotonicity at the two adjacent caps j−1 and j.
    The degrees count the blue and red steps, respectively. -/
theorem interior_product {n p j : ℕ} (hj : 2 ≤ j) (hjp : j < p) (hpn : p < n) :
    rhs n p j ≤ lhs n p j := by
  have h := gy_monotone (n - p) (p - j) (K := j - 1) (L := j) (by omega) (by omega)
  unfold gyF gyH at h
  have ep : j + (p - j) = p := by omega
  have epp : j - 1 + (p - j) = p - 1 := by omega
  have en : p + (n - p) = n := by omega
  have enp : p - 1 + (n - p) = n - 1 := by omega
  have en' : j + ((n - p) + (p - j)) = n := by omega
  have enp' : j - 1 + ((n - p) + (p - j)) = n - 1 := by omega
  simpa only [rhs, lhs, ep, epp, en, enp, en', enp',
    Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h

/-- The second-kind assertion of René Gy's Conjecture 2.1,
    over its full published index range. -/
theorem gy_second_kind (n p j : ℕ) (hj : 1 ≤ j) (hjp : j ≤ p) (hpn : p ≤ n) :
    Nat.stirlingSecond p j * Nat.stirlingSecond n p * Nat.stirlingSecond (n-1) (j-1) ≤
      Nat.stirlingSecond (p-1) (j-1) * Nat.stirlingSecond (n-1) (p-1) *
        Nat.stirlingSecond n j :=
  of_interior (fun _ _ _ h₁ h₂ h₃ => interior_product h₁ h₂ h₃) n p j hj hjp hpn

end GySecond

#print GySecond.gy_second_kind
#print axioms GySecond.gy_second_kind
