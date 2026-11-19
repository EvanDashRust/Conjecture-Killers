import GySecond.Encoding
import GySecond.Ratio

namespace GySecond

/-- If the two constituent ratios decrease, their sum still decreases when
the first summand carries the additional factor `(x+r)/x`. Cross products
keep every expression in the natural numbers. -/
private theorem increment_comparison
    {x y r ax ay bx by_ hx hy : ℕ} (hxy : x ≤ y)
    (ha : ay * hx ≤ ax * hy) (hb : by_ * hx ≤ bx * hy) :
    ((y+r)*ay + y*by_) * (x*hx) ≤ ((x+r)*ax + x*bx) * (y*hy) := by
  have hcoef : x*(y+r) ≤ y*(x+r) := by
    calc
      x*(y+r) = x*y + r*x := by rw [Nat.mul_add, Nat.mul_comm r x]
      _ ≤ x*y + r*y := Nat.add_le_add_left (Nat.mul_le_mul_left r hxy) _
      _ = y*(x+r) := by rw [Nat.mul_add]; ac_rfl
  calc
    ((y+r)*ay + y*by_) * (x*hx) =
        (x*(y+r))*(ay*hx) + (x*y)*(by_*hx) := by
      simp only [Nat.mul_add, Nat.add_mul]
      ac_rfl
    _ ≤ (y*(x+r))*(ax*hy) + (x*y)*(bx*hy) :=
      Nat.add_le_add (Nat.mul_le_mul hcoef ha) (Nat.mul_le_mul_left _ hb)
    _ = ((x+r)*ax + x*bx) * (y*hy) := by
      simp only [Nat.mul_add, Nat.add_mul]
      ac_rfl

/-- For fixed gaps `b,r`, the ratio `gyF b r k / gyH (b+r) k`
decreases with the column `k`. No division is used in the theorem. -/
theorem gy_monotone (b r : ℕ) : ∀ {K L : ℕ}, 1 ≤ K → K ≤ L →
    gyF b r L * gyH (b+r) K ≤ gyF b r K * gyH (b+r) L := by
  induction b generalizing r with
  | zero =>
    intro K L _ _
    simp [Nat.mul_comm]
  | succ b ihb =>
    induction r with
    | zero =>
      intro K L _ _
      simp [Nat.mul_comm]
    | succ r ihr =>
      intro K L _ hKL
      let u := fun k : ℕ =>
        (k+1+(r+1)) * gyF b (r+1) (k+1) + (k+1) * gyF (b+1) r (k+1)
      let v := fun k : ℕ => (k+1) * gyH (b+r+1) (k+1)
      have hdeg : (b+1)+(r+1) = (b+r+1)+1 := by omega
      apply prefix_ratio_rec (gyF (b+1) (r+1)) (gyH ((b+1)+(r+1))) u v
      · exact gyF_succ_succ_zero b r
      · rw [hdeg, gyH_succ_zero]
      · intro k
        simpa only [u, Nat.add_assoc] using gyF_step b r k
      · intro k
        rw [hdeg]
        exact gyH_step (b+r+1) k
      · intro i j hij
        have ha := ihb (r+1) (K := i+1) (L := j+1) (by omega) (by omega)
        have hb := ihr (K := i+1) (L := j+1) (by omega) (by omega)
        have ea : b+(r+1) = b+r+1 := by omega
        have eb : (b+1)+r = b+r+1 := by omega
        rw [ea] at ha
        rw [eb] at hb
        exact increment_comparison (Nat.succ_le_succ hij) ha hb
      · exact hKL

end GySecond
