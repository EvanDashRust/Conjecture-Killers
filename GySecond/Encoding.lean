import GySecond.Basic

/-! Along a fixed diagonal of the Stirling triangle the first difference is a
multiple of the preceding diagonal. Applying the discrete product rule gives the
two-dimensional recurrence below. All identities are subtraction-free. -/

namespace GySecond

/-- The Stirling numbers along the diagonal with excess `d`. -/
def gyH (d k : ℕ) : ℕ := Nat.stirlingSecond (k + d) k

/-- The numerator at column `k`, with successive index gaps `r` and `b`. -/
def gyF (b r k : ℕ) : ℕ := gyH b (k + r) * gyH r k

@[simp] theorem gyH_zero_degree (k : ℕ) : gyH 0 k = 1 := by
  simp [gyH, Nat.stirlingSecond_self]

@[simp] theorem gyH_succ_zero (d : ℕ) : gyH (d + 1) 0 = 0 := by
  simp [gyH, Nat.stirlingSecond_succ_zero]

@[simp] theorem gyF_zero_left (r k : ℕ) : gyF 0 r k = gyH r k := by
  simp [gyF]

@[simp] theorem gyF_zero_middle (b k : ℕ) : gyF b 0 k = gyH b k := by
  simp [gyF]

@[simp] theorem gyF_succ_succ_zero (b r : ℕ) : gyF (b+1) (r+1) 0 = 0 := by
  simp [gyF]

theorem gyH_pos (d k : ℕ) : 0 < gyH d (k+1) :=
  stirling_pos (by omega) (by omega)

theorem gyH_step (d k : ℕ) :
    gyH (d+1) (k+1) = gyH (d+1) k + (k+1) * gyH d (k+1) := by
  unfold gyH
  rw [show k+1+(d+1) = (k+(d+1))+1 by omega, Nat.stirlingSecond_succ_succ,
    show k+1+d = k+(d+1) by omega, Nat.add_comm]

theorem gyF_step (b r k : ℕ) :
    gyF (b+1) (r+1) (k+1) = gyF (b+1) (r+1) k +
      (k+1+(r+1))*gyF b (r+1) (k+1) + (k+1)*gyF (b+1) r (k+1) := by
  have hfirst :
      gyH (b+1) (k+1+(r+1)) = gyH (b+1) (k+(r+1)) +
        (k+1+(r+1))*gyH b (k+1+(r+1)) := by
    simpa only [show k+1+(r+1) = k+(r+1)+1 by omega] using gyH_step b (k+(r+1))
  unfold gyF
  rw [hfirst, gyH_step r k, show k+1+r = k+(r+1) by omega]
  ring

end GySecond
