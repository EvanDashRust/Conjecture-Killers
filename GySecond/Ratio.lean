import Lean

namespace GySecond

/-- A later increment has smaller cross-ratio than any earlier prefix. -/
private theorem increment_vs_prefix (F H u v : Nat → Nat)
    (f0 : F 0 = 0) (h0 : H 0 = 0)
    (fstep : ∀ k, F (k+1) = F k + u k)
    (hstep : ∀ k, H (k+1) = H k + v k)
    (mono : ∀ i j : Nat, i ≤ j → u j * v i ≤ u i * v j)
    (j : Nat) {k : Nat} (hk : k ≤ j) : u j * H k ≤ F k * v j := by
  induction k with
  | zero => simp [f0, h0]
  | succ k ih =>
    rw [fstep, hstep, Nat.mul_add, Nat.add_mul]
    exact Nat.add_le_add (ih (by omega)) (mono k j (by omega))

/-- If the ratio of two sequences of increments decreases, so does the
ratio of their prefix sums. Cross products allow zero terms and empty sums. -/
theorem prefix_ratio_rec (F H u v : Nat → Nat) (f0 : F 0 = 0) (h0 : H 0 = 0)
    (fstep : ∀ k, F (k+1) = F k + u k)
    (hstep : ∀ k, H (k+1) = H k + v k)
    (mono : ∀ i j : Nat, i ≤ j → u j * v i ≤ u i * v j)
    {K L : Nat} (hKL : K ≤ L) : F L * H K ≤ F K * H L := by
  induction L with
  | zero =>
    have hk : K = 0 := by omega
    subst K
    exact Nat.le_refl _
  | succ l ih =>
    by_cases hk : K ≤ l
    · rw [fstep, hstep l, Nat.add_mul, Nat.mul_add]
      exact Nat.add_le_add (ih hk) (increment_vs_prefix F H u v f0 h0 fstep hstep mono l hk)
    · have heq : K = l + 1 := by omega
      subst K
      exact Nat.le_refl _

end GySecond

#print axioms GySecond.prefix_ratio_rec
