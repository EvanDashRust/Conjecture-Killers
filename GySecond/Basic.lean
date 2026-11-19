import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Tactic.Ring

/-!
The left and right factors follow the order used by Gy, Conjecture 2.1.
We isolate the target as a proposition, without assuming it.
-/

namespace GySecond

local notation "S" => Nat.stirlingSecond

def lhs (n p j : ℕ) : ℕ := S (p-1) (j-1) * S (n-1) (p-1) * S n j
def rhs (n p j : ℕ) : ℕ := S p j * S n p * S (n-1) (j-1)

def PublishedTarget : Prop :=
  ∀ n p j : ℕ, 1 ≤ j → j ≤ p → p ≤ n →
    S p j * S n p * S (n-1) (j-1) ≤ S (p-1) (j-1) * S (n-1) (p-1) * S n j

theorem eq_at_p_eq_j (n j : ℕ) : lhs n j j = rhs n j j := by
  simp [lhs, rhs, Nat.stirlingSecond_self, Nat.mul_comm]

theorem eq_at_p_eq_n (n j : ℕ) : lhs n n j = rhs n n j := by
  simp [lhs, rhs, Nat.stirlingSecond_self, Nat.mul_comm]

private theorem zero_column {n : ℕ} (hn : 0 < n) : S n 0 = 0 := by
  cases n with
  | zero => omega
  | succ n => exact Nat.stirlingSecond_succ_zero n

theorem eq_at_j_eq_one {n p : ℕ} (hp : 1 ≤ p) (hpn : p ≤ n) :
    lhs n p 1 = rhs n p 1 := by
  by_cases h : p = 1
  · subst p
    exact eq_at_p_eq_j n 1
  · have hp' : 0 < p - 1 := by omega
    have hn' : 0 < n - 1 := by omega
    simp [lhs, rhs, zero_column hp', zero_column hn']

/-- Denominators on the positive Stirling triangle are nonzero. -/
theorem stirling_pos {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) : 0 < S n k := by
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
    cases k with
    | zero => omega
    | succ k =>
      by_cases h : k = n
      · subst k
        simp [Nat.stirlingSecond_self]
      · have hkn' : k + 1 ≤ n := by omega
        have hpos : 0 < S n (k+1) := ih (by omega) hkn'
        rw [Nat.stirlingSecond_succ_succ]
        exact Nat.add_pos_left (Nat.mul_pos (by omega) hpos) _

/-- It suffices to establish the strict interior, with the original weak conclusion. -/
theorem of_interior (h : ∀ n p j : ℕ, 2 ≤ j → j < p → p < n →
    rhs n p j ≤ lhs n p j) : PublishedTarget := by
  intro n p j hj hjp hpn
  change rhs n p j ≤ lhs n p j
  by_cases h₁ : j = 1
  · subst j
    exact (eq_at_j_eq_one hjp hpn).ge
  by_cases h₂ : p = j
  · subst p
    exact (eq_at_p_eq_j n j).ge
  by_cases h₃ : p = n
  · subst p
    exact (eq_at_p_eq_n n j).ge
  exact h n p j (by omega) (by omega) (by omega)

end GySecond
