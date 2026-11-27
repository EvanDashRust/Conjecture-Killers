import Mathlib.Tactic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped BigOperators

namespace Selfridge

theorem linear_payoff_half {threshold budget load : ℝ}
    (threshold_lt_one : threshold < 1) (budget_cap : threshold ≤ 1 - 2 * budget)
    (load_large : 1 - budget ≤ load) :
    (1 : ℝ) / 2 ≤ max (load - threshold) 0 / (1 - threshold) := by
  apply (le_div_iff₀ (by linarith)).2
  exact (show (1 : ℝ) / 2 * (1 - threshold) ≤ load - threshold by linarith).trans
    (le_max_left _ _)

theorem square_payoff_half {budget load : ℝ}
    (remaining_nonneg : 0 ≤ 1 - budget) (enough : (1 : ℝ) / 2 ≤ (1 - budget)^2)
    (load_large : 1 - budget ≤ load) : (1 : ℝ) / 2 ≤ load^2 :=
  enough.trans (by
    have := mul_le_mul load_large load_large remaining_nonneg (remaining_nonneg.trans load_large)
    simpa [pow_two] using this)

theorem unique_heavy_coordinate {Q : Type*} [DecidableEq Q]
    (ps : Finset Q) (cost : Q → ℝ) (nonnegative : ∀ p ∈ ps, 0 ≤ cost p)
    (small : ∑ p ∈ ps, cost p < 1)
    {p q : Q} (hp : p ∈ ps) (hq : q ∈ ps)
    (cp : (1 : ℝ) / 2 ≤ cost p) (cq : (1 : ℝ) / 2 ≤ cost q) : p = q := by
  by_contra distinct
  have included : ({p,q} : Finset Q) ⊆ ps := by
    intro i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hp
    · simpa using Finset.mem_singleton.1 hi ▸ hq
  have bound : ∑ v ∈ ({p,q} : Finset Q), cost v ≤ ∑ v ∈ ps, cost v :=
    Finset.sum_le_sum_of_subset_of_nonneg included (fun v hv _ => nonnegative v hv)
  simp [distinct] at bound
  linarith

/-- Assign each crossing class to one coordinate that escapes its forbidden values. -/
theorem avoid_assigned_classes {Q C : Type*} [DecidableEq Q] [Fintype C]
    (V : Q → Type*) [∀ q, DecidableEq (V q)]
    (allowed : ∀ q, Finset (V q)) (forbidden : C → ∀ q, Finset (V q))
    (assigned : C → Q)
    (load : ∀ q, (∑ c ∈ Finset.univ.filter (fun c => assigned c = q),
       (forbidden c q).card) < (allowed q).card) :
    ∃ x : ∀ q, V q,
      (∀ q, x q ∈ allowed q) ∧ (∀ c, x (assigned c) ∉ forbidden c (assigned c)) := by
  let reserved (q : Q) := (Finset.univ.filter (fun c => assigned c = q)).biUnion
    (fun c => forbidden c q)
  have choose (q : Q) : ∃ x, x ∈ allowed q ∧ x ∉ reserved q := by
    have hcard : (reserved q).card < (allowed q).card :=
      Finset.card_biUnion_le.trans_lt (load q)
    exact Finset.exists_mem_notMem_of_card_lt_card hcard
  choose x hx hr using choose
  refine ⟨x,hx,?_⟩
  intro c hf
  apply hr (assigned c)
  exact Finset.mem_biUnion.2 ⟨c, by simp, hf⟩

#print axioms linear_payoff_half
#print axioms square_payoff_half
#print axioms unique_heavy_coordinate
#print axioms avoid_assigned_classes
end Selfridge
