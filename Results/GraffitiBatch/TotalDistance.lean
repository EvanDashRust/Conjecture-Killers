import Basic

/-! A transmission bound on the total domination number. -/

namespace GraffitiBatch

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def transmission (r : V) : ℕ := ∑ v, G.dist r v

omit [DecidableEq V] [DecidableRel G.Adj] in
private theorem minimum_root [Nonempty V] :
    ∃ r : V, ∀ x, transmission G r ≤ transmission G x := by
  obtain ⟨r, _, hr⟩ := exists_min_image (univ : Finset V) (transmission G) univ_nonempty
  exact ⟨r, fun x => hr x (mem_univ _)⟩

omit [DecidableRel G.Adj] in
theorem totalDomination_transmission [Nontrivial V] (hc : G.Connected) (r : V) :
    ∃ D, TotalDominates G D ∧ D.card ≤ 1 + (transmission G r + 2) / 3 := by
  classical
  let F : Finset V := univ.filter fun v => 2 ≤ G.dist r v
  have hr_not (v : V) (hv : v ∈ F) : v ≠ r := by
    intro h
    subst v
    simp [F] at hv
  have hw (v : V) (hv : v ∈ F) :
      ∃ u, G.Adj v u ∧ G.dist r u + 1 = G.dist r v :=
    distance_predecessor G hc r v (hr_not v hv)
  by_cases hF : F.Nonempty
  · let parent : V → V := fun v => if hv : v ∈ F then (hw v hv).choose else r
    have hp (v : V) (hv : v ∈ F) :
        G.Adj v (parent v) ∧ G.dist r (parent v) + 1 = G.dist r v := by
      simpa only [parent, dite_eq_left hv] using (hw v hv).choose_spec
    let P := F.image parent
    let D := insert r P
    have hpar (p : V) (hp' : p ∈ P) :
        ∃ v ∈ F, parent v = p := mem_image.mp hp'
    let child : V → V := fun p => if hp' : p ∈ P then (hpar p hp').choose else r
    have hch (p : V) (hp' : p ∈ P) : child p ∈ F ∧ parent (child p) = p := by
      simpa only [child, dite_eq_left hp'] using (hpar p hp').choose_spec
    have hrel (p : V) (hp' : p ∈ P) :
        G.dist r p + 1 = G.dist r (child p) := by
      have h := (hp (child p) (hch p hp').1).2
      rwa [(hch p hp').2] at h
    have hroot : r ∉ P := by
      intro h
      have hx : 2 ≤ G.dist r (child r) := (mem_filter.mp (hch r h).1).2
      have hy := hrel r h
      simp at hy
      omega
    let Q := P.filter fun v => G.dist r v = 1
    let C := P.image child
    have hCQ : Disjoint C Q := by
      apply Finset.disjoint_left.mpr
      intro v hv hq
      obtain ⟨p, hP, rfl⟩ := mem_image.mp hv
      have h₂ := (mem_filter.mp (hch p hP).1).2
      have h₁ := (mem_filter.mp hq).2
      omega
    have hcost (p : V) (hp' : p ∈ P) :
        3 ≤ G.dist r (child p) + (if G.dist r p = 1 then 1 else 0) := by
      have h₂ := (mem_filter.mp (hch p hp').1).2
      have h := hrel p hp'
      split <;> omega
    have h_child : ∑ p ∈ P, G.dist r (child p) = ∑ v ∈ C, G.dist r v := by
      symm
      apply sum_image
      intro x hx y hy he
      rw [← (hch x hx).2, ← (hch y hy).2, he]
    have h_first : (∑ p ∈ P, if G.dist r p = 1 then (1 : ℕ) else 0) =
        ∑ v ∈ Q, G.dist r v := by
      rw [← sum_filter]
      exact sum_congr rfl (fun x hx => ((mem_filter.mp hx).2).symm)
    have hcharge : 3 * P.card ≤ transmission G r := by
      calc
        3 * P.card = ∑ _p ∈ P, (3 : ℕ) := by simp [Nat.mul_comm]
        _ ≤ ∑ p ∈ P, (G.dist r (child p) + if G.dist r p = 1 then 1 else 0) :=
          sum_le_sum hcost
        _ = ∑ v ∈ C ∪ Q, G.dist r v := by rw [sum_add_distrib, h_child, h_first, sum_union hCQ]
        _ ≤ transmission G r := sum_le_sum_of_subset_of_nonneg (subset_univ _) (by simp)
    have hD : TotalDominates G D := by
      intro v
      by_cases hv : v = r
      · subst v
        obtain ⟨x, hx, hx_min⟩ := exists_min_image F (G.dist r) hF
        have h₁ := (hp x hx).2
        have h₂ := (mem_filter.mp hx).2
        have h₃ : G.dist r (parent x) < 2 := by
          by_contra! h
          have hle := hx_min (parent x) (mem_filter.mpr ⟨mem_univ _, h⟩)
          omega
        refine ⟨parent x, mem_insert_of_mem (mem_image_of_mem parent hx), ?_⟩
        exact G.dist_eq_one_iff_adj.mp (by omega)
      · by_cases hvF : v ∈ F
        · exact ⟨parent v, mem_insert_of_mem (mem_image_of_mem parent hvF), (hp v hvF).1⟩
        · have h₀ : G.dist r v ≠ 0 := by
            intro h
            exact hv ((hc.dist_eq_zero_iff).mp h).symm
          have h₂ : ¬ 2 ≤ G.dist r v := fun h => hvF (mem_filter.mpr ⟨mem_univ _, h⟩)
          exact ⟨r, mem_insert_self _ _, (G.dist_eq_one_iff_adj.mp (by omega)).symm⟩
    refine ⟨D, hD, ?_⟩
    dsimp only [D]
    rw [card_insert_of_notMem hroot]
    omega
  · obtain ⟨s, hrs⟩ := hc.preconnected.exists_adj_of_nontrivial r
    have hD : TotalDominates G ({r, s} : Finset V) := by
      intro v
      by_cases hvr : v = r
      · exact ⟨s, by simp, hvr ▸ hrs⟩
      · have h₀ : G.dist r v ≠ 0 := fun h => hvr ((hc.dist_eq_zero_iff).mp h).symm
        have h₂ : ¬ 2 ≤ G.dist r v :=
          fun h => hF ⟨v, mem_filter.mpr ⟨mem_univ _, h⟩⟩
        exact ⟨r, by simp, (G.dist_eq_one_iff_adj.mp (by omega)).symm⟩
    have hsum : 1 ≤ transmission G r := by
      rw [← G.dist_eq_one_iff_adj.mpr hrs]
      exact single_le_sum (f := G.dist r) (by simp) (mem_univ s)
    exact ⟨{r, s}, hD, by rw [card_pair hrs.ne]; omega⟩

omit [DecidableRel G.Adj] in
theorem conjecture310 [Nontrivial V] (hc : G.Connected) :
    ∃ r : V, (∀ x, transmission G r ≤ transmission G x) ∧
      ∃ D, TotalDominates G D ∧ D.card ≤ 1 + (transmission G r + 2) / 3 := by
  obtain ⟨r, hr⟩ := minimum_root G
  exact ⟨r, hr, totalDomination_transmission G hc r⟩

#print axioms conjecture310

end GraffitiBatch
