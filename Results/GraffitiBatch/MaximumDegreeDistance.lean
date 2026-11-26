import Basic

/-! Written on the Wall II, 271. A total dominating set must meet each
radius-two neighborhood of a geodesic in at least two vertices. -/

namespace GraffitiBatch

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem adjoining_levels (h : G.Connected) (r : V) {u v : V} (he : G.Adj u v) :
    G.dist r u ≤ G.dist r v + 1 ∧ G.dist r v ≤ G.dist r u + 1 := by
  have h₁ := h.dist_triangle (u := r) (v := v) (w := u)
  have h₂ := h.dist_triangle (u := r) (v := u) (w := v)
  rw [G.dist_eq_one_iff_adj.mpr he.symm] at h₁
  rw [G.dist_eq_one_iff_adj.mpr he] at h₂
  exact ⟨h₁, h₂⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem exists_at_level (hc : G.Connected) (r y : V) (t : ℕ) (ht : t ≤ G.dist r y) :
    ∃ v, G.dist r v = t := by
  generalize he : G.dist r y = k at ht
  induction k using Nat.strong_induction_on generalizing y with
  | ind k ih =>
    by_cases h : t = k
    · exact ⟨y, he.trans h.symm⟩
    · have hy : y ≠ r := by
        intro hy
        subst y
        simp at he
        omega
      obtain ⟨v, _, hv⟩ := distance_predecessor G hc r y hy
      exact ih (G.dist r v) (by omega) v rfl (by omega)

private noncomputable def band (r : V) (D : Finset V) (t : ℕ) : Finset V := by
  classical
  exact D.filter fun v => G.dist r v ≤ t + 2 ∧ t ≤ G.dist r v + 2

omit [Fintype V] [DecidableRel G.Adj] in
private theorem band_card [Nonempty V] (hc : G.Connected) (r y : V)
    (D : Finset V) (hD : TotalDominates G D) (t : ℕ) (ht : t ≤ G.dist r y) :
    2 ≤ (band G r D t).card := by
  obtain ⟨v, hv⟩ := exists_at_level G hc r y t ht
  obtain ⟨a, ha, hva⟩ := hD v
  obtain ⟨b, hb, hab⟩ := hD a
  have h₁ := adjoining_levels G hc r hva
  have h₂ := adjoining_levels G hc r hab
  have hsub : ({a, b} : Finset V) ⊆ band G r D t := by
    intro w hw
    rcases mem_insert.mp hw with rfl | hw
    · exact mem_filter.mpr ⟨ha, by omega, by omega⟩
    · have he : w = b := mem_singleton.mp hw
      subst w
      exact mem_filter.mpr ⟨hb, by omega, by omega⟩
  simpa [card_pair hab.ne] using card_le_card hsub

omit [Fintype V] [DecidableRel G.Adj] in
private theorem geodesic_bands [Nonempty V] (hc : G.Connected) (x y : V)
    (D : Finset V) (hD : TotalDominates G D) :
    2 * (G.dist x y / 5 + 1) ≤ D.card := by
  classical
  let I := range (G.dist x y / 5 + 1)
  have hdisj : (↑I : Set ℕ).PairwiseDisjoint (fun i => band G x D (5 * i)) := by
    intro i _ j _ hne
    apply Finset.disjoint_left.mpr
    intro v hi hj
    have h₁ := (mem_filter.mp hi).2
    have h₂ := (mem_filter.mp hj).2
    omega
  have hsub : I.biUnion (fun i => band G x D (5 * i)) ⊆ D := by
    intro v hv
    obtain ⟨i, _, hi⟩ := mem_biUnion.mp hv
    exact (mem_filter.mp hi).1
  calc
    2 * (G.dist x y / 5 + 1) = ∑ _i ∈ I, (2 : ℕ) := by simp [I, Nat.mul_comm]
    _ ≤ ∑ i ∈ I, (band G x D (5 * i)).card := by
      apply sum_le_sum
      intro i hi
      have hi' : i < G.dist x y / 5 + 1 := mem_range.mp hi
      exact band_card G hc x y D hD _ (by omega)
    _ = (I.biUnion (fun i => band G x D (5 * i))).card := (card_biUnion hdisj).symm
    _ ≤ D.card := card_le_card hsub

omit [Fintype V] [DecidableRel G.Adj] in
private theorem four_vertices [Nonempty V] (hc : G.Connected) (x y : V)
    (D : Finset V) (hD : TotalDominates G D) (hfour : D.card = 4) :
    G.dist x y ≤ 8 := by
  by_contra! hd
  let A := band G x D 0
  let B := band G x D (G.dist x y)
  have ha : 2 ≤ A.card := band_card G hc x y D hD 0 (Nat.zero_le _)
  have hb : 2 ≤ B.card := band_card G hc x y D hD _ (Nat.le_refl _)
  have hdj : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro v hA hB
    have h₁ := (mem_filter.mp hA).2
    have h₂ := (mem_filter.mp hB).2
    omega
  obtain ⟨w, hw⟩ := exists_at_level G hc x y 4 (by omega)
  obtain ⟨u, hu, hwu⟩ := hD w
  have hlevels := adjoining_levels G hc x hwu
  have huAB : u ∉ A ∪ B := by
    intro hes
    rcases mem_union.mp hes with hA | hB
    · have hh := (mem_filter.mp hA).2
      omega
    · have hh := (mem_filter.mp hB).2
      omega
  have hsub : insert u (A ∪ B) ⊆ D := by
    intro v hv
    rcases mem_insert.mp hv with rfl | hv
    · exact hu
    · exact (mem_union.mp hv).elim (fun h => (mem_filter.mp h).1) fun h => (mem_filter.mp h).1
  have hcount := card_le_card hsub
  rw [card_insert_of_notMem huAB, card_union_of_disjoint hdj] at hcount
  omega

private theorem two_vertices (hc : G.Connected) {x y : V}
    (hx : G.degree x = G.maxDegree) (hy : G.degree y = G.maxDegree)
    (D : Finset V) (hD : TotalDominates G D) (htwo : D.card = 2) :
    G.dist x y ≤ 2 := by
  classical
  obtain ⟨a, b, hab, hDab⟩ := card_eq_two.mp htwo
  have hU : G.neighborFinset a ∪ G.neighborFinset b = univ := by
    apply eq_univ_of_forall
    intro v
    obtain ⟨w, hw, hvw⟩ := hD v
    rw [hDab] at hw
    rcases mem_insert.mp hw with rfl | hw
    · exact mem_union_left _ ((G.mem_neighborFinset _ _).mpr hvw.symm)
    · have he := mem_singleton.mp hw
      subst w
      exact mem_union_right _ ((G.mem_neighborFinset _ _).mpr hvw.symm)
  have hcount := card_union_le (G.neighborFinset a) (G.neighborFinset b)
  rw [hU, card_univ, card_neighborFinset_eq_degree, card_neighborFinset_eq_degree] at hcount
  have ha := G.degree_le_maxDegree a
  have hb := G.degree_le_maxDegree b
  by_contra! hd
  have hxy : x ≠ y := fun e => by subst y; simp at hd
  have hnadj : ¬ G.Adj x y := fun e => by
    have := G.dist_eq_one_iff_adj.mpr e
    omega
  have hdisj : Disjoint (G.neighborFinset x) (G.neighborFinset y) := by
    apply Finset.disjoint_left.mpr
    intro w hwx hwy
    have h₁ := G.dist_eq_one_iff_adj.mpr ((G.mem_neighborFinset _ _).mp hwx)
    have h₂ := G.dist_eq_one_iff_adj.mpr ((G.mem_neighborFinset _ _).mp hwy).symm
    have ht := hc.dist_triangle (u := x) (v := w) (w := y)
    omega
  have hout : x ∉ G.neighborFinset x ∪ G.neighborFinset y := by
    simp [G.adj_comm (u := y), hnadj]
  have hone := card_le_univ (insert x (G.neighborFinset x ∪ G.neighborFinset y))
  rw [card_insert_of_notMem hout, card_union_of_disjoint hdisj,
    card_neighborFinset_eq_degree, card_neighborFinset_eq_degree, hx, hy] at hone
  omega

/-- Written on the Wall II, 271. Squaring the ceiling-square-root bound gives
this equivalent integer inequality for each pair of maximum-degree vertices. -/
theorem conjecture271 (hc : G.Connected) (D : Finset V) (hD : TotalDominates G D)
    (x y : V) (hx : G.degree x = G.maxDegree) (hy : G.degree y = G.maxDegree) :
    2 * G.dist x y ≤ D.card ^ 2 := by
  have : Nonempty V := ⟨x⟩
  have h := geodesic_bands G hc x y D hD
  by_cases hsmall : D.card < 5
  · by_cases h₂ : D.card = 2
    · have hb := two_vertices G hc hx hy D hD h₂
      rw [h₂]
      omega
    · by_cases h₃ : D.card = 3
      · rw [h₃]
        omega
      · have h₄ : D.card = 4 := by omega
        have hb := four_vertices G hc x y D hD h₄
        rw [h₄]
        omega
  · have hle : 2 * G.dist x y ≤ 5 * D.card := by omega
    exact hle.trans (by
      rw [pow_two]
      exact Nat.mul_le_mul_right _ (by omega))

#print axioms conjecture271

end GraffitiBatch
