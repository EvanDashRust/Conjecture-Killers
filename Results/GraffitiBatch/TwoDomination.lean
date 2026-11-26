import Basic

/-! The open-neighborhood bounds of Written on the Wall II, 393b and 393c. -/

namespace GraffitiBatch

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem twoDominates_of_cover (S D : Finset V)
    (hS : S ⊆ D) (hOutside : univ \ openNeighbors G S ⊆ D)
    (hOnce : once G S ⊆ D) : TwoDominates G D := by
  intro v hv
  have hx : v ∈ openNeighbors G S := by
    by_contra h
    exact hv (hOutside (mem_sdiff.mpr ⟨mem_univ _, h⟩))
  obtain ⟨s, hs, hvs⟩ := (mem_openNeighbors G).mp hx
  have hpos : 0 < (G.neighborFinset v ∩ S).card :=
    card_pos.mpr ⟨s, mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hvs, hs⟩⟩
  have hne : (G.neighborFinset v ∩ S).card ≠ 1 :=
    fun h => hv (hOnce (mem_filter.mpr ⟨mem_univ _, h⟩))
  have hle : (G.neighborFinset v ∩ S).card ≤ (G.neighborFinset v ∩ D).card :=
    card_le_card (inter_subset_inter (Subset.rfl) hS)
  omega

/-- Written on the Wall II, 393c. The conclusion holds on every finite simple graph. -/
theorem conjecture393c :
    ∃ D, TwoDominates G D ∧ D.card ≤
      (univ \ openNeighbors G (supports G)).card + (supports G).card +
        (once G (pendants G ∪ supports G)).card := by
  let S := supports G
  let E := once G (pendants G ∪ S)
  let U := univ \ openNeighbors G S
  let D := U ∪ S ∪ E
  refine ⟨D, ?_, (card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _)⟩
  intro v hv
  have hU : v ∉ U := fun h => hv (mem_union_left _ (mem_union_left _ h))
  have hS : v ∉ S := fun h => hv (mem_union_left _ (mem_union_right _ h))
  have hE : v ∉ E := fun h => hv (mem_union_right _ h)
  have hx : v ∈ openNeighbors G S := by
    by_contra h
    exact hU (mem_sdiff.mpr ⟨mem_univ _, h⟩)
  obtain ⟨s, hs, hvs⟩ := (mem_openNeighbors G).mp hx
  have hEq : G.neighborFinset v ∩ (pendants G ∪ S) = G.neighborFinset v ∩ S := by
    ext w
    simp only [mem_inter, mem_union, G.mem_neighborFinset]
    exact ⟨fun ⟨h, hw⟩ => ⟨h, hw.resolve_left
      (fun hp => support_not_adjacent_to_pendant G hS hp h)⟩,
      fun ⟨h, hw⟩ => ⟨h, Or.inr hw⟩⟩
  have hpos : 0 < (G.neighborFinset v ∩ S).card :=
    card_pos.mpr ⟨s, mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hvs, hs⟩⟩
  have hne : (G.neighborFinset v ∩ S).card ≠ 1 :=
    fun h => hE (mem_filter.mpr ⟨mem_univ _, hEq ▸ h⟩)
  have hle : (G.neighborFinset v ∩ S).card ≤ (G.neighborFinset v ∩ D).card :=
    card_le_card (inter_subset_inter (Subset.rfl)
      (fun _ h => mem_union_left _ (mem_union_right _ h)))
  omega

private theorem induced_degree (S : Finset V) (v : (S : Set V)) :
    (G.induce (S : Set V)).degree v = (G.neighborFinset v ∩ S).card := by
  rw [← card_neighborFinset_eq_degree, ← card_map (Function.Embedding.subtype _)]
  congr 1
  ext w
  simp only [mem_map, mem_inter, G.mem_neighborFinset]
  constructor
  · rintro ⟨⟨u, hu⟩, ha, rfl⟩
    exact ⟨((G.induce (S : Set V)).mem_neighborFinset _ _).mp ha, hu⟩
  · rintro ⟨ha, hw⟩
    exact ⟨⟨w, hw⟩, ((G.induce (S : Set V)).mem_neighborFinset _ _).mpr ha, rfl⟩

/-- Written on the Wall II, 393b. Charge each additional support to the degree sum. -/
theorem conjecture393b :
    ∃ D, TwoDominates G D ∧ D.card ≤
      (univ \ openNeighbors G (supports G)).card +
        (G.induce (supports G : Set V)).edgeFinset.card + (once G (supports G)).card := by
  let S := supports G
  let U := univ \ openNeighbors G S
  let E := once G S
  let A := S \ (U ∪ E)
  let D := U ∪ E ∪ A
  have hS : S ⊆ D := by
    intro v hv
    by_cases h : v ∈ U ∪ E
    · exact mem_union_left _ h
    · exact mem_union_right _ (mem_sdiff.mpr ⟨hv, h⟩)
  have hlow (v : V) (hv : v ∈ A) : 2 ≤ (G.neighborFinset v ∩ S).card := by
    have hno := (mem_sdiff.mp hv).2
    have hx : v ∈ openNeighbors G S := by
      by_contra h
      exact hno (mem_union_left _ (mem_sdiff.mpr ⟨mem_univ _, h⟩))
    obtain ⟨w, hw, hvw⟩ := (mem_openNeighbors G).mp hx
    have hpos : 0 < (G.neighborFinset v ∩ S).card :=
      card_pos.mpr ⟨w, mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hvw, hw⟩⟩
    have hne : (G.neighborFinset v ∩ S).card ≠ 1 :=
      fun h => hno (mem_union_right _ (mem_filter.mpr ⟨mem_univ _, h⟩))
    omega
  let H := G.induce (S : Set V)
  let T : Finset (S : Set V) := univ.filter fun x => (x : V) ∈ A
  have hT : T.card = A.card := by
    rw [← card_map (Function.Embedding.subtype (· ∈ (S : Set V))) (s := T)]
    congr 1
    ext v
    simp only [T, mem_map, mem_filter, mem_univ, true_and,
      Function.Embedding.subtype_apply]
    constructor
    · rintro ⟨⟨x, hx⟩, ha, rfl⟩
      exact ha
    · exact fun hv => ⟨⟨v, (mem_sdiff.mp hv).1⟩, hv, rfl⟩
  have hcount : 2 * A.card ≤ 2 * H.edgeFinset.card := by
    calc
      2 * A.card = ∑ _v ∈ T, (2 : ℕ) := by simp [hT, Nat.mul_comm]
      _ ≤ ∑ v ∈ T, H.degree v := by
        apply sum_le_sum
        intro v hv
        rw [induced_degree G]
        exact hlow v (mem_filter.mp hv).2
      _ ≤ ∑ v, H.degree v := sum_le_sum_of_subset_of_nonneg (subset_univ _) (by simp)
      _ = 2 * H.edgeFinset.card := H.sum_degrees_eq_twice_card_edges
  have hD : D.card ≤ U.card + E.card + A.card :=
    (card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _)
  refine ⟨D, twoDominates_of_cover G S D hS
    (fun _ h => mem_union_left _ (mem_union_left _ h))
    (fun _ h => mem_union_left _ (mem_union_right _ h)), ?_⟩
  change D.card ≤ U.card + H.edgeFinset.card + E.card
  omega

#print axioms conjecture393b
#print axioms conjecture393c

end GraffitiBatch
