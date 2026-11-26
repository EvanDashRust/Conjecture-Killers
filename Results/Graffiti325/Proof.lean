import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Degrees
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.WellTotallyDominated
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-! Written on the Wall II, Conjecture 325. -/

namespace Graffiti325

open SimpleGraph
open scoped Sym2

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The closed neighborhood of the vertices of degree two. -/
def degreeTwoClosedNeighborhood : Set V :=
  {v | G.degree v = 2 ∨ ∃ w, G.degree w = 2 ∧ G.Adj v w}

private abbrev neighborhoodGraph := G.induce (degreeTwoClosedNeighborhood G)
private abbrev NeighborhoodComponent := (neighborhoodGraph G).ConnectedComponent

/-- The number of connected components of the corresponding induced subgraph. -/
noncomputable def componentCount : ℕ := Nat.card (NeighborhoodComponent G)

/-- The values being minimized in the original hypothesis. -/
def complementNeighborhoodSizes : Finset ℕ :=
  Gᶜ.edgeFinset.image (Gᶜ.non_edge_neighborhood_card)

omit [DecidableEq V] in
private theorem component_has_degree_two (C : NeighborhoodComponent G) :
    ∃ v : degreeTwoClosedNeighborhood G, G.degree v.val = 2 ∧
      (neighborhoodGraph G).connectedComponentMk v = C := by
  obtain ⟨v, rfl⟩ := Quot.exists_rep C
  rcases v.property with hv | ⟨w, hw, hadj⟩
  · exact ⟨v, hv, rfl⟩
  · let w' : degreeTwoClosedNeighborhood G := ⟨w, Or.inl hw⟩
    exact ⟨w', hw, ConnectedComponent.connectedComponentMk_eq_of_adj
      (G := neighborhoodGraph G) (v := w') (w := v) hadj.symm⟩

private noncomputable def componentVertices (C : NeighborhoodComponent G) : Finset V :=
  open scoped Classical in
  ((Finset.univ : Finset (degreeTwoClosedNeighborhood G)).filter
    (fun v => (neighborhoodGraph G).connectedComponentMk v = C)).map (Function.Embedding.subtype _)

omit [DecidableEq V] in
private theorem mem_componentVertices {C : NeighborhoodComponent G} {v : V} :
    v ∈ componentVertices G C ↔ ∃ h : v ∈ degreeTwoClosedNeighborhood G,
      (neighborhoodGraph G).connectedComponentMk ⟨v, h⟩ = C := by
  classical
  unfold componentVertices
  constructor
  · intro hv
    obtain ⟨w, hw, hEq⟩ := Finset.mem_map.mp hv
    change w.val = v at hEq
    subst v
    exact ⟨w.property, (Finset.mem_filter.mp hw).2⟩
  · rintro ⟨hv, hC⟩
    exact Finset.mem_map.mpr ⟨⟨v, hv⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hC⟩, rfl⟩

private theorem three_le_component_card (C : NeighborhoodComponent G) :
    3 ≤ (componentVertices G C).card := by
  classical
  obtain ⟨v, hv, hvC⟩ := component_has_degree_two G C
  obtain ⟨p, q, hpq, hNeighbors⟩ := Finset.card_eq_two.mp
    (show (G.neighborFinset v.val).card = 2 from hv)
  have hp : G.Adj v.val p := (G.mem_neighborFinset v.val p).mp (by simp [hNeighbors])
  have hq : G.Adj v.val q := (G.mem_neighborFinset v.val q).mp (by simp [hNeighbors])
  have hpMem : p ∈ degreeTwoClosedNeighborhood G := Or.inr ⟨v.val, hv, hp.symm⟩
  have hqMem : q ∈ degreeTwoClosedNeighborhood G := Or.inr ⟨v.val, hv, hq.symm⟩
  have hpC : p ∈ componentVertices G C := (mem_componentVertices G).mpr
    ⟨hpMem, (ConnectedComponent.connectedComponentMk_eq_of_adj
      (G := neighborhoodGraph G) (v := ⟨p, hpMem⟩) (w := v) hp.symm).trans hvC⟩
  have hqC : q ∈ componentVertices G C := (mem_componentVertices G).mpr
    ⟨hqMem, (ConnectedComponent.connectedComponentMk_eq_of_adj
      (G := neighborhoodGraph G) (v := ⟨q, hqMem⟩) (w := v) hq.symm).trans hvC⟩
  have hvMem : v.val ∈ componentVertices G C :=
    (mem_componentVertices G).mpr ⟨v.property, hvC⟩
  have hSub : {v.val, p, q} ⊆ componentVertices G C :=
    Finset.insert_subset hvMem (Finset.insert_subset hpC (Finset.singleton_subset_iff.mpr hqC))
  simpa [hp.ne, hq.ne, hpq] using Finset.card_le_card hSub

private abbrev complementUnion (a b : V) : Finset V :=
  Gᶜ.neighborFinset a ∪ Gᶜ.neighborFinset b

private theorem endpoint_mem_left {a b : V} (hab : Gᶜ.Adj a b) :
    a ∈ complementUnion G a b :=
  Finset.mem_union_right _ ((Gᶜ.mem_neighborFinset b a).mpr hab.symm)

private theorem endpoint_mem_right {a b : V} (hab : Gᶜ.Adj a b) :
    b ∈ complementUnion G a b :=
  Finset.mem_union_left _ ((Gᶜ.mem_neighborFinset a b).mpr hab)

private theorem two_le_union {a b : V} (hab : Gᶜ.Adj a b) :
    2 ≤ (complementUnion G a b).card := by
  have hSub : {a, b} ⊆ complementUnion G a b := Finset.insert_subset
    (endpoint_mem_left G hab) (Finset.singleton_subset_iff.mpr (endpoint_mem_right G hab))
  simpa [hab.ne] using Finset.card_le_card hSub

private theorem outside_endpoints_bound {a b : V} (hab : Gᶜ.Adj a b)
    (ha : a ∉ degreeTwoClosedNeighborhood G) (hb : b ∉ degreeTwoClosedNeighborhood G) :
    componentCount G + 2 ≤ (complementUnion G a b).card := by
  classical
  let U := complementUnion G a b
  let S := (Finset.univ : Finset (degreeTwoClosedNeighborhood G)).filter (fun v => G.degree v.val = 2)
  have hImage : S.image (neighborhoodGraph G).connectedComponentMk = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro C
    obtain ⟨v, hv, hvC⟩ := component_has_degree_two G C
    exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, hvC⟩
  have hCount : componentCount G ≤ S.card := by
    rw [componentCount, Nat.card_eq_fintype_card, ← Finset.card_univ, ← hImage]
    exact Finset.card_image_le
  have hSub : S.map (Function.Embedding.subtype _) ⊆ (U.erase a).erase b := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hv
    have hd := (Finset.mem_filter.mp hw).2
    have hwa : w.val ≠ a := fun h => ha (h ▸ w.property)
    have hwb : w.val ≠ b := fun h => hb (h ▸ w.property)
    have hna : ¬ G.Adj a w.val := fun h => ha (Or.inr ⟨w.val, hd, h⟩)
    have hU : w.val ∈ U := Finset.mem_union_left _
      ((Gᶜ.mem_neighborFinset a w.val).mpr ((G.compl_adj a w.val).mpr ⟨hwa.symm, hna⟩))
    exact Finset.mem_erase.mpr ⟨hwb, Finset.mem_erase.mpr ⟨hwa, hU⟩⟩
  have hLe := Finset.card_le_card hSub
  have haU : a ∈ U := endpoint_mem_left G hab
  have hbU : b ∈ U.erase a := Finset.mem_erase.mpr ⟨hab.ne.symm, endpoint_mem_right G hab⟩
  rw [Finset.card_map, Finset.card_erase_of_mem hbU, Finset.card_erase_of_mem haU] at hLe
  have hTwo : 2 ≤ U.card := two_le_union G hab
  change componentCount G + 2 ≤ U.card
  omega

private theorem inside_endpoint_bound {a b : V} (hab : Gᶜ.Adj a b)
    (ha : a ∈ degreeTwoClosedNeighborhood G) :
    3 * (componentCount G - 1) + 1 ≤ (complementUnion G a b).card := by
  classical
  let U := complementUnion G a b
  let C₀ := (neighborhoodGraph G).connectedComponentMk ⟨a, ha⟩
  let other := (Finset.univ : Finset (NeighborhoodComponent G)).erase C₀
  have hOther : other.card = componentCount G - 1 := by
    simp [other, componentCount, Nat.card_eq_fintype_card]
  have hDisjoint : (other : Set (NeighborhoodComponent G)).PairwiseDisjoint (componentVertices G) := by
    intro C _ D _ hCD
    apply Finset.disjoint_left.mpr
    intro v hvC hvD
    obtain ⟨_, hC⟩ := (mem_componentVertices G).mp hvC
    obtain ⟨_, hD⟩ := (mem_componentVertices G).mp hvD
    exact hCD (hC.symm.trans hD)
  have hSub : (other.biUnion (componentVertices G)) ⊆ U.erase a := by
    intro v hv
    obtain ⟨C, hC, hvC⟩ := Finset.mem_biUnion.mp hv
    obtain ⟨hvMem, hvEq⟩ := (mem_componentVertices G).mp hvC
    have hCne := Finset.ne_of_mem_erase hC
    have hva : v ≠ a := by
      rintro rfl
      exact hCne hvEq.symm
    have hna : ¬ G.Adj a v := fun h => hCne
      (hvEq.symm.trans (ConnectedComponent.connectedComponentMk_eq_of_adj
        (G := neighborhoodGraph G) (v := ⟨v, hvMem⟩) (w := ⟨a, ha⟩) h.symm))
    exact Finset.mem_erase.mpr ⟨hva, Finset.mem_union_left _
      ((Gᶜ.mem_neighborFinset a v).mpr ((G.compl_adj a v).mpr ⟨hva.symm, hna⟩))⟩
  have hCount : 3 * (componentCount G - 1) ≤ (other.biUnion (componentVertices G)).card := by
    rw [Finset.card_biUnion hDisjoint, ← hOther, Nat.mul_comm]
    calc
      other.card * 3 = ∑ _C ∈ other, (3 : ℕ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun C _ => three_le_component_card G C
  have hLe := Finset.card_le_card hSub
  rw [Finset.card_erase_of_mem (endpoint_mem_left G hab)] at hLe
  change _ ≤ U.card - 1 at hLe
  have hTwo : 2 ≤ U.card := two_le_union G hab
  change 3 * (componentCount G - 1) + 1 ≤ U.card
  omega

/-- Under the numerical hypothesis, the induced closed neighborhood has a
single component, and the complement edge has no other neighbors. -/
theorem componentCount_and_complementUnion {a b : V} (hab : Gᶜ.Adj a b)
    (h : (complementUnion G a b).card ≤ 1 + componentCount G) :
    componentCount G = 1 ∧ complementUnion G a b = {a, b} := by
  have hTwo := two_le_union G hab
  have hC : componentCount G = 1 := by
    by_cases ha : a ∈ degreeTwoClosedNeighborhood G
    · have hLe := inside_endpoint_bound G hab ha
      omega
    · by_cases hb : b ∈ degreeTwoClosedNeighborhood G
      · have hLe := inside_endpoint_bound G hab.symm hb
        rw [show complementUnion G b a = complementUnion G a b from Finset.union_comm ..] at hLe
        omega
      · have hLe := outside_endpoints_bound G hab ha hb
        omega
  have hSub : {a, b} ⊆ complementUnion G a b := Finset.insert_subset
    (endpoint_mem_left G hab) (Finset.singleton_subset_iff.mpr (endpoint_mem_right G hab))
  refine ⟨hC, (Finset.eq_of_subset_of_card_le hSub ?_).symm⟩
  simpa [hab.ne, hC] using h

omit [Fintype V] in
private theorem minimal_pair {a b : V} (hab : a ≠ b) {D : Finset V}
    (hD : G.IsMinimalTotalDominatingSet D) (hSub : {a, b} ⊆ D)
    (hPair : G.IsTotalDominatingSet {a, b}) : D.card = 2 := by
  have hEq : {a, b} = D := by
    by_contra hn
    exact hD.2 _ (Finset.ssubset_iff_subset_ne.mpr ⟨hSub, hn⟩) hPair
  rw [← hEq]
  simp [hab]

omit [Fintype V] in
private theorem two_le_totalDominatingCard (v : V) {D : Finset V}
    (hD : G.IsTotalDominatingSet D) : 2 ≤ D.card := by
  obtain ⟨a, ha, _⟩ := hD v
  obtain ⟨b, hb, hab⟩ := hD a
  have hSub : {a, b} ⊆ D := Finset.insert_subset ha (Finset.singleton_subset_iff.mpr hb)
  simpa [hab.ne] using Finset.card_le_card hSub

omit [Fintype V] in
private theorem twin_in_dominating_set {a b : V} (hab : ¬ G.Adj a b)
    (hTwin : ∀ x, x ≠ a → x ≠ b → G.Adj a x ∧ G.Adj b x)
    {D : Finset V} (haD : a ∈ D) (hD : G.IsMinimalTotalDominatingSet D) : D.card = 2 := by
  obtain ⟨w, hwD, haw⟩ := hD.1 a
  have hwb : w ≠ b := fun h => hab (h ▸ haw)
  refine minimal_pair G haw.ne hD (Finset.insert_subset haD (Finset.singleton_subset_iff.mpr hwD)) ?_
  intro x
  by_cases hxa : x = a
  · exact ⟨w, by simp, hxa ▸ haw⟩
  by_cases hxb : x = b
  · exact ⟨w, by simp, hxb ▸ (hTwin w haw.ne.symm hwb).2⟩
  exact ⟨a, by simp, (hTwin x hxa hxb).1.symm⟩

private theorem minimal_card_of_hypothesis {a b : V} (hab : Gᶜ.Adj a b)
    (h : (complementUnion G a b).card ≤ 1 + componentCount G)
    {D : Finset V} (hD : G.IsMinimalTotalDominatingSet D) : D.card = 2 := by
  obtain ⟨hC, hU⟩ := componentCount_and_complementUnion G hab h
  have hTwin (x : V) (hxa : x ≠ a) (hxb : x ≠ b) : G.Adj a x ∧ G.Adj b x := by
    by_contra hNot
    have hMissing : x ∈ complementUnion G a b := by
      by_cases hAx : G.Adj a x
      · exact Finset.mem_union_right _
          ((Gᶜ.mem_neighborFinset b x).mpr ((G.compl_adj b x).mpr ⟨hxb.symm, fun hb => hNot ⟨hAx, hb⟩⟩))
      · exact Finset.mem_union_left _
          ((Gᶜ.mem_neighborFinset a x).mpr ((G.compl_adj a x).mpr ⟨hxa.symm, hAx⟩))
    rw [hU] at hMissing
    simp [hxa, hxb] at hMissing
  have hNonAdj := ((G.compl_adj a b).mp hab).2
  by_cases haD : a ∈ D
  · exact twin_in_dominating_set G hNonAdj hTwin haD hD
  by_cases hbD : b ∈ D
  · exact twin_in_dominating_set G (fun h' => hNonAdj h'.symm)
      (fun x hxb hxa => (hTwin x hxa hxb).symm) hbD hD
  classical
  have hCN : 0 < Fintype.card (NeighborhoodComponent G) := by
    simpa [componentCount, Nat.card_eq_fintype_card, hC] using show 0 < componentCount G by omega
  obtain ⟨C⟩ := Fintype.card_pos_iff.mp hCN
  obtain ⟨s, hs, _⟩ := component_has_degree_two G C
  have hLower := two_le_totalDominatingCard G a hD.1
  have hUpper : D.card ≤ 2 := by
    by_cases hsa : s.val = a
    · have hSub : D ⊆ G.neighborFinset a := by
        intro v hv
        exact (G.mem_neighborFinset a v).mpr (hTwin v (fun h' => haD (h' ▸ hv))
          (fun h' => hbD (h' ▸ hv))).1
      have haDeg : G.degree a = 2 := hsa ▸ hs
      simpa [haDeg] using Finset.card_le_card hSub
    by_cases hsb : s.val = b
    · have hSub : D ⊆ G.neighborFinset b := by
        intro v hv
        exact (G.mem_neighborFinset b v).mpr (hTwin v (fun h' => haD (h' ▸ hv))
          (fun h' => hbD (h' ▸ hv))).2
      have hbDeg : G.degree b = 2 := hsb ▸ hs
      simpa [hbDeg] using Finset.card_le_card hSub
    have hAdj := hTwin s.val hsa hsb
    have hSub : {a, b} ⊆ G.neighborFinset s.val :=
      Finset.insert_subset ((G.mem_neighborFinset s.val a).mpr hAdj.1.symm)
        (Finset.singleton_subset_iff.mpr ((G.mem_neighborFinset s.val b).mpr hAdj.2.symm))
    have hNeighbors : {a, b} = G.neighborFinset s.val :=
      Finset.eq_of_subset_of_card_le hSub (by simp [hs, hab.ne])
    obtain ⟨w, hw, hadj⟩ := hD.1 s.val
    have hMem := (G.mem_neighborFinset s.val w).mpr hadj
    rw [← hNeighbors] at hMem
    rcases Finset.mem_insert.mp hMem with rfl | hb
    · exact (haD hw).elim
    · have : w = b := Finset.mem_singleton.mp hb
      exact (hbD (this ▸ hw)).elim
  omega

omit [Fintype V] in
private theorem complete_isWellTotallyDominated (v : V)
    (hComplete : ∀ a b, a ≠ b → G.Adj a b) : G.IsWellTotallyDominated := by
  have hCard : ∀ D : Finset V, G.IsMinimalTotalDominatingSet D → D.card = 2 := by
    intro D hD
    obtain ⟨a, ha, _⟩ := hD.1 v
    obtain ⟨b, hb, hab⟩ := hD.1 a
    refine minimal_pair G hab.ne hD (Finset.insert_subset ha (Finset.singleton_subset_iff.mpr hb)) ?_
    intro x
    by_cases hxa : x = a
    · exact ⟨b, by simp, hxa ▸ hab⟩
    · exact ⟨a, by simp, hComplete x a hxa⟩
  intro S T hS hT
  rw [hCard S hS, hCard T hT]

/-- Written on the Wall II Conjecture 325. Complete graphs satisfy the
conclusion directly, without assigning any value to the minimum over no edges. -/
theorem conjecture325 [Nontrivial V] (_hConn : G.Connected)
    (h : ∀ hs : (complementNeighborhoodSizes G).Nonempty,
      (complementNeighborhoodSizes G).min' hs ≤ 1 + componentCount G) :
    G.IsWellTotallyDominated := by
  classical
  by_cases hEdges : Gᶜ.edgeFinset.Nonempty
  · have hs : (complementNeighborhoodSizes G).Nonempty := hEdges.image _
    have hMem := Finset.min'_mem _ hs
    obtain ⟨e, he, heMin⟩ := Finset.mem_image.mp hMem
    induction e using Sym2.inductionOn with
    | _ a b =>
      have hab : Gᶜ.Adj a b := mem_edgeFinset.mp he
      have hBound : (complementUnion G a b).card ≤ 1 + componentCount G := by
        change (complementUnion G a b).card = _ at heMin
        exact heMin ▸ h hs
      intro S T hS hT
      rw [minimal_card_of_hypothesis G hab hBound hS, minimal_card_of_hypothesis G hab hBound hT]
  · obtain ⟨v⟩ := (inferInstance : Nonempty V)
    apply complete_isWellTotallyDominated G v
    intro a b hne
    by_contra hn
    exact hEdges ⟨s(a, b), mem_edgeFinset.mpr ((G.compl_adj a b).mpr ⟨hne, hn⟩)⟩

#print axioms conjecture325

end Graffiti325
