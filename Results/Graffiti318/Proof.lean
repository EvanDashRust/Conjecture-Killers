import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.VertexDistance
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.WellTotallyDominated

/-! A proof of Written on the Wall II, Conjecture 318. -/

namespace Graffiti318

open SimpleGraph
open scoped Sym2

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A vertex at even distance is either the starting vertex or a neighbor in
the complement. -/
theorem distEven_le_complement_degree_add_one (v : V) :
    G.distEven v ≤ Gᶜ.degree v + 1 := by
  classical
  have hSub : (Finset.univ.filter (fun w => Even (G.dist v w))) ⊆
      insert v (Gᶜ.neighborFinset v) := by
    intro w hw
    by_cases hwv : w = v
    · rw [hwv]
      exact Finset.mem_insert_self v (Gᶜ.neighborFinset v)
    · apply Finset.mem_insert_of_mem
      apply (Gᶜ.mem_neighborFinset v w).mpr
      refine (G.compl_adj v w).mpr ⟨Ne.symm hwv, ?_⟩
      intro hadj
      have heven := (Finset.mem_filter.mp hw).2
      rw [G.dist_eq_one_iff_adj.mpr hadj] at heven
      exact (by decide : ¬ Even (1 : ℕ)) heven
  have hv : v ∉ Gᶜ.neighborFinset v := by simp
  have h := Finset.card_le_card hSub
  rw [Finset.card_insert_of_notMem hv, card_neighborFinset_eq_degree] at h
  exact h

private theorem complement_edge_away {v a b : V} (ha : a ≠ v) (hb : b ≠ v)
    (hab : a ≠ b) (hn : ¬ G.Adj a b) :
    s(a, b) ∈ Gᶜ.edgeFinset \ Gᶜ.incidenceFinset v := by
  have h := (G.compl_adj a b).mpr ⟨hab, hn⟩
  refine Finset.mem_sdiff.mpr ⟨mem_edgeFinset.mpr h, ?_⟩
  intro hc
  exact (((Gᶜ.mk'_mem_incidenceSet_iff).mp ((Gᶜ.mem_incidenceFinset v _).mp hc)).2).elim
    (fun he => ha he.symm) (fun he => hb he.symm)

/-- In a graph whose complement has at most one edge away from `v`, every
total dominating set contains a total dominating pair. -/
theorem contains_total_dominating_pair (v : V)
    (hAway : (Gᶜ.edgeFinset \ Gᶜ.incidenceFinset v).card ≤ 1)
    (D : Finset V) (hD : G.IsTotalDominatingSet D) :
    ∃ a b : V, a ≠ b ∧ {a, b} ⊆ D ∧ G.IsTotalDominatingSet {a, b} := by
  classical
  have uniqueNonedge {e f : Sym2 V}
      (he : e ∈ Gᶜ.edgeFinset \ Gᶜ.incidenceFinset v)
      (hf : f ∈ Gᶜ.edgeFinset \ Gᶜ.incidenceFinset v) : e = f :=
    Finset.card_le_one_iff.mp hAway he hf
  obtain ⟨a, haD, hva⟩ := hD v
  by_cases hPair : ∃ b ∈ D, b ≠ v ∧ G.Adj a b
  · obtain ⟨b, hbD, hbv, hab⟩ := hPair
    refine ⟨a, b, hab.ne, Finset.insert_subset haD (Finset.singleton_subset_iff.mpr hbD), ?_⟩
    intro x
    by_cases hxa : G.Adj x a
    · exact ⟨a, by simp, hxa⟩
    by_cases hxb : G.Adj x b
    · exact ⟨b, by simp, hxb⟩
    have hxv : x ≠ v := fun h => hxa (h ▸ hva)
    have hxan : x ≠ a := fun h => hxb (h ▸ hab)
    have hxbn : x ≠ b := fun h => hxa (h ▸ hab.symm)
    have he := uniqueNonedge (complement_edge_away G hxv hva.ne' hxan hxa)
      (complement_edge_away G hxv hbv hxbn hxb)
    rcases Sym2.eq_iff.mp he with ⟨_, hEq⟩ | ⟨hEq, _⟩
    · exact (hab.ne hEq).elim
    · exact (hxbn hEq).elim
  · obtain ⟨t, htD, hat⟩ := hD a
    have htv : t = v := by
      by_contra hn
      exact hPair ⟨t, htD, hn, hat⟩
    have hvD : v ∈ D := htv ▸ htD
    refine ⟨a, v, hva.ne', Finset.insert_subset haD (Finset.singleton_subset_iff.mpr hvD), ?_⟩
    intro x
    by_cases hxa : G.Adj x a
    · exact ⟨a, by simp, hxa⟩
    by_cases hxv : G.Adj x v
    · exact ⟨v, by simp, hxv⟩
    obtain ⟨b, hbD, hxb⟩ := hD x
    have hxvn : x ≠ v := fun h => hxa (h ▸ hva)
    have hxan : x ≠ a := fun h => hxv (h ▸ hva.symm)
    have hbv : b ≠ v := fun h => hxv (h ▸ hxb)
    have hba : b ≠ a := fun h => hxa (h ▸ hxb)
    have hab : ¬ G.Adj a b := fun h => hPair ⟨b, hbD, hbv, h⟩
    have he := uniqueNonedge (complement_edge_away G hva.ne' hxvn hxan.symm
        (fun h => hxa h.symm))
      (complement_edge_away G hva.ne' hbv hba.symm hab)
    rcases Sym2.eq_iff.mp he with ⟨_, hEq⟩ | ⟨hEq, _⟩
    · exact (hxb.ne hEq).elim
    · exact (hba hEq.symm).elim

private theorem minimal_total_dominating_card_eq_two (v : V)
    (hAway : (Gᶜ.edgeFinset \ Gᶜ.incidenceFinset v).card ≤ 1)
    (D : Finset V) (hD : G.IsMinimalTotalDominatingSet D) : D.card = 2 := by
  obtain ⟨a, b, hab, hSub, hTD⟩ := contains_total_dominating_pair G v hAway D hD.1
  have hEq : {a, b} = D := by
    by_contra hn
    exact hD.2 {a, b} (Finset.ssubset_iff_subset_ne.mpr ⟨hSub, hn⟩) hTD
  rw [← hEq]
  simp [hab]

/-- Every minimal total dominating set has cardinality two under the
numerical hypothesis of Conjecture 318. -/
theorem minimal_total_dominating_card_eq_two_of_edge_bound
    (v : V) (h : Gᶜ.edgeFinset.card ≤ G.distEven v)
    (D : Finset V) (hD : G.IsMinimalTotalDominatingSet D) :
    D.card = 2 := by
  apply minimal_total_dominating_card_eq_two G v _ D hD
  rw [Finset.card_sdiff_of_subset (Gᶜ.incidenceFinset_subset v), card_incidenceFinset_eq_degree]
  have hBound := distEven_le_complement_degree_add_one G v
  omega

/-- Written on the Wall II Conjecture 318 with its original complement and
even-distance invariants. -/
theorem conjecture318 [Nontrivial V] (_hConn : G.Connected)
    (h : let E := Finset.univ.image (G.distEven ·)
         Gᶜ.edgeFinset.card ≤ E.max' (Finset.univ_nonempty.image _)) :
    G.IsWellTotallyDominated := by
  let E := Finset.univ.image (G.distEven ·)
  have hNonempty : E.Nonempty := Finset.univ_nonempty.image _
  have hm : E.max' hNonempty ∈ Finset.univ.image (G.distEven ·) :=
    Finset.max'_mem E hNonempty
  obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hm
  have hBound : Gᶜ.edgeFinset.card ≤ G.distEven v := by
    rw [hv]
    exact h
  intro S T hS hT
  rw [minimal_total_dominating_card_eq_two_of_edge_bound G v hBound S hS,
    minimal_total_dominating_card_eq_two_of_edge_bound G v hBound T hT]

#print axioms conjecture318

end Graffiti318
