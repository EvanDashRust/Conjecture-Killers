import Basic

/-! Written on the Wall II, 416, with a stronger inequality. -/

namespace GraffitiBatch

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def difference (I : Finset V) : ℤ := (I.card : ℤ) - (openNeighbors G I).card

def Critical (I : Finset V) : Prop :=
  Independent G I ∧ ∀ J, Independent G J → difference G J ≤ difference G I

def MaximumCritical (I : Finset V) : Prop :=
  Critical G I ∧ ∀ J, Critical G J → J.card ≤ I.card

noncomputable def criticalUnion : Finset V := by
  classical
  exact univ.filter fun v => ∃ I, MaximumCritical G I ∧ v ∈ I

def isolates (S : Finset V) : Finset V :=
  S.filter fun v => Disjoint (G.neighborFinset v) S

private theorem exists_maximum_critical : ∃ I, MaximumCritical G I := by
  classical
  let sets : Finset (Finset V) := (univ : Finset V).powerset
  have h_empty : Independent G ∅ := by simp [Independent]
  let inds := sets.filter (Independent G)
  obtain ⟨I, hI, hmax⟩ := exists_max_image inds (difference G) ⟨∅, by simp [inds, sets, h_empty]⟩
  have hcrit : Critical G I := ⟨(mem_filter.mp hI).2, fun J hJ =>
    hmax J (mem_filter.mpr ⟨by simp [sets], hJ⟩)⟩
  let crits := sets.filter (Critical G)
  obtain ⟨J, hJ, hcard⟩ := exists_max_image crits Finset.card
    ⟨I, mem_filter.mpr ⟨by simp [sets], hcrit⟩⟩
  exact ⟨J, (mem_filter.mp hJ).2, fun I hI => hcard I (mem_filter.mpr ⟨by simp [sets], hI⟩)⟩

omit [Fintype V] [DecidableRel G.Adj] in
private theorem pendant_neighbor_universal (hc : G.Connected)
    (hdiam : ∀ v w, G.dist v w ≤ 2) {p u : V}
    (hpu : G.Adj p u) (hu : ∀ w, G.Adj p w → w = u) :
    ∀ v ≠ u, G.Adj u v := by
  intro v hv
  by_cases hvp : v = p
  · subst v
    exact hpu.symm
  have hno : ¬ G.Adj p v := fun h => hv (hu v h)
  have h0 : G.dist p v ≠ 0 := fun h => hvp ((hc.dist_eq_zero_iff).mp h).symm
  have h1 : G.dist p v ≠ 1 := fun h => hno (G.dist_eq_one_iff_adj.mp h)
  obtain ⟨w, hvw, hw⟩ := distance_predecessor G hc p v hvp
  have hpv := hdiam p v
  have hpw : G.Adj p w := G.dist_eq_one_iff_adj.mp (by omega)
  rw [hu w hpw] at hvw
  exact hvw.symm

private theorem universal_pendant_neighbor (hn : 2 < Fintype.card V)
    {u p : V} (hp : p ∈ pendants G) (hU : ∀ v ≠ u, G.Adj u v) :
    G.Adj p u ∧ ∀ w, G.Adj p w → w = u := by
  have hne : p ≠ u := by
    intro h
    subst p
    have hsub : univ \ ({u} : Finset V) ⊆ G.neighborFinset u := by
      intro v hv
      exact (G.mem_neighborFinset _ _).mpr (hU v (by simpa using (mem_sdiff.mp hv).2))
    have hc := card_le_card hsub
    have hcard : (univ \ ({u} : Finset V)).card = Fintype.card V - 1 := by rw [card_sdiff_of_subset (subset_univ _), card_univ, card_singleton]
    have hd : G.degree u = 1 := (mem_filter.mp hp).2
    rw [hcard, card_neighborFinset_eq_degree, hd] at hc
    omega
  have h := (hU p hne).symm
  obtain ⟨w, _, hw⟩ := pendant_unique G hp
  exact ⟨h, fun v hv => (hw v hv).trans (hw u h).symm⟩

/-- Written on the Wall II, 416. In fact the subtraction by two is unnecessary. -/
theorem conjecture416 (hn : 2 < Fintype.card V) (hc : G.Connected)
    (hdiam : ∀ v w, G.dist v w ≤ 2) :
    (isolates G (openNeighbors G (supports G))).card ≤ (criticalUnion G).card := by
  classical
  by_cases hP : (pendants G).Nonempty
  · obtain ⟨p, hp⟩ := hP
    obtain ⟨u, hpu, hu⟩ := pendant_unique G hp
    have hU := pendant_neighbor_universal G hc hdiam hpu hu
    have hS : supports G = {u} := by
      ext v
      simp only [mem_openNeighbors, mem_singleton]
      exact ⟨fun ⟨q, hq, hvq⟩ => (universal_pendant_neighbor G hn hq hU).2 v hvq.symm,
        fun h => ⟨p, hp, h ▸ hpu.symm⟩⟩
    have hX : openNeighbors G (supports G) = univ \ {u} := by
      rw [hS]
      ext v
      simp only [mem_openNeighbors, mem_singleton, mem_sdiff, mem_univ, true_and]
      exact ⟨fun ⟨w, hw, hvw⟩ => hw ▸ hvw.ne, fun hv => ⟨u, rfl, (hU v hv).symm⟩⟩
    have hiso : isolates G (openNeighbors G (supports G)) ⊆ pendants G := by
      rw [hX]
      intro v hv
      obtain ⟨hv, hd⟩ := mem_filter.mp hv
      have hne : v ≠ u := by simpa using (mem_sdiff.mp hv).2
      refine mem_filter.mpr ⟨mem_univ _, SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr
        ⟨u, (hU v hne).symm, ?_⟩⟩
      intro w hvw
      by_contra h
      exact disjoint_left.mp hd ((G.mem_neighborFinset _ _).mpr hvw) (by simp [h])
    obtain ⟨I, hI⟩ := exists_maximum_critical G
    have hp₀ : Independent G ({p} : Finset V) := by
      intro v hv w hw
      simp only [mem_singleton] at hv hw
      simp [hv, hw]
    have hpN : openNeighbors G ({p} : Finset V) = {u} := by
      ext v
      simp only [mem_openNeighbors, mem_singleton]
      exact ⟨fun ⟨w, hw, hvw⟩ => hu v (hw ▸ hvw.symm),
        fun h => ⟨p, rfl, h ▸ hpu.symm⟩⟩
    have hpDiff : difference G {p} = 0 := by simp [difference, hpN]
    have hI₀ : 0 ≤ difference G I := by
      simpa [hpDiff] using hI.1.2 {p} hp₀
    have huI : u ∉ I := by
      intro h
      have hEq : I = {u} := by
        ext v
        simp only [mem_singleton]
        exact ⟨fun hv => by
          by_contra he
          exact hI.1.1 h hv (hU v he), fun e => e ▸ h⟩
      have hNu : openNeighbors G ({u} : Finset V) = univ \ {u} := by simpa [hS] using hX
      have hcount : (univ \ ({u} : Finset V)).card = Fintype.card V - 1 := by rw [card_sdiff_of_subset (subset_univ _), card_univ, card_singleton]
      rw [hEq, difference, hNu, hcount, card_singleton] at hI₀
      omega
    have hIn : I.Nonempty := by
      by_contra h
      have he : I = ∅ := not_nonempty_iff_eq_empty.mp h
      have hh : difference G I = 0 := by simp [he, difference, openNeighbors]
      have hpc : Critical G {p} :=
        ⟨hp₀, fun J hJ => by simpa [hpDiff, hh] using hI.1.2 J hJ⟩
      have := hI.2 {p} hpc
      simp [he] at this
    have hIncl : pendants G ⊆ I := by
      intro q hq
      by_contra hqI
      obtain ⟨v, hv⟩ := hIn
      have hvu : v ≠ u := fun e => huI (e ▸ hv)
      have hUN : u ∈ openNeighbors G I := (mem_openNeighbors G).mpr ⟨v, hv, hU v hvu⟩
      have hqU := universal_pendant_neighbor G hn hq hU
      have hJ : Independent G (insert q I) := by
        intro x hx y hy he
        rcases mem_insert.mp hx with hxq | hxI
        · subst x
          rcases mem_insert.mp hy with hyq | hyI
          · subst y
            exact G.irrefl he
          · exact huI ((hqU.2 y he) ▸ hyI)
        · rcases mem_insert.mp hy with hyq | hyI
          · subst y
            have hu_eq := hqU.2 x he.symm
            rw [hu_eq] at hxI
            exact huI hxI
          · exact hI.1.1 hxI hyI he
      have hEq : openNeighbors G (insert q I) = openNeighbors G I := by
        ext x
        simp only [mem_openNeighbors, mem_insert]
        constructor
        · rintro ⟨w, rfl | hw, he⟩
          · rw [← mem_openNeighbors]
            exact hqU.2 x he.symm ▸ hUN
          · exact ⟨w, hw, he⟩
        · exact fun ⟨w, hw, he⟩ => ⟨w, Or.inr hw, he⟩
      have hbad := hI.1.2 (insert q I) hJ
      rw [difference, card_insert_of_notMem hqI, hEq] at hbad
      unfold difference at hbad
      omega
    exact card_le_card (fun v hv => mem_filter.mpr ⟨mem_univ _, I, hI, hIncl (hiso hv)⟩)
  · change (isolates G (openNeighbors G (openNeighbors G (pendants G)))).card ≤ _
    rw [not_nonempty_iff_eq_empty.mp hP]
    simp [openNeighbors, isolates]

#print axioms conjecture416

end GraffitiBatch
