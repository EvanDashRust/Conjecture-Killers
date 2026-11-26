import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.SpanningTree
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.VertexDistance
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-! Written on the Wall II, Conjecture 169. -/

namespace Graffiti169

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Keep exactly the edges crossing the parity of distance from the root. -/
private def parityGraph (r : V) : SimpleGraph V where
  Adj u w := G.Adj u w ∧ G.dist r u % 2 ≠ G.dist r w % 2
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.2 rfl⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem distance_predecessor (hConn : G.Connected) (r x : V) (hx : x ≠ r) :
    ∃ y, G.Adj x y ∧ G.dist r y + 1 = G.dist r x := by
  obtain ⟨p, hp⟩ := hConn.exists_walk_length_eq_dist x r
  have hpNonempty : ¬ p.Nil := fun h => hx (p.eq_of_length_eq_zero h.length_eq_zero)
  have hAdj := p.adj_snd hpNonempty
  have hTail := p.length_tail_add_one hpNonempty
  have hLe := G.dist_le p.tail
  have hTriangle : G.dist x r ≤ 1 + G.dist p.snd r := by
    simpa only [G.dist_eq_one_iff_adj.mpr hAdj] using
      (hConn.dist_triangle (u := x) (v := p.snd) (w := r))
  refine ⟨p.snd, hAdj, ?_⟩
  rw [G.dist_comm (u := r) (v := p.snd), G.dist_comm (u := r) (v := x)]
  omega

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem parityGraph_connected (hConn : G.Connected) (r : V) :
    (parityGraph G r).Connected := by
  have : Nonempty V := ⟨r⟩
  have hReach (x : V) : (parityGraph G r).Reachable x r := by
    generalize hn : G.dist r x = n
    induction n using Nat.strong_induction_on generalizing x with
    | h n ih =>
      by_cases hx : x = r
      · subst x
        exact Reachable.rfl
      obtain ⟨y, hy, hDist⟩ := distance_predecessor G hConn r x hx
      have hEdge : (parityGraph G r).Adj x y := ⟨hy, by omega⟩
      exact hEdge.reachable.trans (ih (G.dist r y) (by omega) y rfl)
  exact ⟨fun x y => (hReach x).trans (hReach y).symm⟩

private abbrev leaves (T : SimpleGraph V) [DecidableRel T.Adj] :=
  (Finset.univ : Finset V).filter (fun x => T.degree x = 1)

omit [DecidableEq V] [DecidableRel G.Adj] in
private theorem part_bound [Nontrivial V] (T : SimpleGraph V) [DecidableRel T.Adj]
    (hTree : T.IsTree) (s t : Finset V) (hBip : T.IsBipartiteWith s t) :
    2 * s.card + 1 ≤ Fintype.card V + (leaves T).card := by
  let ones := s.filter fun x => T.degree x = 1
  let others := s.filter fun x => T.degree x ≠ 1
  have hDegree (v : V) : 1 ≤ T.degree v := by
    obtain ⟨w, hw⟩ := hTree.connected.preconnected.exists_adj_of_nontrivial v
    exact hw.degree_pos_left
  have hOne : (∑ v ∈ ones, T.degree v) = ones.card := by
    calc
      _ = ∑ _v ∈ ones, (1 : ℕ) := Finset.sum_congr rfl fun v hv => (Finset.mem_filter.mp hv).2
      _ = _ := by simp
  have hOthers : 2 * others.card ≤ ∑ v ∈ others, T.degree v := by
    calc
      _ = ∑ _v ∈ others, (2 : ℕ) := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun v hv => by
        have hne := (Finset.mem_filter.mp hv).2
        have hpos := hDegree v
        omega
  have hCounts : ones.card + others.card = s.card :=
    Finset.card_filter_add_card_filter_not (s := s) _
  have hSum : (∑ v ∈ ones, T.degree v) + ∑ v ∈ others, T.degree v =
      ∑ v ∈ s, T.degree v := Finset.sum_filter_add_sum_filter_not _ _ _
  have hEdges := T.isBipartiteWith_sum_degrees_eq_card_edges hBip
  have hTotal := hTree.card_edgeFinset
  have hLeaves : ones.card ≤ (leaves T).card := Finset.card_le_card fun v hv =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hv).2⟩
  omega

omit [DecidableEq V] in
private theorem spanning_tree_leaves_le_Ls (T : SimpleGraph V) [DecidableRel T.Adj]
    (hSub : T ≤ G) (hTree : T.IsTree) : ((leaves T).card : ℝ) ≤ G.Ls := by
  classical
  let S := SimpleGraph.toSubgraph T hSub
  have hSpan : S.IsSpanning := SimpleGraph.toSubgraph.isSpanning T hSub
  have hSTree : S.coe.IsTree := (S.spanningCoeEquivCoeOfSpanning hSpan).isTree_iff.mp hTree
  unfold SimpleGraph.Ls
  apply le_csSup
  · refine ⟨Fintype.card V, ?_⟩
    rintro _ ⟨A, _, rfl⟩
    change ((A.verts.toFinset.filter fun x => A.degree x = 1).card : ℝ) ≤ Fintype.card V
    exact_mod_cast Finset.card_le_univ _
  · refine ⟨S, ⟨hSpan, hSTree⟩, ?_⟩
    have hVerts : S.verts.toFinset = Finset.univ := by simp [hSpan.verts_eq_univ]
    simp only [hVerts, S, SimpleGraph.degree_toSubgraph]

/-- The two distance parities separately give bounds on the number of leaves. -/
theorem parity_bounds [Nontrivial V] (hConn : G.Connected) (r : V) :
    2 * (G.distEven r : ℝ) + 1 ≤ (Fintype.card V : ℝ) + G.Ls ∧
    2 * ((Fintype.card V : ℝ) - G.distEven r) + 1 ≤ (Fintype.card V : ℝ) + G.Ls := by
  classical
  obtain ⟨T, hSub, hTree⟩ := (parityGraph_connected G hConn r).exists_isTree_le
  let s := (Finset.univ : Finset V).filter (fun x => Even (G.dist r x))
  have hBip : T.IsBipartiteWith (s : Set V) (↑(sᶜ : Finset V) : Set V) := by
    refine ⟨Finset.disjoint_coe.mpr disjoint_compl_right, ?_⟩
    intro u w hAdj
    have hPar : G.dist r u % 2 ≠ G.dist r w % 2 := (hSub hAdj).2
    simp only [Finset.mem_coe, Finset.mem_compl, s, Finset.mem_filter, Finset.mem_univ,
      true_and, Nat.even_iff]
    omega
  have hEv : 2 * s.card + 1 ≤ Fintype.card V + (leaves T).card := part_bound T hTree s sᶜ hBip
  have hOd : 2 * sᶜ.card + 1 ≤ Fintype.card V + (leaves T).card := part_bound T hTree sᶜ s hBip.symm
  have hLeaves := spanning_tree_leaves_le_Ls G T (fun _ _ h => (hSub h).1) hTree
  have hL : (s.card : ℝ) = G.distEven r := rfl
  have hR : (sᶜ.card : ℝ) = (Fintype.card V : ℝ) - G.distEven r := by
    rw [Finset.card_compl, Nat.cast_sub (Finset.card_le_univ s), hL]
  have hEvR : 2 * (s.card : ℝ) + 1 ≤ (Fintype.card V : ℝ) + (leaves T).card := by exact_mod_cast hEv
  have hOdR : 2 * (sᶜ.card : ℝ) + 1 ≤ (Fintype.card V : ℝ) + (leaves T).card := by exact_mod_cast hOd
  rw [hL] at hEvR
  rw [hR] at hOdR
  exact ⟨hEvR.trans (add_le_add le_rfl hLeaves), hOdR.trans (add_le_add le_rfl hLeaves)⟩

omit [DecidableRel G.Adj] in
/-- The maximum and minimum range over all vertices, exactly as in the source. -/
noncomputable def evenDistanceCounts := Finset.univ.image (G.distEven ·)

/-- Graffiti.pc Conjecture 169 holds on every connected graph of order at least two. -/
theorem conjecture169_nontrivial [Nontrivial V] (hConn : G.Connected) :
    let E := evenDistanceCounts G
    1 + (E.max' (Finset.univ_nonempty.image _) : ℝ) -
      (E.min' (Finset.univ_nonempty.image _) : ℝ) ≤ G.Ls := by
  let E := evenDistanceCounts G
  have hNE : E.Nonempty := Finset.univ_nonempty.image _
  obtain ⟨a, _, ha⟩ := Finset.mem_image.mp (Finset.max'_mem E hNE)
  obtain ⟨b, _, hb⟩ := Finset.mem_image.mp (Finset.min'_mem E hNE)
  change 1 + (E.max' hNE : ℝ) - (E.min' hNE : ℝ) ≤ G.Ls
  rw [← ha, ← hb]
  linarith [(parity_bounds G hConn a).1, (parity_bounds G hConn b).2]

omit [DecidableEq V] in
/-- A spanning tree on a subsingleton vertex type has no degree-one vertices. -/
private theorem Ls_subsingleton [Subsingleton V] : G.Ls = 0 := by
  classical
  unfold SimpleGraph.Ls
  have h (T : Subgraph G) : (T.verts.toFinset.filter fun v => T.degree v = 1) = ∅ := by
    ext v
    simp [T.degree_eq_zero_of_subsingleton v (fun _ _ _ _ => Subsingleton.elim _ _)]
  simp only [h, Finset.card_empty, Nat.cast_zero]
  let F : Set (Subgraph G) := {T | T.IsSpanning ∧ T.coe.IsTree}
  change sSup ((fun _ => (0 : ℝ)) '' F) = 0
  by_cases hn : F.Nonempty
  · rw [hn.image_const, csSup_singleton]
  · rw [Set.not_nonempty_iff_eq_empty.mp hn, Set.image_empty, Real.sSup_empty]

/-- The inequality holds exactly when the connected graph has at least two vertices. -/
theorem conjecture169_iff_nontrivial [Nonempty V] (hConn : G.Connected) :
    (let E := evenDistanceCounts G
     1 + (E.max' (Finset.univ_nonempty.image _) : ℝ) -
       (E.min' (Finset.univ_nonempty.image _) : ℝ) ≤ G.Ls) ↔ Nontrivial V := by
  classical
  by_cases hNT : Nontrivial V
  · have := hNT
    exact ⟨fun _ => hNT, fun _ => conjecture169_nontrivial G hConn⟩
  · have : Subsingleton V := not_nontrivial_iff_subsingleton.mp hNT
    have hEven (x : V) : G.distEven x = 1 := by
      have hUniv : (Finset.univ : Finset V) = {x} := by
        ext y
        simp [Subsingleton.elim y x]
      have hKeep : (({x} : Finset V).filter fun y => Even (G.dist x y)) = {x} := by
        apply Finset.filter_eq_self.mpr
        intro y hy
        rw [Finset.mem_singleton.mp hy, G.dist_self]
        exact ⟨0, rfl⟩
      rw [SimpleGraph.distEven, hUniv, hKeep, Finset.card_singleton]
    have hE : evenDistanceCounts G = {1} := by
      unfold evenDistanceCounts
      simp_rw [hEven]
      exact Finset.image_const Finset.univ_nonempty 1
    dsimp only
    simp [hE, Ls_subsingleton, hNT]

/-- With the degree-one leaf convention, the literal formulation fails on K₁. -/
theorem conjecture169_singleton_counterexample :
    let G : SimpleGraph (Fin 1) := ⊥
    let E := evenDistanceCounts G
    G.Connected ∧ ¬ (1 + (E.max' (Finset.univ_nonempty.image _) : ℝ) -
      (E.min' (Finset.univ_nonempty.image _) : ℝ) ≤ G.Ls) := by
  dsimp only
  have hConn : (⊥ : SimpleGraph (Fin 1)).Connected := SimpleGraph.Connected.of_subsingleton
  exact ⟨hConn, fun h => (not_nontrivial_iff_subsingleton.mpr inferInstance)
    ((conjecture169_iff_nontrivial ⊥ hConn).mp h)⟩

#print axioms conjecture169_iff_nontrivial
#print axioms conjecture169_singleton_counterexample

end Graffiti169
