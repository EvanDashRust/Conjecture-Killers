import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Eccentricity
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.WellTotallyDominated

/-! Written on the Wall II, Conjecture 321. -/

namespace Graffiti321

open SimpleGraph

private def rowSum {V : Type*} [Fintype V] (d : V → V → ℕ) (v : V) : ℕ :=
  ∑ w, d v w

private def maxRowSum {V : Type*} [Fintype V] (d : V → V → ℕ) : ℕ :=
  Finset.univ.sup (rowSum d)

private def eccentricitySum {V : Type*} [Fintype V] (d : V → V → ℕ) : ℕ :=
  ∑ v, Finset.univ.sup (d v)

/-- The largest sum of distances from one vertex. The diagonal term is zero. -/
noncomputable def maximumTotalDistance {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  maxRowSum G.dist

private def scaledBound {V : Type*} [Fintype V] (d : V → V → ℕ) : Prop :=
  Fintype.card V * maxRowSum d ≤ 3 * eccentricitySum d

private def distanceDiameter {V : Type*} [Fintype V] (d : V → V → ℕ) : ℕ :=
  (Finset.univ : Finset (V × V)).sup fun p => d p.1 p.2

section Orders

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable (G : SimpleGraph V)

private theorem scaledBound_of_source [DecidableRel G.Adj] (hConn : G.Connected)
    (h : (1 / 3 : ℝ) * (maximumTotalDistance G : ℝ) ≤ G.averageEccentricity) :
    scaledBound G.dist := by
  have hSum : (∑ v : V, (G.eccent v).toNat) = eccentricitySum G.dist := by
    unfold eccentricitySum
    apply Finset.sum_congr rfl
    intro v _
    rw [G.eccent_eq_computable hConn]
    simp only [ENat.toNat_natCast, computable_eccent, ← G.dist_eq_computable]
  have hCard : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  rw [SimpleGraph.averageEccentricity, hSum, one_div_mul_eq_div] at h
  have h' := (le_div_iff₀ hCard).mp h
  rw [div_mul_eq_mul_div] at h'
  have h'' := (div_le_iff₀ (by norm_num : (0 : ℝ) < 3)).mp h'
  unfold scaledBound
  exact_mod_cast (show (Fintype.card V : ℝ) * (maximumTotalDistance G : ℝ) ≤
    3 * (eccentricitySum G.dist : ℝ) by simpa [mul_comm] using h'')

omit [DecidableEq V] [Nontrivial V] in
private theorem dist_le_diameter (v w : V) : G.dist v w ≤ distanceDiameter G.dist :=
  Finset.le_sup (f := fun p : V × V => G.dist p.1 p.2) (Finset.mem_univ (v, w))

omit [DecidableEq V] in
private theorem metric_bounds (hConn : G.Connected) :
    Fintype.card V * distanceDiameter G.dist ≤ 2 * maxRowSum G.dist ∧
    eccentricitySum G.dist ≤ Fintype.card V * distanceDiameter G.dist ∧
    0 < distanceDiameter G.dist := by
  let diameter := distanceDiameter G.dist
  obtain ⟨⟨a, b⟩, _, hab⟩ := Finset.exists_mem_eq_sup
    (Finset.univ : Finset (V × V)) Finset.univ_nonempty (fun p => G.dist p.1 p.2)
  change diameter = G.dist a b at hab
  obtain ⟨z, hz⟩ := exists_ne a
  have hDPos : 0 < diameter :=
    (hConn.preconnected z a).pos_dist_of_ne hz |>.trans_le (dist_le_diameter G z a)
  have hEcc : eccentricitySum G.dist ≤ Fintype.card V * diameter := by
    calc
      eccentricitySum G.dist ≤ ∑ _v : V, diameter :=
        Finset.sum_le_sum fun v _ => Finset.sup_le fun w _ => dist_le_diameter G v w
      _ = _ := by simp
  have hTotals : Fintype.card V * diameter ≤ 2 * maxRowSum G.dist := by
    calc
      Fintype.card V * diameter = ∑ _v : V, diameter := by simp
      _ ≤ ∑ v : V, (G.dist a v + G.dist b v) := by
        apply Finset.sum_le_sum
        intro v _
        rw [hab, G.dist_comm (u := b) (v := v)]
        exact hConn.dist_triangle
      _ = rowSum G.dist a + rowSum G.dist b := Finset.sum_add_distrib
      _ ≤ 2 * maxRowSum G.dist := by
        rw [two_mul]
        exact Nat.add_le_add (Finset.le_sup (Finset.mem_univ a))
          (Finset.le_sup (Finset.mem_univ b))
  exact ⟨hTotals, hEcc, hDPos⟩

omit [DecidableEq V] in
/-- For diametral vertices `a,b`, the triangle inequality gives
`n * diameter ≤ T(a) + T(b)`. This bounds the order by six. -/
private theorem card_le_six (hConn : G.Connected) (h : scaledBound G.dist) :
    Fintype.card V ≤ 6 := by
  let diameter := distanceDiameter G.dist
  obtain ⟨hTotals, hEcc, hDPos⟩ := metric_bounds G hConn
  have hCompare : (Fintype.card V * Fintype.card V) * diameter ≤
      (6 * Fintype.card V) * diameter := by
    calc
      _ = Fintype.card V * (Fintype.card V * diameter) := by ring
      _ ≤ Fintype.card V * (2 * maxRowSum G.dist) :=
        Nat.mul_le_mul_left (Fintype.card V) hTotals
      _ = 2 * (Fintype.card V * maxRowSum G.dist) := by ring
      _ ≤ 2 * (3 * eccentricitySum G.dist) := Nat.mul_le_mul_left 2 h
      _ ≤ 2 * (3 * (Fintype.card V * diameter)) :=
        Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left 3 hEcc)
      _ = _ := by ring
  have hCancel := Nat.le_of_mul_le_mul_right hCompare hDPos
  exact Nat.le_of_mul_le_mul_right hCancel Fintype.card_pos

end Orders

private def hasDistantVertex {V : Type*} (G : SimpleGraph V) (v : V) : Prop :=
  ∃ w, w ≠ v ∧ ¬ G.Adj v w ∧ ∀ x, ¬ (G.Adj v x ∧ G.Adj x w)

private def sixPrune {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  (∀ v, (Finset.univ.filter fun w => w ≠ v ∧ ¬ G.Adj v w).card ≤ 1) ∨
    (∀ v, hasDistantVertex G v)

private theorem sixPrune_of_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hConn : G.Connected) (hn : Fintype.card V = 6)
    (h : scaledBound G.dist) : sixPrune G := by
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨hTotals, hEcc, _⟩ := metric_bounds G hConn
  unfold scaledBound at h
  rw [hn] at h hTotals hEcc
  by_cases hSmall : distanceDiameter G.dist ≤ 2
  · left
    intro v
    apply Finset.card_le_one_iff.mpr
    intro a b ha hb
    by_contra hab
    have hva := (Finset.mem_filter.mp ha).2
    have hvb := (Finset.mem_filter.mp hb).2
    have haDist : 2 ≤ G.dist v a := by
      have hpos := (hConn.preconnected v a).pos_dist_of_ne hva.1.symm
      have hne : G.dist v a ≠ 1 := fun he => hva.2 (G.dist_eq_one_iff_adj.mp he)
      omega
    have hbDist : 2 ≤ G.dist v b := by
      have hpos := (hConn.preconnected v b).pos_dist_of_ne hvb.1.symm
      have hne : G.dist v b ≠ 1 := fun he => hvb.2 (G.dist_eq_one_iff_adj.mp he)
      omega
    let rest := ((Finset.univ.erase v).erase a).erase b
    have haMem : a ∈ (Finset.univ : Finset V).erase v := by simp [hva.1]
    have hbMem : b ∈ ((Finset.univ : Finset V).erase v).erase a := by
      simp [hvb.1, Ne.symm hab]
    have hRestCard : rest.card = 3 := by
      simp only [rest, Finset.card_erase_of_mem hbMem, Finset.card_erase_of_mem haMem,
        Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, hn]
    have hRest : 3 ≤ ∑ w ∈ rest, G.dist v w := by
      rw [← hRestCard]
      calc
        rest.card = ∑ _w ∈ rest, 1 := by simp
        _ ≤ _ := Finset.sum_le_sum fun w hw =>
          (hConn.preconnected v w).pos_dist_of_ne
            (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hw))).symm
    have hRow : (∑ w ∈ rest, G.dist v w) + G.dist v b + G.dist v a + G.dist v v =
        rowSum G.dist v := by
      unfold rowSum rest
      rw [Finset.sum_erase_add _ _ hbMem, Finset.sum_erase_add _ _ haMem,
        Finset.sum_erase_add _ _ (Finset.mem_univ v)]
    have hMax : rowSum G.dist v ≤ maxRowSum G.dist := Finset.le_sup (Finset.mem_univ v)
    omega
  · right
    intro v
    have hEvery : ∀ w : V, Finset.univ.sup (G.dist w) ≤ distanceDiameter G.dist :=
      fun w => Finset.sup_le fun x _ => dist_le_diameter G w x
    have hv : Finset.univ.sup (G.dist v) = distanceDiameter G.dist := by
      apply le_antisymm (hEvery v)
      by_contra! hlt
      have hSum := Finset.sum_lt_sum
        (fun w (_ : w ∈ Finset.univ) => hEvery w) ⟨v, Finset.mem_univ _, hlt⟩
      have hSum' : eccentricitySum G.dist < 6 * distanceDiameter G.dist := by
        have hConst : (∑ _w : V, distanceDiameter G.dist) = 6 * distanceDiameter G.dist := by
          simp [hn]
        rwa [hConst] at hSum
      omega
    obtain ⟨w, _, hw⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty (G.dist v)
    have hFar : 2 < G.dist v w := by
      rw [← hw, hv]
      omega
    refine ⟨w, ?_, ?_, ?_⟩
    · rintro rfl
      simp at hFar
    · intro hadj
      have := G.dist_eq_one_iff_adj.mpr hadj
      omega
    · intro x hx
      have hWalk : G.dist v w ≤ 2 :=
        G.dist_le (.cons hx.1 (.cons hx.2 .nil))
      omega

section Census

private abbrev UpperEdge (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

private def upperAdj {n : ℕ} (edges : Finset (UpperEdge n)) (a b : Fin n) : Prop :=
  if h : a < b then ⟨(a, b), h⟩ ∈ edges else False

private instance {n : ℕ} (edges : Finset (UpperEdge n)) (a b : Fin n) :
    Decidable (upperAdj edges a b) := by
  unfold upperAdj
  infer_instance

private def graphOfEdges {n : ℕ} (edges : Finset (UpperEdge n)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (upperAdj edges)

private instance graphAdjDecidable {n : ℕ} (edges : Finset (UpperEdge n)) :
    DecidableRel (graphOfEdges edges).Adj := fun a b => by
  change Decidable (a ≠ b ∧ (upperAdj edges a b ∨ upperAdj edges b a))
  infer_instance

private theorem graphOfEdges_complete {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ∃ edges, graphOfEdges edges = G := by
  let edges : Finset (UpperEdge n) := Finset.univ.filter fun p => G.Adj p.val.1 p.val.2
  refine ⟨edges, ?_⟩
  ext a b
  simp only [graphOfEdges, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, hab | hba⟩
    · unfold upperAdj at hab
      split at hab
      · exact (Finset.mem_filter.mp hab).2
      · contradiction
    · unfold upperAdj at hba
      split at hba
      · exact ((Finset.mem_filter.mp hba).2 : G.Adj b a).symm
      · contradiction
  · intro hab
    refine ⟨hab.ne, ?_⟩
    rcases lt_or_gt_of_ne hab.ne with h | h
    · left
      simpa [upperAdj, h, edges] using hab
    · right
      simpa [upperAdj, h, edges] using hab.symm

private instance {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : Finset (Fin n)) :
    Decidable (G.IsTotalDominatingSet D) := by
  unfold IsTotalDominatingSet
  infer_instance

private def isMinimalByDeletion {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D : Finset (Fin n)) : Prop :=
  G.IsTotalDominatingSet D ∧ ∀ v ∈ D, ¬ G.IsTotalDominatingSet (D.erase v)

private instance {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : Finset (Fin n)) :
    Decidable (isMinimalByDeletion G D) := by
  unfold isMinimalByDeletion
  infer_instance

private theorem isMinimalByDeletion_iff {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (D : Finset (Fin n)) :
    isMinimalByDeletion G D ↔ G.IsMinimalTotalDominatingSet D := by
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · intro h T hSub hTD
    obtain ⟨v, hvD, hvT⟩ := Finset.exists_of_ssubset hSub
    apply h v hvD
    intro w
    obtain ⟨u, hu, hadj⟩ := hTD w
    exact ⟨u, Finset.mem_erase.mpr ⟨fun heq => hvT (heq ▸ hu), hSub.subset hu⟩, hadj⟩
  · intro h v hv
    exact h _ (Finset.erase_ssubset hv)

private def minimalCards {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Finset ℕ :=
  (Finset.univ.filter (isMinimalByDeletion G)).image Finset.card

private def bfsLayers {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ℕ → Finset (Fin n) → List (Finset (Fin n))
  | 0, _ => []
  | fuel + 1, reached => reached :: bfsLayers G fuel (G.bfsStep reached)

private def firstLayer {n : ℕ} (w : Fin n) : ℕ → List (Finset (Fin n)) → ℕ
  | _, [] => 0
  | depth, reached :: rest =>
    if w ∈ reached then depth else firstLayer w (depth + 1) rest

private theorem firstLayer_eq_bfs {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Fin n) (fuel depth : ℕ) (reached : Finset (Fin n)) :
    firstLayer w depth (bfsLayers G fuel reached) = G.bfs_dist_aux w fuel depth reached := by
  induction fuel generalizing depth reached with
  | zero => rfl
  | succ fuel ih => simp only [bfsLayers, firstLayer, bfs_dist_aux, ih]

/-- Compute all the distances in a row from the same breadth-first search. -/
private def distanceRow {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v : Fin n) : Fin n → ℕ :=
  let layers := bfsLayers G (Fintype.card (Fin n)) (G.bfsStep {v})
  fun w => if v = w then 0 else firstLayer w 1 layers

private theorem distanceRow_eq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    distanceRow G = G.computable_dist := by
  funext v w
  simp only [distanceRow, computable_dist, firstLayer_eq_bfs]

private def memoizedDistance {n : ℕ} (d : Fin n → Fin n → ℕ) : Fin n → Fin n → ℕ :=
  let distances := List.ofFn (fun v => List.ofFn (d v))
  fun v w => (distances[v.val]?.getD [])[w.val]?.getD 0

private theorem memoizedDistance_eq {n : ℕ} (d : Fin n → Fin n → ℕ) :
    memoizedDistance d = d := by
  funext v w
  simp [memoizedDistance]

private def censusCheck {n : ℕ} (edges : Finset (UpperEdge n)) : Bool :=
  let G := graphOfEdges edges
  let d := memoizedDistance (distanceRow G)
  if ∀ v w, v ≠ w → d v w ≠ 0 then
    if Fintype.card (Fin n) * maxRowSum d ≤ 3 * eccentricitySum d then
      decide ((minimalCards G).card ≤ 1)
    else true
  else true

private instance hasDistantVertexDecidable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v : Fin n) : Decidable (hasDistantVertex G v) := by
  unfold hasDistantVertex
  infer_instance

private instance sixPruneDecidable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Decidable (sixPrune G) := by
  unfold sixPrune
  infer_instance

private def screenedCheck {n : ℕ} (edges : Finset (UpperEdge n)) : Bool :=
  if ∀ v, ∃ w, (graphOfEdges edges).Adj v w then
    if n = 6 then
      if sixPrune (graphOfEdges edges) then censusCheck edges else true
    else censusCheck edges
  else true

private def allUpperEdges (n : ℕ) : List (UpperEdge n) :=
  (List.finRange n).flatMap fun a =>
    (List.finRange n).filterMap fun b => if h : a < b then some ⟨(a, b), h⟩ else none

private theorem mem_allUpperEdges {n : ℕ} (e : UpperEdge n) : e ∈ allUpperEdges n := by
  obtain ⟨⟨a, b⟩, hab⟩ := e
  exact List.mem_flatMap.mpr ⟨a, List.mem_finRange a, List.mem_filterMap.mpr
    ⟨b, List.mem_finRange b, by simp [hab]⟩⟩

/-- Visit each completion of the selected edges by deciding the remaining
edges one at a time. -/
private def checkCompletions {n : ℕ} : List (UpperEdge n) → Finset (UpperEdge n) → Bool
  | [], chosen => screenedCheck chosen
  | e :: rest, chosen =>
    checkCompletions rest chosen && checkCompletions rest (insert e chosen)

private theorem checkCompletions_sound {n : ℕ} (remaining : List (UpperEdge n))
    (chosen edges : Finset (UpperEdge n)) (hChosen : chosen ⊆ edges)
    (hRemaining : ∀ e ∈ edges, e ∈ chosen ∨ e ∈ remaining)
    (hCheck : checkCompletions remaining chosen = true) : screenedCheck edges = true := by
  induction remaining generalizing chosen with
  | nil =>
    have hEq : edges = chosen := Finset.Subset.antisymm
      (fun e he => (hRemaining e he).resolve_right List.not_mem_nil) hChosen
    simpa only [hEq, checkCompletions] using hCheck
  | cons e rest ih =>
    have hBoth := Bool.and_eq_true_iff.mp hCheck
    by_cases he : e ∈ edges
    · refine ih (insert e chosen) (Finset.insert_subset he hChosen) ?_ hBoth.2
      intro f hf
      rcases hRemaining f hf with h | h
      · exact Or.inl (Finset.mem_insert_of_mem h)
      · rcases List.mem_cons.mp h with rfl | hr
        · exact Or.inl (Finset.mem_insert_self _ _)
        · exact Or.inr hr
    · refine ih chosen hChosen ?_ hBoth.1
      intro f hf
      rcases hRemaining f hf with h | h
      · exact Or.inl h
      · rcases List.mem_cons.mp h with rfl | hr
        · exact (he hf).elim
        · exact Or.inr hr

set_option maxHeartbeats 0 in
private theorem census (n : ℕ) (h₂ : 2 ≤ n) (h₆ : n ≤ 6) :
    checkCompletions (allUpperEdges n) ∅ = true := by
  interval_cases n
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · native_decide
  · native_decide

private theorem small_graph {n : ℕ} (h₂ : 2 ≤ n) (h₆ : n ≤ 6)
    (G : SimpleGraph (Fin n)) [decAdj : DecidableRel G.Adj]
    (hConn : G.Connected) (h : scaledBound G.dist) : G.IsWellTotallyDominated := by
  obtain ⟨edges, rfl⟩ := graphOfEdges_complete G
  have hDecision : decAdj = graphAdjDecidable edges := Subsingleton.elim _ _
  subst decAdj
  have hDist : (graphOfEdges edges).computable_dist = (graphOfEdges edges).dist :=
    funext fun v => funext fun w => ((graphOfEdges edges).dist_eq_computable v w).symm
  have hPositive : ∀ v w, v ≠ w → (graphOfEdges edges).computable_dist v w ≠ 0 := by
    intro v w hvw
    rw [hDist]
    exact (graphOfEdges edges).dist_ne_zero_iff_ne_and_reachable.mpr
      ⟨hvw, hConn.preconnected v w⟩
  have hScaled : scaledBound (graphOfEdges edges).computable_dist := by rwa [hDist]
  unfold scaledBound at hScaled
  have hCards : (minimalCards (graphOfEdges edges)).card ≤ 1 := by
    have hScreened := checkCompletions_sound (allUpperEdges n) ∅ edges (Finset.empty_subset _)
      (fun e _ => Or.inr (mem_allUpperEdges e)) (census n h₂ h₆)
    have hCheck : censusCheck edges = true := by
      have : Nontrivial (Fin n) :=
        Fintype.one_lt_card_iff_nontrivial.mp (by simpa using Nat.lt_of_succ_le h₂)
      have hNeighbors := hConn.preconnected.exists_adj_of_nontrivial
      by_cases hn : n = 6
      · have hScreen := sixPrune_of_bound (graphOfEdges edges) hConn (by simpa using hn) h
        simpa only [screenedCheck, if_pos hNeighbors, if_pos hn, if_pos hScreen] using hScreened
      · simpa only [screenedCheck, if_pos hNeighbors, if_neg hn] using hScreened
    simp only [censusCheck, memoizedDistance_eq, distanceRow_eq] at hCheck
    split at hCheck
    · exact of_decide_eq_true hCheck
    · rename_i hn
      exact (hn hPositive).elim
  intro S T hS hT
  exact Finset.card_le_one_iff.mp hCards
    (Finset.mem_image.mpr ⟨S, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (isMinimalByDeletion_iff _ S).mpr hS⟩, rfl⟩)
    (Finset.mem_image.mpr ⟨T, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (isMinimalByDeletion_iff _ T).mpr hT⟩, rfl⟩)

end Census

section Relabeling

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
variable {G : SimpleGraph V} {H : SimpleGraph W}

omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] in
private theorem iso_dist (e : G ≃g H) (hConn : G.Connected) (v w : V) :
    H.dist (e v) (e w) = G.dist v w := by
  apply le_antisymm
  · obtain ⟨p, hp⟩ := hConn.exists_walk_length_eq_dist v w
    simpa [hp] using H.dist_le (p.map e.toHom)
  · obtain ⟨p, hp⟩ := (e.connected_iff.mp hConn).exists_walk_length_eq_dist (e v) (e w)
    simpa [hp] using G.dist_le (p.map e.symm.toHom)

omit [DecidableEq V] [DecidableEq W] in
private theorem sup_relabel (e : V ≃ W) (f : V → ℕ) (g : W → ℕ)
    (h : ∀ x, g (e x) = f x) : Finset.univ.sup g = Finset.univ.sup f := by
  apply le_antisymm
  · apply Finset.sup_le
    intro w _
    obtain ⟨v, rfl⟩ := e.surjective w
    rw [h]
    exact Finset.le_sup (Finset.mem_univ v)
  · apply Finset.sup_le
    intro v _
    rw [← h]
    exact Finset.le_sup (Finset.mem_univ (e v))

omit [DecidableEq V] [DecidableEq W] in
private theorem scaledBound_relabel (e : G ≃g H) (hConn : G.Connected)
    (h : scaledBound G.dist) : scaledBound H.dist := by
  have hMax : maxRowSum H.dist = maxRowSum G.dist := by
    apply sup_relabel e.toEquiv
    intro v
    exact (Fintype.sum_equiv e.toEquiv (G.dist v) (H.dist (e v))
      (fun w => (iso_dist e hConn v w).symm)).symm
  have hEcc : eccentricitySum H.dist = eccentricitySum G.dist := by
    symm
    apply Fintype.sum_equiv e.toEquiv
    intro v
    exact (sup_relabel e.toEquiv (G.dist v) (H.dist (e v)) (iso_dist e hConn v)).symm
  unfold scaledBound at *
  rwa [hMax, hEcc, ← Fintype.card_congr e.toEquiv]

variable [DecidableRel G.Adj] [DecidableRel H.Adj]

omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] in
private theorem totalDom_relabel (e : G ≃g H) (s : Finset V) :
    H.IsTotalDominatingSet (s.map e.toEquiv.toEmbedding) ↔ G.IsTotalDominatingSet s := by
  constructor
  · intro h v
    obtain ⟨w, hw, hadj⟩ := h (e v)
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hw
    exact ⟨x, hx, e.map_adj_iff.mp hadj⟩
  · intro h w
    obtain ⟨v, rfl⟩ := e.toEquiv.surjective w
    obtain ⟨u, hu, hadj⟩ := h v
    exact ⟨e u, Finset.mem_map.mpr ⟨u, hu, rfl⟩, e.map_adj_iff.mpr hadj⟩

omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] in
private theorem minimalTotalDom_relabel (e : G ≃g H) (s : Finset V)
    (hs : G.IsMinimalTotalDominatingSet s) :
    H.IsMinimalTotalDominatingSet (s.map e.toEquiv.toEmbedding) := by
  refine ⟨(totalDom_relabel e s).mpr hs.1, ?_⟩
  intro t ht htd
  let tPre := t.map e.symm.toEquiv.toEmbedding
  have hMap : tPre.map e.toEquiv.toEmbedding = t := by
    have hEmbedding : e.symm.toEquiv.toEmbedding.trans e.toEquiv.toEmbedding =
        Function.Embedding.refl W := by
      ext x
      exact e.apply_symm_apply x
    simp [tPre, Finset.map_map, hEmbedding]
  have hSub : tPre ⊂ s := Finset.map_ssubset_map.mp (by rwa [hMap])
  apply hs.2 tPre hSub
  apply (totalDom_relabel e tPre).mp
  rwa [hMap]

end Relabeling

/-- The original average-eccentricity hypothesis implies well-total-domination
for every finite, connected simple graph on at least two vertices. -/
theorem conjecture321 {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hConn : G.Connected)
    (h : (1 / 3 : ℝ) * (maximumTotalDistance G : ℝ) ≤ G.averageEccentricity) :
    G.IsWellTotallyDominated := by
  have hScaled := scaledBound_of_source G hConn h
  have h₆ := card_le_six G hConn hScaled
  have h₂ := Fintype.one_lt_card (α := V)
  let e := Fintype.equivFin V
  let H : SimpleGraph (Fin (Fintype.card V)) := G.comap e.symm
  let : DecidableRel (G.comap e.symm).Adj := fun v w =>
    inferInstanceAs (Decidable (G.Adj (e.symm v) (e.symm w)))
  let iso : G ≃g H := ⟨e, by
    intro u v
    change G.Adj (e.symm (e u)) (e.symm (e v)) ↔ G.Adj u v
    simp⟩
  have hSmall := small_graph h₂ h₆ H (iso.connected_iff.mp hConn)
    (scaledBound_relabel iso hConn hScaled)
  intro S T hS hT
  simpa using hSmall (S.map e.toEmbedding) (T.map e.toEmbedding)
    (minimalTotalDom_relabel iso S hS) (minimalTotalDom_relabel iso T hT)

#print axioms conjecture321

end Graffiti321
