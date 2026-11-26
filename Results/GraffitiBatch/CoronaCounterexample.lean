import Basic
import Mathlib.Combinatorics.SimpleGraph.Matching

/-! Written on the Wall II, 393d, with the maximum incident K₄ count
interpreted literally, including ties. -/

namespace GraffitiBatch

open Finset SimpleGraph
open scoped BigOperators

namespace Corona

abbrev Vertex := Fin 21 × Bool

private def coreAdj (i j : Fin 21) : Prop :=
  let a := min i.val j.val
  let b := max i.val j.val
  i ≠ j ∧
    if a < 4 then b < 4 ∨ b = a + 4
    else b - a = 1 ∨ (b - a = 2 ∧ a ≠ 4 ∧ a ≠ 5) ∨
      (a = 4 ∧ 19 ≤ b) ∨ (a = 5 ∧ b = 20)

def graph : SimpleGraph Vertex where
  Adj x y := if x.2 = y.2 then x.2 = false ∧ coreAdj x.1 y.1 else x.1 = y.1
  symm := ⟨fun x y h => by
    by_cases he : x.2 = y.2
    · rw [ite_eq_left he] at h
      rw [ite_eq_left he.symm]
      refine ⟨he.symm.trans h.1, ?_⟩
      simp only [coreAdj, min_comm y.1.val x.1.val, max_comm y.1.val x.1.val]
      exact ⟨h.2.1.symm, h.2.2⟩
    · rw [ite_eq_right he] at h
      rw [ite_eq_right (Ne.symm he)]
      exact h.symm⟩
  loopless := ⟨fun x h => by simp [coreAdj] at h⟩

instance : DecidableRel graph.Adj := fun x y => by
  unfold graph coreAdj
  infer_instance

def centers : Finset Vertex := univ.filter fun x => x.2 = false

def leaves : Finset Vertex := univ.filter fun x => x.2 = true

private def step (v : Vertex) : Vertex :=
  if v.2 then (v.1, false)
  else if v.1.val ≤ 4 then (0, false)
  else (⟨v.1.val - 1, by omega⟩, false)

private def rank (v : Vertex) : ℕ := 2 * v.1.val + if v.2 then 1 else 0

private theorem step_check :
    ∀ v : Vertex, v ≠ (0, false) → graph.Adj v (step v) ∧ rank (step v) < rank v := by decide

theorem connected : graph.Connected := by
  have hreach (v : Vertex) : graph.Reachable v (0, false) := by
    generalize he : rank v = n
    induction n using Nat.strong_induction_on generalizing v with
    | ind n ih =>
      by_cases hr : v = (0, false)
      · subst v
        exact Reachable.rfl
      · obtain ⟨he', hlt⟩ := step_check v hr
        exact he'.reachable.trans (ih _ (by omega) _ rfl)
  exact ⟨fun x y => (hreach x).trans (hreach y).symm⟩

private def adjacentTo (v : Vertex) : Finset Vertex := univ.filter (graph.Adj v)

private theorem adjacentTo_eq (v : Vertex) : adjacentTo v = graph.neighborFinset v :=
  graph.neighborFinset_eq_filter.symm

private theorem degree_check (v : Vertex) : graph.degree v = if v.2 then 1 else 5 := by
  have h : ∀ w : Vertex, (adjacentTo w).card = if w.2 then 1 else 5 := by decide
  simpa only [adjacentTo_eq, card_neighborFinset_eq_degree] using h v

private theorem leaves_card : leaves.card = 21 := by decide
private theorem centers_card : centers.card = 21 := by decide
private theorem centers_compl : univ \ centers = leaves := by decide

theorem pendant_set : pendants graph = leaves := by
  ext v
  simp only [pendants, leaves, mem_filter, mem_univ, true_and, degree_check]
  cases v.2 <;> decide

theorem maximum_degree_set :
    (univ.filter fun v => graph.degree v = graph.maxDegree) = centers := by
  have hMax : graph.maxDegree = 5 := by
    apply Nat.le_antisymm
    · obtain ⟨v, hv⟩ := graph.exists_maximal_degree_vertex
      rw [hv, degree_check]
      split <;> decide
    · simpa [degree_check] using graph.degree_le_maxDegree (0, false)
  ext v
  simp only [centers, mem_filter, mem_univ, true_and, degree_check, hMax]
  cases v.2 <;> decide

theorem neighborhood_of_leaves : openNeighbors graph leaves = centers := by
  have h : ∀ v : Vertex,
      (∃ w ∈ leaves, graph.Adj v w) ↔ v ∈ centers := by decide
  ext v
  simpa only [mem_openNeighbors] using h v

theorem neighborhood_of_centers : openNeighbors graph centers = univ := by
  have h : ∀ v : Vertex, ∃ w ∈ centers, graph.Adj v w := by decide
  apply eq_univ_of_forall
  intro v
  simpa only [mem_openNeighbors] using h v

private def cliqueCheck (S : Finset Vertex) : Bool :=
  decide (∀ a ∈ S, ∀ b ∈ S, a ≠ b → graph.Adj a b)

def incidentK4Count (v : Vertex) : ℕ :=
  ((adjacentTo v).powersetCard 3 |>.filter fun S => cliqueCheck S = true).card

/-- Every K₄ through v consists of v and a 3-clique among its neighbors. -/
theorem mem_countedK4_iff (v : Vertex) (S : Finset Vertex) :
    S ∈ ((adjacentTo v).powersetCard 3 |>.filter fun T => cliqueCheck T = true) ↔
      S.card = 3 ∧ S ⊆ graph.neighborFinset v ∧ graph.IsClique (↑S : Set Vertex) := by
  simp only [mem_filter, mem_powersetCard, adjacentTo_eq, cliqueCheck,
    decide_eq_true_eq, isClique_iff, Set.Pairwise, mem_coe]
  tauto

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem incident_check : ∀ v : Vertex,
    incidentK4Count v = if v.1.val < 4 ∧ v.2 = false then 1 else 0 := by
  decide

def maximumK4Vertices : Finset Vertex :=
  univ.filter fun v => incidentK4Count v = univ.sup incidentK4Count

theorem maximumK4_count : maximumK4Vertices.card = 4 := by
  have hMax : (univ : Finset Vertex).sup incidentK4Count = 1 := by
    apply Nat.le_antisymm
    · apply Finset.sup_le
      intro v _
      rw [incident_check]
      split <;> decide
    · have h := le_sup (s := (univ : Finset Vertex)) (f := incidentK4Count)
        (mem_univ (0, false))
      simpa [incident_check] using h
  have he : maximumK4Vertices = univ.filter fun v => v.1.val < 4 ∧ v.2 = false := by
    ext v
    simp only [maximumK4Vertices, hMax, incident_check, mem_filter, mem_univ, true_and]
    split <;> simp_all
  rw [he]
  decide

theorem leaves_independent : Independent graph leaves := by
  intro v hv w hw
  have h₁ := (mem_filter.mp hv).2
  have h₂ := (mem_filter.mp hw).2
  simp [graph, h₁, h₂]

private theorem covered_centers (D : Finset Vertex) (hD : TwoDominates graph D) :
    centers ⊆ (D ∩ centers).biUnion (fun v => insert v (graph.neighborFinset v ∩ centers)) := by
  intro x hx
  by_cases hxD : x ∈ D
  · exact mem_biUnion.mpr ⟨x, mem_inter.mpr ⟨hxD, hx⟩, mem_insert_self _ _⟩
  · have hxC := (mem_filter.mp hx).2
    by_contra hn
    have hsub : graph.neighborFinset x ∩ D ⊆ ({(x.1, true)} : Finset Vertex) := by
      intro y hy
      obtain ⟨hyN, hyD⟩ := mem_inter.mp hy
      have he := (graph.mem_neighborFinset _ _).mp hyN
      cases hY : y.2 with
      | false =>
        exact (hn (mem_biUnion.mpr ⟨y, mem_inter.mpr
          ⟨hyD, mem_filter.mpr ⟨mem_univ _, hY⟩⟩,
          mem_insert_of_mem (mem_inter.mpr ⟨(graph.mem_neighborFinset _ _).mpr he.symm, hx⟩)⟩)).elim
      | true =>
        have hxy : x.1 = y.1 := by simpa [graph, hxC, hY] using he
        exact mem_singleton.mpr (Prod.ext hxy.symm hY)
    have hle := card_le_card hsub
    rw [card_singleton] at hle
    have h := hD x hxD
    omega

private theorem center_ball_size (v : Vertex) (hv : v ∈ centers) :
    (insert v (graph.neighborFinset v ∩ centers)).card = 5 := by
  have h : ∀ u : Vertex, u ∈ centers →
      (insert u (adjacentTo u ∩ centers)).card = 5 := by decide
  simpa only [adjacentTo_eq] using h v hv

theorem twoDomination_lower (D : Finset Vertex) (hD : TwoDominates graph D) :
    26 ≤ D.card := by
  have hL : leaves ⊆ D := by
    intro v hv
    by_contra hn
    have h := hD v hn
    have hle := card_le_card (inter_subset_left (s₁ := graph.neighborFinset v) (s₂ := D))
    have hP : v ∈ pendants graph := pendant_set ▸ hv
    have hdeg : graph.degree v = 1 := (mem_filter.mp hP).2
    rw [card_neighborFinset_eq_degree, hdeg] at hle
    omega
  have hC : 21 ≤ 5 * (D ∩ centers).card := by
    calc
      21 = centers.card := centers_card.symm
      _ ≤ ((D ∩ centers).biUnion (fun v => insert v (graph.neighborFinset v ∩ centers))).card :=
        card_le_card (covered_centers D hD)
      _ ≤ ∑ v ∈ D ∩ centers, (insert v (graph.neighborFinset v ∩ centers)).card :=
        card_biUnion_le
      _ = 5 * (D ∩ centers).card := by
        rw [sum_congr rfl (fun v hv => center_ball_size v (mem_inter.mp hv).2)]
        simp [Nat.mul_comm]
  have hdis : Disjoint leaves (D ∩ centers) := by
    apply Finset.disjoint_left.mpr
    intro v hv hm
    have h₁ := (mem_filter.mp hv).2
    have h₂ := (mem_filter.mp (mem_inter.mp hm).2).2
    rw [h₁] at h₂
    contradiction
  have hcard := card_le_card (union_subset hL (inter_subset_left (s₁ := D) (s₂ := centers)))
  rw [card_union_of_disjoint hdis, leaves_card] at hcard
  omega

private def optimum : Finset Vertex :=
  leaves ∪ {(0, false), (1, false), (8, false), (13, false), (18, false)}

theorem twoDomination_optimum :
    ∃ D : Finset Vertex, D.card = 26 ∧ TwoDominates graph D := by
  refine ⟨optimum, by decide, ?_⟩
  have h : ∀ v : Vertex, v ∉ optimum → 2 ≤ (adjacentTo v ∩ optimum).card := by decide
  intro v hv
  simpa only [adjacentTo_eq] using h v hv

/-- Written on the Wall II, 393d, is false. The three terms are 0, 21, and 4. -/
theorem conjecture393d_counterexample :
    graph.Connected ∧ 2 < Fintype.card Vertex ∧
    univ \ openNeighbors graph (supports graph) = ∅ ∧
    (∀ S : Finset Vertex, S ⊆ univ \ (univ.filter fun v => graph.degree v = graph.maxDegree) →
      S.card ≤ 21) ∧
    leaves ⊆ univ \ (univ.filter fun v => graph.degree v = graph.maxDegree) ∧
    Independent graph leaves ∧ leaves.card = 21 ∧
    maximumK4Vertices.card = 4 ∧
    (∀ D, TwoDominates graph D → 25 < D.card) := by
  refine ⟨connected, by decide, ?_, ?_, ?_, leaves_independent, leaves_card,
    maximumK4_count, fun D hD => twoDomination_lower D hD⟩
  · change univ \ openNeighbors graph (openNeighbors graph (pendants graph)) = ∅
    rw [pendant_set, neighborhood_of_leaves, neighborhood_of_centers, sdiff_self]
    rfl
  · rw [maximum_degree_set, centers_compl]
    exact fun S hS => (card_le_card hS).trans_eq leaves_card
  · rw [maximum_degree_set, centers_compl]

#print axioms conjecture393d_counterexample
#print axioms twoDomination_optimum

end Corona
end GraffitiBatch
