import Std

namespace Graffiti255

/-- A finite simple graph with vertices numbered from 0 to n-1. -/
structure Graph (n : Nat) where
  adj : Fin n → Fin n → Bool
  symmetric : ∀ u v, adj u v = adj v u
  loopless : ∀ u, adj u u = false

namespace Graph

/-- Whether there is a walk of length at most k. -/
def reaches (G : Graph n) : Nat → Fin n → Fin n → Bool
  | 0, u, v => u == v
  | k + 1, u, v =>
      G.reaches k u v ||
        (List.finRange n).any (fun w => G.adj u w && G.reaches k w v)

def Connected (G : Graph n) : Prop :=
  ∀ u v, ∃ k, G.reaches k u v = true

def EccAtMost (G : Graph n) (k : Nat) (u : Fin n) : Prop :=
  ∀ v, G.reaches k u v = true

/-- The vertex reaches every other vertex within a globally minimal radius. -/
def IsCenter (G : Graph n) (u : Fin n) : Prop :=
  ∃ r, G.EccAtMost r u ∧ ∀ v k, G.EccAtMost k v → r ≤ k

def TotallyDominates (G : Graph n) (vertices : List (Fin n)) : Prop :=
  ∀ v, vertices.any (G.adj v) = true

def edgeNeighborhoodSize (G : Graph n) (u v : Fin n) : Nat :=
  (List.finRange n).countP (fun w => G.adj u w || G.adj v w)

end Graph

/-- Clear the denominator in the published inequality. Equivalently, for every
total dominating set, some edge has a large enough open neighborhood union.
On a finite connected graph of order at least two, taking a smallest such set
and an edge maximizing the union recovers the printed formulation. -/
def Conjecture : Prop :=
  ∀ (n : Nat) (G : Graph n), 2 ≤ n → G.Connected →
    ∀ centers : List (Fin n), centers.Nodup →
      (∀ v, v ∈ centers ↔ G.IsCenter v) →
      ∀ D : List (Fin n), D.Nodup → G.TotallyDominates D →
        ∃ u v, G.adj u v = true ∧
          2 * centers.length ≤ D.length * G.edgeNeighborhoodSize u v

/-- Vertices 0–4 form a clique. For each i in that clique, vertex i+5 is
the middle of a two-edge path from i to the common hub 10. -/
private def orderedAdj (u v : Nat) : Bool :=
  (v < 5) || (u < 5 && v == u + 5) || (5 ≤ u && v == 10)

private def adjacent (u v : Fin 11) : Bool :=
  u != v && orderedAdj (min u.val v.val) (max u.val v.val)

def witness : Graph 11 where
  adj := adjacent
  symmetric := by decide
  loopless := by decide

set_option maxHeartbeats 4000000
set_option maxRecDepth 12000

private theorem allPairsWithinTwo : ∀ u v, witness.reaches 2 u v = true := by
  decide

theorem witness_connected : witness.Connected :=
  fun u v => ⟨2, allPairsWithinTwo u v⟩

private theorem noSmallerRadius :
    ∀ (u : Fin 11) (k : Fin 2), ∃ v, witness.reaches k.val u v = false := by
  decide

theorem every_vertex_is_a_center (u : Fin 11) : witness.IsCenter u := by
  refine ⟨2, allPairsWithinTwo u, ?_⟩
  intro v k h
  by_cases hk : 2 ≤ k
  · exact hk
  · have hk' : k < 2 := by omega
    obtain ⟨w, hw⟩ := noSmallerRadius v ⟨k, hk'⟩
    rw [h w] at hw
    contradiction

def dominatingSet : List (Fin 11) := [0, 5, 10]

theorem dominating_set_works : witness.TotallyDominates dominatingSet := by
  change ∀ v, dominatingSet.any (witness.adj v) = true
  decide

private theorem noDominatingPair :
    ∀ (a b : Fin 11), ∃ v, witness.adj v a = false ∧ witness.adj v b = false := by
  decide

theorem total_domination_at_least_three (D : List (Fin 11))
    (h : witness.TotallyDominates D) : 3 ≤ D.length := by
  cases D with
  | nil =>
      have := h 0
      simp at this
  | cons a tail =>
      cases tail with
      | nil =>
          obtain ⟨v, hva, _⟩ := noDominatingPair a a
          have := h v
          simp [hva] at this
      | cons b tail =>
          cases tail with
          | nil =>
              obtain ⟨v, hva, hvb⟩ := noDominatingPair a b
              have := h v
              simp [hva, hvb] at this
          | cons c tail => simp

theorem every_edge_neighborhood_has_size_seven :
    ∀ u v, witness.adj u v = true → witness.edgeNeighborhoodSize u v = 7 := by
  decide

theorem seven_is_attained :
    witness.adj 0 5 = true ∧ witness.edgeNeighborhoodSize 0 5 = 7 := by
  decide

theorem conjecture255_false : ¬ Conjecture := by
  intro conjecture
  have hcenters : ∀ v, v ∈ List.finRange 11 ↔ witness.IsCenter v :=
    fun v => ⟨fun _ => every_vertex_is_a_center v, fun _ => List.mem_finRange v⟩
  obtain ⟨u, v, huv, hbound⟩ :=
    conjecture 11 witness (by decide) witness_connected (List.finRange 11)
      (by decide) hcenters dominatingSet (by decide) dominating_set_works
  have hsize := every_edge_neighborhood_has_size_seven u v huv
  change 2 * 11 ≤ 3 * witness.edgeNeighborhoodSize u v at hbound
  omega

#print axioms conjecture255_false

end Graffiti255
