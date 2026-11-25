import Graffiti255.Counterexample

namespace Graffiti256

open Graffiti255 (Graph)

def degree (G : Graph n) (v : Fin n) : Nat :=
  (List.finRange n).countP (G.adj v)

def minimumDegreeVertices (G : Graph n) : List (Fin n) :=
  let vertices := List.finRange n
  vertices.filter (fun u => vertices.all (fun v => degree G u ≤ degree G v))

theorem mem_minimumDegreeVertices (G : Graph n) (u : Fin n) :
    u ∈ minimumDegreeVertices G ↔ ∀ v, degree G u ≤ degree G v := by
  simp [minimumDegreeVertices, List.all_eq_true, List.mem_finRange]

/-- Cardinality of the union of the open neighborhoods of the listed vertices. -/
def neighborhoodSize (G : Graph n) (vertices : List (Fin n)) : Nat :=
  (List.finRange n).countP (fun u => vertices.any (G.adj u))

/-- Clearing the denominator, the published inequality says that for every
total dominating set, some edge attains the required product. A minimum total
dominating set and an edge maximizing the neighborhood union give equivalence. -/
def Conjecture : Prop :=
  ∀ (n : Nat) (G : Graph n), 2 ≤ n → G.Connected →
    ∀ D : List (Fin n), D.Nodup → G.TotallyDominates D →
      ∃ u v, G.adj u v = true ∧
        2 * neighborhoodSize G (minimumDegreeVertices G) ≤
          D.length * G.edgeNeighborhoodSize u v

/-- The common endpoints are 0 and 2. The two-edge path goes through 1.
The six three-edge paths go through i and i+6 for i from 3 to 8. -/
private def orderedAdj (u v : Nat) : Bool :=
  (u == 0 && (v == 1 || (3 ≤ v && v ≤ 8))) ||
  (u == 1 && v == 2) ||
  (u == 2 && 9 ≤ v) ||
  (3 ≤ u && u ≤ 8 && v == u + 6)

private def adjacent (u v : Fin 15) : Bool :=
  u != v && orderedAdj (min u.val v.val) (max u.val v.val)

def witness : Graph 15 where
  adj := adjacent
  symmetric := by decide
  loopless := by decide

set_option maxHeartbeats 4000000
set_option maxRecDepth 12000

private theorem allPairsWithinThree :
    ∀ (u v : Fin 15), witness.reaches 3 u v = true := by
  decide

theorem witness_connected : witness.Connected :=
  fun u v => ⟨3, allPairsWithinThree u v⟩

theorem minimum_degree_vertices :
    minimumDegreeVertices witness = [1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14] := by
  decide

theorem minimum_degree_neighborhood_size :
    neighborhoodSize witness (minimumDegreeVertices witness) = 14 := by
  decide

def dominatingSet : List (Fin 15) := [0, 1, 2]

theorem dominating_set_works : witness.TotallyDominates dominatingSet := by
  change ∀ v, dominatingSet.any (witness.adj v) = true
  decide

private theorem noDominatingPair :
    ∀ (a b : Fin 15), ∃ v, witness.adj v a = false ∧ witness.adj v b = false := by
  decide

theorem total_domination_at_least_three (D : List (Fin 15))
    (h : witness.TotallyDominates D) : 3 ≤ D.length := by
  match D with
  | [] =>
      have impossible := h 0
      simp at impossible
  | [a] =>
      obtain ⟨v, ha, _⟩ := noDominatingPair a a
      have impossible := h v
      simp [ha] at impossible
  | [a, b] =>
      obtain ⟨v, ha, hb⟩ := noDominatingPair a b
      have impossible := h v
      simp [ha, hb] at impossible
  | _ :: _ :: _ :: _ => simp

theorem edge_neighborhood_size_at_most_nine :
    ∀ (u v : Fin 15), witness.adj u v = true → witness.edgeNeighborhoodSize u v ≤ 9 := by
  decide

theorem nine_is_attained : witness.adj 0 1 = true ∧ witness.edgeNeighborhoodSize 0 1 = 9 := by
  decide

theorem conjecture256_false : ¬ Conjecture := by
  intro conjecture
  obtain ⟨u, v, huv, hineq⟩ :=
    conjecture 15 witness (by decide) witness_connected dominatingSet
      (by decide) dominating_set_works
  have hmax := edge_neighborhood_size_at_most_nine u v huv
  rw [minimum_degree_neighborhood_size] at hineq
  change 2 * 14 ≤ 3 * witness.edgeNeighborhoodSize u v at hineq
  omega

#print axioms conjecture256_false

end Graffiti256
