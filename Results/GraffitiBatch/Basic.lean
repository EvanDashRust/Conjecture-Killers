import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Metric

/-! Definitions shared by the Written on the Wall II proofs. -/

namespace GraffitiBatch

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def openNeighbors (S : Finset V) : Finset V :=
  S.biUnion (fun v => G.neighborFinset v)

@[simp] theorem mem_openNeighbors {S : Finset V} {v : V} :
    v ∈ openNeighbors G S ↔ ∃ s ∈ S, G.Adj v s := by
  simp only [openNeighbors, Finset.mem_biUnion, G.mem_neighborFinset]
  exact ⟨fun ⟨s, hs, h⟩ => ⟨s, hs, h.symm⟩, fun ⟨s, hs, h⟩ => ⟨s, hs, h.symm⟩⟩

def pendants : Finset V := univ.filter fun v => G.degree v = 1

abbrev supports := openNeighbors G (pendants G)

def once (S : Finset V) : Finset V :=
  univ.filter fun v => (G.neighborFinset v ∩ S).card = 1

/-- Definition 90 of the catalog. A vertex in the set has no extra requirement. -/
def TwoDominates (D : Finset V) : Prop :=
  ∀ v ∉ D, 2 ≤ (G.neighborFinset v ∩ D).card

def TotalDominates (D : Finset V) : Prop :=
  ∀ v, ∃ w ∈ D, G.Adj v w

def Independent (D : Finset V) : Prop :=
  ∀ ⦃v⦄, v ∈ D → ∀ ⦃w⦄, w ∈ D → ¬ G.Adj v w

theorem support_not_adjacent_to_pendant {v w : V}
    (hv : v ∉ supports G) (hw : w ∈ pendants G) : ¬ G.Adj v w :=
  fun h => hv ((mem_openNeighbors G).mpr ⟨w, hw, h⟩)

omit [DecidableEq V] in
theorem pendant_unique {v : V} (hv : v ∈ pendants G) :
    ∃! w, G.Adj v w :=
  SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp (Finset.mem_filter.mp hv).2

theorem openNeighbors_mono {A B : Finset V} (h : A ⊆ B) :
    openNeighbors G A ⊆ openNeighbors G B := by
  intro v hv
  obtain ⟨w, hw, he⟩ := (mem_openNeighbors G).mp hv
  exact (mem_openNeighbors G).mpr ⟨w, h hw, he⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem distance_predecessor (hConn : G.Connected) (r x : V) (hx : x ≠ r) :
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

end GraffitiBatch
