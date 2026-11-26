import Basic
import Mathlib.Combinatorics.SimpleGraph.Star

/-! The two local-independence bounds in Written on the Wall II, 161 and 162. -/

namespace GraffitiBatch

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem tree_degree_le_leaves [Nontrivial V] (hT : G.IsTree) (r : V) :
    G.degree r ≤ (pendants G).card := by
  let U := univ.erase r
  let L := U.filter fun v => G.degree v = 1
  let I := U.filter fun v => G.degree v ≠ 1
  have hpart : L.card + I.card = U.card := card_filter_add_card_filter_not (s := U) _
  have hu : U.card + 1 = Fintype.card V := by
    dsimp only [U]
    rw [card_erase_add_one (mem_univ r), card_univ]
  have hl : ∑ v ∈ L, G.degree v = L.card := by
    calc
      _ = ∑ _v ∈ L, (1 : ℕ) := sum_congr rfl fun v hv => (mem_filter.mp hv).2
      _ = _ := by simp
  have hi : 2 * I.card ≤ ∑ v ∈ I, G.degree v := by
    calc
      _ = ∑ _v ∈ I, (2 : ℕ) := by simp [Nat.mul_comm]
      _ ≤ _ := by
        apply sum_le_sum
        intro v hv
        obtain ⟨w, hw⟩ := hT.connected.preconnected.exists_adj_of_nontrivial v
        have hpos := hw.degree_pos_left
        have hne := (mem_filter.mp hv).2
        omega
  have hsum : (∑ v ∈ L, G.degree v) + (∑ v ∈ I, G.degree v) + G.degree r =
      2 * (Fintype.card V - 1) := by
    rw [show (∑ v ∈ L, G.degree v) + (∑ v ∈ I, G.degree v) = ∑ v ∈ U, G.degree v
        from sum_filter_add_sum_filter_not _ _ _]
    rw [sum_erase_add _ _ (mem_univ r), G.sum_degrees_eq_twice_card_edges]
    have he := hT.card_edgeFinset
    omega
  have hleaves : L.card ≤ (pendants G).card :=
    card_le_card fun v hv => mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hv).2⟩
  omega

omit [Fintype V] [DecidableRel G.Adj] in
private theorem crossing_edge (hc : G.Connected) {S : Finset V} {x y : V}
    (hx : x ∈ S) (hy : y ∉ S) : ∃ v ∈ S, ∃ w ∉ S, G.Adj v w := by
  obtain ⟨p⟩ := hc x y
  induction p with
  | nil => exact False.elim (hy hx)
  | @cons a b c h _ ih =>
    by_cases hb : b ∈ S
    · exact ih hb hy
    · exact ⟨a, hx, b, hb, h⟩

/-- Written on the Wall II, 161. Every proper clique is bounded by the leaf maximum.
The source's complement-neighborhood independent sets are such cliques. -/
theorem conjecture161 (hc : G.Connected) :
    ∃ T : SimpleGraph V, ∃ _ : DecidableRel T.Adj, T ≤ G ∧ T.IsTree ∧
      ∀ x : V, ∀ K : Finset V, (↑K : Set V) ⊆ Gᶜ.neighborSet x →
        Gᶜ.IsIndepSet (↑K : Set V) → K.card ≤ (pendants T).card := by
  classical
  by_cases hn : Nontrivial V
  · let := hn
    obtain ⟨r, hr⟩ := G.exists_maximal_degree_vertex
    let H := G ⊓ starGraph r
    have ha : H.IsAcyclic := (isAcyclic_starGraph r).anti inf_le_right
    obtain ⟨T, hHT, hTG, hT⟩ := hc.exists_isTree_le_of_le_of_isAcyclic inf_le_left ha
    let : DecidableRel T.Adj := Classical.decRel _
    have hdeg : G.degree r ≤ T.degree r := by
      rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
      exact card_le_card fun v hv => (T.mem_neighborFinset _ _).mpr
        (hHT (⟨(G.mem_neighborFinset _ _).mp hv,
          starGraph_center_adj ((G.mem_neighborFinset _ _).mp hv).ne⟩ : H.Adj r v))
    refine ⟨T, inferInstance, hTG, hT, fun x K hx hK => ?_⟩
    by_cases hk : K.Nonempty
    · obtain ⟨k, hk⟩ := hk
      have hxK : x ∉ K := fun h => Gᶜ.irrefl (hx h)
      obtain ⟨v, hv, w, hw, hvw⟩ := crossing_edge G hc hk hxK
      have hCl : G.IsClique (↑K : Set V) := by simpa using hK
      have hi : insert w (K.erase v) ⊆ G.neighborFinset v := by
        intro u hu
        apply (G.mem_neighborFinset _ _).mpr
        rcases mem_insert.mp hu with rfl | hu
        · exact hvw
        · exact hCl hv (mem_erase.mp hu).2 (mem_erase.mp hu).1.symm
      have hcard : (insert w (K.erase v)).card = K.card := by
        rw [card_insert_of_notMem (fun h => hw (mem_erase.mp h).2), card_erase_add_one hv]
      have hKdeg := card_le_card hi
      rw [hcard, card_neighborFinset_eq_degree] at hKdeg
      exact hKdeg.trans ((G.degree_le_maxDegree v).trans
        (hr ▸ hdeg.trans (tree_degree_le_leaves T hT r)))
    · simp [not_nonempty_iff_eq_empty.mp hk]
  · have : Subsingleton V := not_nontrivial_iff_subsingleton.mp hn
    obtain ⟨T, hTG, hT⟩ := hc.exists_isTree_le
    let : DecidableRel T.Adj := Classical.decRel _
    refine ⟨T, inferInstance, hTG, hT, fun x K hx _ => ?_⟩
    have he : K = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro v hv
      have hvx : v = x := Subsingleton.elim _ _
      exact Gᶜ.irrefl (hvx ▸ hx hv)
    simp [he]

def Simplicial (v : V) : Prop := G.IsClique (G.neighborSet v)

noncomputable def localIndependence (v : V) : ℕ := (G.induce (G.neighborSet v)).indepNum

omit [DecidableEq V] [DecidableRel G.Adj] in
private theorem localIndependence_pos [Nontrivial V] (hc : G.Connected) (v : V) :
    1 ≤ localIndependence G v := by
  obtain ⟨w, hw⟩ := hc.preconnected.exists_adj_of_nontrivial v
  let W : G.neighborSet v := ⟨w, hw⟩
  have hs : (G.induce (G.neighborSet v)).IsIndepSet (↑({W} : Finset (G.neighborSet v))) := by simp
  simpa [localIndependence] using hs.card_le_indepNum

private theorem localIndependence_one_iff [Nontrivial V] (hc : G.Connected) (v : V) :
    localIndependence G v = 1 ↔ Simplicial G v := by
  classical
  constructor
  · intro h a ha b hb hab
    by_contra he
    let A : G.neighborSet v := ⟨a, ha⟩
    let B : G.neighborSet v := ⟨b, hb⟩
    have hn : A ≠ B := fun e => hab (congrArg Subtype.val e)
    have hs : (G.induce (G.neighborSet v)).IsIndepSet
        (↑({A, B} : Finset (G.neighborSet v))) := by
      have hes : ¬ G.Adj b a := fun e => he e.symm
      simpa [Set.pairwise_pair, hn, SimpleGraph.induce, A, B] using And.intro he hes
    have hle := hs.card_le_indepNum
    rw [card_pair hn] at hle
    change 2 ≤ localIndependence G v at hle
    rw [h] at hle
    omega
  · intro hs
    let H := G.induce (G.neighborSet v)
    obtain ⟨K, hK, hcard⟩ := H.exists_isNIndepSet_indepNum
    have hsub : K.card ≤ 1 := by
      apply card_le_one.mpr
      intro x hx y hy
      by_contra hxy
      have hne : (x : V) ≠ y := fun e => hxy (Subtype.ext e)
      exact hK hx hy hxy (hs x.property y.property hne)
    have hpos := localIndependence_pos G hc v
    change 1 ≤ H.indepNum at hpos
    change H.indepNum = 1
    omega

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem predecessor_nonsimplicial (hc : G.Connected) {x y z : V}
    (hyz : G.Adj y z) (hz : G.dist x z + 1 = G.dist x y) (hd : 2 ≤ G.dist x y) :
    ¬ Simplicial G z := by
  have hzx : z ≠ x := by
    intro e
    subst z
    simp at hz
    omega
  obtain ⟨w, hzw, hw⟩ := distance_predecessor G hc x z hzx
  intro hs
  have hwy : w ≠ y := by
    intro e
    subst w
    omega
  have he := hs hzw hyz.symm hwy
  have ht := hc.dist_triangle (u := x) (v := w) (w := y)
  rw [G.dist_eq_one_iff_adj.mpr he] at ht
  omega

omit [DecidableRel G.Adj] in
private theorem spanning_tree_simplicial_leaves (hc : G.Connected)
    (hcore : ∃ v, ¬ Simplicial G v) :
    ∃ T : SimpleGraph V, ∃ _ : DecidableRel T.Adj, T ≤ G ∧ T.IsTree ∧
      ∀ v, Simplicial G v → T.degree v = 1 := by
  classical
  obtain ⟨r, hr⟩ := hcore
  have hattach (v : V) (hv : Simplicial G v) :
      ∃ u, G.Adj v u ∧ ¬ Simplicial G u := by
    have hne : v ≠ r := fun e => hr (e ▸ hv)
    obtain ⟨u, hu, hdist⟩ := distance_predecessor G hc r v hne
    refine ⟨u, hu, ?_⟩
    by_cases hd : 2 ≤ G.dist r v
    · exact predecessor_nonsimplicial G hc hu hdist hd
    · have hu₀ : G.dist r u = 0 := by omega
      have he := hc.dist_eq_zero_iff.mp hu₀
      exact he ▸ hr
  let next : V → V := fun v => if h : Simplicial G v then (hattach v h).choose else v
  have hnext (v : V) (hv : Simplicial G v) : G.Adj v (next v) ∧ ¬ Simplicial G (next v) := by
    simpa only [next, dite_eq_left hv] using (hattach v hv).choose_spec
  let H : SimpleGraph V :=
    { Adj := fun a b => G.Adj a b ∧
        (Simplicial G a → b = next a) ∧ (Simplicial G b → a = next b)
      symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
      loopless := ⟨fun _ h => G.irrefl h.1⟩ }
  have hpath (v : V) (hv : ¬ Simplicial G v) : H.Reachable v r := by
    generalize he : G.dist r v = k
    induction k using Nat.strong_induction_on generalizing v with
    | ind k ih =>
      by_cases hvr : v = r
      · subst v
        exact Reachable.rfl
      · obtain ⟨u, hu, hdist⟩ := distance_predecessor G hc r v hvr
        have hu' : ¬ Simplicial G u := by
          by_cases hd : 2 ≤ G.dist r v
          · exact predecessor_nonsimplicial G hc hu hdist hd
          · have he := hc.dist_eq_zero_iff.mp (by omega : G.dist r u = 0)
            exact he ▸ hr
        have hed : H.Adj v u := ⟨hu, fun h => (hv h).elim, fun h => (hu' h).elim⟩
        exact hed.reachable.trans (ih (G.dist r u) (by omega) u hu' rfl)
  have hreach (v : V) : H.Reachable v r := by
    by_cases hv : Simplicial G v
    · have h := hnext v hv
      have he : H.Adj v (next v) := ⟨h.1, fun _ => rfl, fun h' => (h.2 h').elim⟩
      exact he.reachable.trans (hpath (next v) h.2)
    · exact hpath v hv
  have : Nonempty V := ⟨r⟩
  have hH : H.Connected := ⟨fun x y => (hreach x).trans (hreach y).symm⟩
  obtain ⟨T, hTH, hT⟩ := hH.exists_isTree_le
  let : DecidableRel T.Adj := Classical.decRel _
  refine ⟨T, inferInstance, fun _ _ h => (hTH h).1, hT, fun v hv => ?_⟩
  have : Nontrivial V := ⟨v, next v, (hnext v hv).1.ne⟩
  obtain ⟨w, hw⟩ := hT.connected.preconnected.exists_adj_of_nontrivial v
  exact degree_eq_one_iff_existsUnique_adj.mpr ⟨w, hw, fun y hy =>
    ((hTH hy).2.1 hv).trans ((hTH hw).2.1 hv).symm⟩

/-- Written on the Wall II, 162. The denominator is defined for connected graphs of order ≥ 2. -/
theorem conjecture162 [Nontrivial V] (hc : G.Connected) :
    ∃ (r : V) (T : SimpleGraph V), ∃ _ : DecidableRel T.Adj, T ≤ G ∧ T.IsTree ∧
      (∀ v : V, localIndependence G r ≤ localIndependence G v) ∧
      (Finset.filter (fun v => localIndependence G v = localIndependence G r) univ).card *
        (1 / G.minDegree) ≤ (pendants T).card := by
  classical
  obtain ⟨r, _, hr⟩ := exists_min_image (univ : Finset V) (localIndependence G) univ_nonempty
  have hpos (v : V) : 1 ≤ G.degree v := by
    obtain ⟨w, hw⟩ := hc.preconnected.exists_adj_of_nontrivial v
    exact hw.degree_pos_left
  obtain ⟨p, hp⟩ := G.exists_minimal_degree_vertex
  by_cases hd : G.minDegree = 1
  · have hpd : p ∈ pendants G := mem_filter.mpr ⟨mem_univ _, hp.symm.trans hd⟩
    obtain ⟨u, hpu, hu⟩ := pendant_unique G hpd
    have hpS : Simplicial G p := fun a ha b hb hn =>
      (hn ((hu a ha).trans (hu b hb).symm)).elim
    have hr₁ : localIndependence G r = 1 := by
      have h := hr p (mem_univ _)
      rw [(localIndependence_one_iff G hc p).mpr hpS] at h
      exact Nat.le_antisymm h (localIndependence_pos G hc r)
    by_cases hcore : ∃ v, ¬ Simplicial G v
    · obtain ⟨T, _, hle, hT, hs⟩ := spanning_tree_simplicial_leaves G hc hcore
      refine ⟨r, T, inferInstance, hle, hT, fun v => hr v (mem_univ _), ?_⟩
      simp only [hr₁, hd, Nat.div_one, mul_one]
      exact card_le_card fun v hv => mem_filter.mpr ⟨mem_univ _,
        hs v ((localIndependence_one_iff G hc v).mp (mem_filter.mp hv).2)⟩
    · have huS : Simplicial G u := by
        by_contra hx
        exact hcore ⟨u, hx⟩
      have onlyU (v : V) (hv : G.Adj u v) : v = p := by
        by_contra hvp
        exact hv.ne (hu v (huS hv hpu.symm hvp).symm).symm
      have hPair (v : V) : v = p ∨ v = u := by
        obtain ⟨w⟩ := hc p v
        have stays {a b : V} (w : G.Walk a b) (ha : a = p ∨ a = u) :
            b = p ∨ b = u := by
          induction w with
          | nil => exact ha
          | @cons a c b hac _ ih =>
            rcases ha with rfl | rfl
            · exact ih (Or.inr (hu c hac))
            · exact ih (Or.inl (onlyU c hac))
        exact stays w (Or.inl rfl)
      obtain ⟨T, hle, hT⟩ := hc.exists_isTree_le
      let : DecidableRel T.Adj := Classical.decRel _
      have hEvery (v : V) : T.degree v = 1 := by
        obtain ⟨w, hw⟩ := hT.connected.preconnected.exists_adj_of_nontrivial v
        refine degree_eq_one_iff_existsUnique_adj.mpr ⟨w, hw, fun x hx => ?_⟩
        rcases hPair v with rfl | rfl
        · exact (hu x (hle hx)).trans (hu w (hle hw)).symm
        · exact (onlyU x (hle hx)).trans (onlyU w (hle hw)).symm
      refine ⟨r, T, inferInstance, hle, hT, fun v => hr v (mem_univ _), ?_⟩
      simp only [hd, Nat.div_one, mul_one]
      exact card_le_card fun v _ => mem_filter.mpr ⟨mem_univ _, hEvery v⟩
  · have hn : 1 < G.minDegree := by have := hpos p; omega
    obtain ⟨T, hle, hT⟩ := hc.exists_isTree_le
    let : DecidableRel T.Adj := Classical.decRel _
    refine ⟨r, T, inferInstance, hle, hT, fun v => hr v (mem_univ _), ?_⟩
    simp [Nat.div_eq_of_lt hn]

#print axioms conjecture161
#print axioms conjecture162

end GraffitiBatch
