import Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-! Written on the Wall II, 432b. The even–odd difference is signed. -/

namespace GraffitiBatch

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem pendants_independent (hn : 2 < Fintype.card V) (hc : G.Connected) :
    Independent G (pendants G) := by
  intro p hp q hq hpq
  obtain ⟨u, _, hu⟩ := pendant_unique G hp
  obtain ⟨v, _, hv⟩ := pendant_unique G hq
  have onlyP (w : V) (he : G.Adj p w) : w = q := (hu w he).trans (hu q hpq).symm
  have onlyQ (w : V) (he : G.Adj q w) : w = p := (hv w he).trans (hv p hpq.symm).symm
  have stays {x y : V} (w : G.Walk x y) (hx : x = p ∨ x = q) : y = p ∨ y = q := by
    induction w with
    | nil => exact hx
    | @cons a b c hab _ ih =>
      apply ih
      rcases hx with rfl | rfl
      · exact Or.inr (onlyP b hab)
      · exact Or.inl (onlyQ b hab)
  have hsub : univ ⊆ ({p, q} : Finset V) := by
    intro w _
    obtain ⟨walk⟩ := hc p w
    simpa using stays walk (Or.inl rfl)
  have hle := card_le_card hsub
  rw [card_univ, card_pair hpq.ne] at hle
  omega

def IndependentlyDominates (S : Finset V) : Prop :=
  Independent G S ∧ ∀ v ∉ S, ∃ w ∈ S, G.Adj v w

private theorem exists_independent_domination (P : Finset V) (hP : Independent G P) :
    ∃ D, P ⊆ D ∧ IndependentlyDominates G D := by
  classical
  let candidates := (univ : Finset V).powerset.filter fun D => P ⊆ D ∧ Independent G D
  obtain ⟨D, hD, hmax⟩ := exists_max_image candidates Finset.card
    ⟨P, mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _), Subset.rfl, hP⟩⟩
  obtain ⟨hPD, hInd⟩ := (mem_filter.mp hD).2
  refine ⟨D, hPD, hInd, ?_⟩
  intro v hv
  by_contra! hn
  have hNew : Independent G (insert v D) := by
    intro x hx y hy he
    rcases mem_insert.mp hx with hxv | hxD
    · subst x
      rcases mem_insert.mp hy with hyv | hyD
      · subst y
        exact G.irrefl he
      · exact hn y hyD he
    · rcases mem_insert.mp hy with hyv | hyD
      · subst y
        exact hn x hxD he.symm
      · exact hInd hxD hyD he
  have hcard := hmax (insert v D) (mem_filter.mpr
    ⟨mem_powerset.mpr (subset_univ _), fun _ h => mem_insert_of_mem (hPD h), hNew⟩)
  rw [card_insert_of_notMem hv] at hcard
  omega

noncomputable def evenLayer (r : V) : Finset V := by
  classical
  exact univ.filter fun x => G.dist r x % 2 = 0

noncomputable def parityBalance (r : V) : ℤ :=
  ((evenLayer G r).card : ℤ) - ((univ \ evenLayer G r).card : ℤ)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem walk_parity_of_coloring (c : V → Fin 2)
    (hc : ∀ ⦃v w⦄, G.Adj v w → c v ≠ c w) {v w : V} (p : G.Walk v w) :
    p.length % 2 = 0 ↔ c v = c w := by
  induction p with
  | nil => simp
  | @cons a b z hab p ih =>
    have hneq : (c a).val ≠ (c b).val := fun h => hc hab (Fin.ext h)
    have ha := (c a).isLt
    have hb := (c b).isLt
    have hz := (c z).isLt
    simp only [Fin.ext_iff] at ih ⊢
    simp only [Walk.length_cons]
    omega

omit [DecidableEq V] [DecidableRel G.Adj] in
private theorem evenLayer_mem_iff (hc : G.Connected) (c : V → Fin 2)
    (hcol : ∀ ⦃v w⦄, G.Adj v w → c v ≠ c w) (r v : V) :
    v ∈ evenLayer G r ↔ c r = c v := by
  obtain ⟨walk, hwalk⟩ := hc.exists_walk_length_eq_dist r v
  simpa [evenLayer, hwalk] using walk_parity_of_coloring G c hcol walk

private theorem supports_card_le_layer (hn : 2 < Fintype.card V) (hc : G.Connected)
    (A : Finset V) (hcross : ∀ ⦃v w⦄, G.Adj v w → (v ∈ A ↔ w ∉ A)) :
    (supports G).card ≤ A.card := by
  classical
  let S := supports G
  let U := S \ A
  let W := S ∩ A
  have hP := pendants_independent G hn hc
  have hpend (v : V) (hv : v ∈ U) : ∃ p ∈ pendants G, G.Adj v p :=
    (mem_openNeighbors G).mp (mem_sdiff.mp hv).1
  let leaf : V → V := fun v => if hv : v ∈ U then (hpend v hv).choose else v
  have hleaf (v : V) (hv : v ∈ U) : leaf v ∈ pendants G ∧ G.Adj v (leaf v) := by
    simpa only [leaf, dite_eq_left hv] using (hpend v hv).choose_spec
  have hInject : Set.InjOn leaf (U : Set V) := by
    intro v hv w hw he
    obtain ⟨x, _, hx⟩ := pendant_unique G (hleaf v hv).1
    exact (hx v (hleaf v hv).2.symm).trans (hx w (he ▸ (hleaf w hw).2.symm)).symm
  have hDisj : Disjoint W (U.image leaf) := by
    apply Finset.disjoint_left.mpr
    intro p hpW hpIm
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hpIm
    obtain ⟨q, hq, he⟩ := (mem_openNeighbors G).mp (mem_inter.mp hpW).1
    exact hP (hleaf v hv).1 hq he
  have hsub : W ∪ U.image leaf ⊆ A := by
    intro p hp
    rcases mem_union.mp hp with hp | hp
    · exact (mem_inter.mp hp).2
    · obtain ⟨v, hv, rfl⟩ := mem_image.mp hp
      exact (hcross (hleaf v hv).2.symm).mpr (mem_sdiff.mp hv).2
  have hc₁ := card_le_card hsub
  rw [card_union_of_disjoint hDisj, card_image_of_injOn hInject] at hc₁
  have hc₂ : U.card + W.card = S.card := by
    have h := card_sdiff_add_card_eq_card (s := W) (t := S) (inter_subset_left)
    have he : S \ W = U := by
      ext v
      simp only [W, U, mem_sdiff, mem_inter]
      tauto
    rwa [he] at h
  change S.card ≤ A.card
  omega

noncomputable def bipartiteTerm (r : V) : ℤ := by
  classical
  exact if G.IsBipartite then parityBalance G r else 0

/-- Written on the Wall II, 432b. A single witness works against the minimum over all roots. -/
theorem conjecture432b [Nontrivial V] (hn : 3 < Fintype.card V) (hc : G.Connected) :
    ∃ D, IndependentlyDominates G D ∧ ∀ r : V,
      (D.card : ℤ) ≤ ((univ \ supports G).card : ℤ) +
        bipartiteTerm G r := by
  classical
  by_cases hb : G.IsBipartite
  · obtain ⟨r, _, hr⟩ := exists_min_image (univ : Finset V) (parityBalance G) univ_nonempty
    have hColor := hb
    obtain ⟨c, hcol⟩ := hColor
    have hcol' ⦃v w : V⦄ (h : G.Adj v w) : c v ≠ c w := hcol h
    let A := evenLayer G r
    have hcross {v w : V} (he : G.Adj v w) : v ∈ A ↔ w ∉ A := by
      rw [evenLayer_mem_iff G hc c @hcol', evenLayer_mem_iff G hc c @hcol']
      have hne : (c v).val ≠ (c w).val := fun e => hcol' he (Fin.ext e)
      have hv := (c v).isLt
      have hw := (c w).isLt
      have hz := (c r).isLt
      simp only [Fin.ext_iff]
      omega
    have hD : IndependentlyDominates G A := by
      constructor
      · exact fun _ hx _ hy he => (hcross he).mp hx hy
      · intro v hv
        obtain ⟨w, hw⟩ := hc.preconnected.exists_adj_of_nontrivial v
        exact ⟨w, (hcross hw.symm).mpr hv, hw⟩
    have hs := supports_card_le_layer G (by omega) hc A @hcross
    have hcount (B : Finset V) : (univ \ B).card + B.card = Fintype.card V := by
      rw [card_sdiff_add_card_eq_card (subset_univ _), card_univ]
    refine ⟨A, hD, fun x => ?_⟩
    rw [bipartiteTerm, ite_eq_left hb]
    have hrx := hr x (mem_univ _)
    have hA := hcount A
    have hS := hcount (supports G)
    change (A.card : ℤ) - ((univ \ A).card : ℤ) ≤ _ at hrx
    omega
  · obtain ⟨D, hP, hD⟩ := exists_independent_domination G (pendants G)
      (pendants_independent G (by omega) hc)
    have hsub : D ⊆ univ \ supports G := by
      intro v hv
      refine mem_sdiff.mpr ⟨mem_univ _, fun hs => ?_⟩
      obtain ⟨p, hp, he⟩ := (mem_openNeighbors G).mp hs
      exact hD.1 hv (hP hp) he
    refine ⟨D, hD, fun x => ?_⟩
    simpa [bipartiteTerm, hb] using (Int.ofNat_le.mpr (card_le_card hsub))

#print axioms conjecture432b

end GraffitiBatch
