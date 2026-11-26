import IndependentDomination

/-! Written on the Wall II, 393a. Match the supports that lie in the second
open neighborhood to their leaves, then extend by a matching on the residual graph. -/

namespace GraffitiBatch

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

private def Ends (e : V × V) (v : V) : Prop := v = e.1 ∨ v = e.2

/-- Edges may be oriented arbitrarily. Distinct entries share no endpoint. -/
def MatchingIn (R : Finset V) (F : Finset (V × V)) : Prop :=
  (∀ e ∈ F, e.1 ∈ R ∧ e.2 ∈ R ∧ G.Adj e.1 e.2) ∧
  ∀ e ∈ F, ∀ f ∈ F, e ≠ f → ∀ v, Ends e v → ¬ Ends f v

private def Free (F : Finset (V × V)) (v : V) : Prop :=
  ∀ e ∈ F, ¬ Ends e v

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem MatchingIn.subset {R : Finset V} {F K : Finset (V × V)}
    (h : MatchingIn G R F) (hK : K ⊆ F) : MatchingIn G R K :=
  ⟨fun e he => h.1 e (hK he), fun e he f hf => h.2 e (hK he) f (hK hf)⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem unavailable_edge {F : Finset (V × V)} {x y : V} (hx : Free F x) : (x, y) ∉ F :=
  fun h => hx _ h (Or.inl rfl)

omit [Fintype V] [DecidableRel G.Adj] in
private theorem MatchingIn.insert_of_free {R : Finset V} {F : Finset (V × V)} {x y : V}
    (h : MatchingIn G R F) (hx : x ∈ R) (hy : y ∈ R) (he : G.Adj x y)
    (hfx : Free F x) (hfy : Free F y) : MatchingIn G R (insert (x, y) F) := by
  refine ⟨fun e he' => ?_, fun e he' f hf' hne v hev hfv => ?_⟩
  · rcases mem_insert.mp he' with rfl | hm
    · exact ⟨hx, hy, he⟩
    · exact h.1 _ hm
  · rcases mem_insert.mp he' with ee | ee <;> rcases mem_insert.mp hf' with ef | ef
    · exact hne (ee.trans ef.symm)
    · subst e
      rcases hev with rfl | rfl
      · exact hfx f ef hfv
      · exact hfy f ef hfv
    · subst f
      rcases hfv with rfl | rfl
      · exact hfx e ee hev
      · exact hfy e ee hev
    · exact h.2 _ ee _ ef hne _ hev hfv

omit [Fintype V] [DecidableRel G.Adj] in
private theorem MatchingIn.free_of_erase {R : Finset V} {F : Finset (V × V)} {e : V × V}
    (h : MatchingIn G R F) (he : e ∈ F) {v : V} (hv : Ends e v) : Free (F.erase e) v := by
  intro f hf hf'
  exact h.2 f (mem_erase.mp hf).2 e he (mem_erase.mp hf).1 v hf' hv

omit [Fintype V] [DecidableRel G.Adj] in
private theorem MatchingIn.augment {R : Finset V} {M : Finset (V × V)} {e : V × V}
    (hm : MatchingIn G R M) (he : e ∈ M)
    (hmax : ∀ F, MatchingIn G R F → F.card ≤ M.card)
    {x y : V} (hx : x ∈ R) (hy : y ∈ R) (hfx : Free M x) (hfy : Free M y)
    (hxe : G.Adj e.1 x) (hye : G.Adj e.2 y) : x = y := by
  by_contra hxy
  let K := M.erase e
  have hk := hm.subset G (erase_subset e M)
  have hL := hm.free_of_erase G he (Or.inl rfl : Ends e e.1)
  have hR := hm.free_of_erase G he (Or.inr rfl : Ends e e.2)
  have hxK : Free K x := fun f hf => hfx f (erase_subset _ _ hf)
  have hyK : Free K y := fun f hf => hfy f (erase_subset _ _ hf)
  have hK₁ := hk.insert_of_free G (hm.1 e he).1 hx hxe hL hxK
  have hK₂ : Free (insert (e.1, x) K) e.2 := by
    intro f hf hf'
    rcases mem_insert.mp hf with hf | hf
    · subst f
      rcases hf' with hleft | hright
      · exact (hm.1 e he).2.2.ne hleft.symm
      · exact hfx e he (Or.inr hright.symm)
    · exact hR f hf hf'
  have hy₂ : Free (insert (e.1, x) K) y := by
    intro f hf hf'
    rcases mem_insert.mp hf with hf | hf
    · subst f
      rcases hf' with hleft | hright
      · exact hfy e he (Or.inl hleft)
      · exact hxy hright.symm
    · exact hyK f hf hf'
  have hK₃ := hK₁.insert_of_free G (hm.1 e he).2.1 hy hye hK₂ hy₂
  have hle := hmax _ hK₃
  rw [card_insert_of_notMem (unavailable_edge hK₂),
    card_insert_of_notMem (unavailable_edge hL)] at hle
  have hcard := card_erase_add_one he
  change K.card + 2 ≤ M.card at hle
  change K.card + 1 = M.card at hcard
  omega

/-- With one endpoint selected per edge of a maximum matching, all nonisolated
vertices are selected or have a selected neighbor. -/
private theorem matched_domination (R : Finset V) :
    ∃ (M : Finset (V × V)) (Q : Finset V), MatchingIn G R M ∧ Q ⊆ R ∧
      Q.card ≤ M.card ∧
      ∀ v ∈ R, v ∉ Q → (∃ w ∈ R, G.Adj v w) → ∃ w ∈ Q, G.Adj v w := by
  classical
  let candidates := (univ : Finset (V × V)).powerset.filter (MatchingIn G R)
  have hempty : MatchingIn G R ∅ := by simp [MatchingIn]
  obtain ⟨M, hM, hmax⟩ := exists_max_image candidates Finset.card
    ⟨∅, mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _), hempty⟩⟩
  have hm := (mem_filter.mp hM).2
  have hMax (F : Finset (V × V)) (hF : MatchingIn G R F) : F.card ≤ M.card :=
    hmax F (mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _), hF⟩)
  let sel : V × V → V := fun e =>
    if ∃ z ∈ R, Free M z ∧ G.Adj e.1 z then e.1 else e.2
  let Q := M.image sel
  have hsel (e : V × V) : Ends e (sel e) := by
    unfold sel
    split
    · exact Or.inl rfl
    · exact Or.inr rfl
  refine ⟨M, Q, hm, ?_, card_image_le, ?_⟩
  · intro y hy
    obtain ⟨e, he, rfl⟩ := mem_image.mp hy
    rcases hsel e with h | h
    · exact h.symm ▸ (hm.1 e he).1
    · exact h.symm ▸ (hm.1 e he).2.1
  · intro v hv hvQ hvN
    by_cases hfree : Free M v
    · obtain ⟨w, hw, hvw⟩ := hvN
      have hnot : ¬ Free M w := by
        intro hf
        have he := hm.insert_of_free G hv hw hvw hfree hf
        have h := hMax _ he
        rw [card_insert_of_notMem (unavailable_edge hfree)] at h
        omega
      unfold Free at hnot
      push Not at hnot
      obtain ⟨e, he, hwe⟩ := hnot
      refine ⟨sel e, mem_image_of_mem _ he, ?_⟩
      rcases hwe with hw₁ | hw₂
      · have hed : G.Adj e.1 v := hw₁ ▸ hvw.symm
        simpa [sel, show ∃ z ∈ R, Free M z ∧ G.Adj e.1 z from ⟨v, hv, hfree, hed⟩]
          using hed.symm
      · have hed : G.Adj e.2 v := hw₂ ▸ hvw.symm
        by_cases hx : ∃ z ∈ R, Free M z ∧ G.Adj e.1 z
        · obtain ⟨z, hz, hfz, hez⟩ := hx
          have hzv := hm.augment G he hMax hz hv hfz hfree hez hed
          have hSel : sel e = e.1 := ite_eq_left ⟨z, hz, hfz, hez⟩
          exact hSel.symm ▸ (hzv ▸ hez).symm
        · simpa [sel, hx] using hed.symm
    · unfold Free at hfree
      push Not at hfree
      obtain ⟨e, he, hvE⟩ := hfree
      have hSel : sel e ∈ Q := mem_image_of_mem _ he
      have hne : v ≠ sel e := fun h => hvQ (h ▸ hSel)
      refine ⟨sel e, hSel, ?_⟩
      rcases hvE with hvL | hvR <;> rcases hsel e with hsL | hsR
      · exact (hne (hvL.trans hsL.symm)).elim
      · rw [hvL, hsR]
        exact (hm.1 e he).2.2
      · rw [hvR, hsL]
        exact (hm.1 e he).2.2.symm
      · exact (hne (hvR.trans hsR.symm)).elim

/-- Written on the Wall II, 393a. The exhibited matching certifies an upper
bound at most the one with the maximum matching number. -/
theorem conjecture393a [Nontrivial V] (hn : 2 < Fintype.card V) (hc : G.Connected) :
    ∃ (D : Finset V) (F : Finset (V × V)), TwoDominates G D ∧
      MatchingIn G (openNeighbors G (supports G)) F ∧ D.card ≤
        (univ \ openNeighbors G (supports G)).card + F.card + (pendants G).card := by
  classical
  let P := pendants G
  let S := supports G
  let X := openNeighbors G S
  let U := univ \ X
  let B := S ∩ X
  let R := X \ (S ∪ P)
  have hpS : Disjoint P S := by
    apply Finset.disjoint_left.mpr
    intro v hv hs
    obtain ⟨w, hw, hvw⟩ := (mem_openNeighbors G).mp hs
    exact pendants_independent G hn hc hv hw hvw
  have hPX : P ⊆ X := by
    intro p hp
    obtain ⟨s, hs, _⟩ := pendant_unique G hp
    exact (mem_openNeighbors G).mpr ⟨s, (mem_openNeighbors G).mpr ⟨p, hp, hs.symm⟩, hs⟩
  have hpend (s : V) (hs : s ∈ B) : ∃ p ∈ P, G.Adj s p :=
    (mem_openNeighbors G).mp (mem_inter.mp hs).1
  let leaf : V → V := fun s => if hs : s ∈ B then (hpend s hs).choose else s
  have hleaf (s : V) (hs : s ∈ B) : leaf s ∈ P ∧ G.Adj s (leaf s) := by
    simpa only [leaf, dite_eq_left hs] using (hpend s hs).choose_spec
  let K := B.image fun s => (s, leaf s)
  have hKcard : K.card = B.card := card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)
  have hK : MatchingIn G X K := by
    constructor
    · intro e he
      obtain ⟨s, hs, rfl⟩ := mem_image.mp he
      exact ⟨(mem_inter.mp hs).2, hPX (hleaf s hs).1, (hleaf s hs).2⟩
    · intro e he f hf hne v hev hfv
      obtain ⟨s, hs, rfl⟩ := mem_image.mp he
      obtain ⟨t, ht, rfl⟩ := mem_image.mp hf
      have hst : s ≠ t := fun h => by subst t; exact hne rfl
      rcases hev with hev | hev <;> rcases hfv with hfv | hfv
      · exact hst (hev.symm.trans hfv)
      · have he : s = leaf t := hev.symm.trans hfv
        exact Finset.disjoint_left.mp hpS (he.symm ▸ (hleaf t ht).1) (mem_inter.mp hs).1
      · have he : leaf s = t := hev.symm.trans hfv
        exact Finset.disjoint_left.mp hpS (he ▸ (hleaf s hs).1) (mem_inter.mp ht).1
      · have hEq : leaf s = leaf t := hev.symm.trans hfv
        obtain ⟨r, _, hr⟩ := pendant_unique G (hleaf s hs).1
        exact hst ((hr s (hleaf s hs).2.symm).trans
          (hr t (hEq ▸ (hleaf t ht).2.symm)).symm)
  obtain ⟨M, Q, hM, hQR, hQcard, hdom⟩ := matched_domination G R
  have hRoutside {e : V × V} {v : V} (he : e ∈ M) (hv : Ends e v) : v ∈ R := by
    rcases hv with rfl | rfl
    · exact (hM.1 e he).1
    · exact (hM.1 e he).2.1
  have hKoutside {e : V × V} {v : V} (he : e ∈ K) (hv : Ends e v) :
      v ∈ S ∪ P := by
    obtain ⟨s, hs, rfl⟩ := mem_image.mp he
    rcases hv with hv | hv
    · exact mem_union_left _ (hv.symm ▸ (mem_inter.mp hs).1)
    · exact mem_union_right _ (hv.symm ▸ (hleaf s hs).1)
  have hsep {e f : V × V} (he : e ∈ K) (hf : f ∈ M) (v : V)
      (heV : Ends e v) (hfV : Ends f v) : False :=
    (mem_sdiff.mp (hRoutside hf hfV)).2 (hKoutside he heV)
  have hF : MatchingIn G X (K ∪ M) := by
    constructor
    · intro e he
      rcases mem_union.mp he with he | he
      · exact hK.1 e he
      · exact ⟨(mem_sdiff.mp (hM.1 e he).1).1, (mem_sdiff.mp (hM.1 e he).2.1).1,
          (hM.1 e he).2.2⟩
    · intro e he f hf hef v heV hfV
      rcases mem_union.mp he with he | he <;> rcases mem_union.mp hf with hf | hf
      · exact hK.2 e he f hf hef v heV hfV
      · exact hsep he hf v heV hfV
      · exact hsep hf he v hfV heV
      · exact hM.2 e he f hf hef v heV hfV
  have hdis : Disjoint K M := Finset.disjoint_left.mpr fun e he hf =>
    hsep he hf e.1 (Or.inl rfl) (Or.inl rfl)
  let D := U ∪ P ∪ B ∪ Q
  have hDS : S ⊆ D := by
    intro v hv
    by_cases hx : v ∈ X
    · exact mem_union_left _ (mem_union_right _ (mem_inter.mpr ⟨hv, hx⟩))
    · exact mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_sdiff.mpr ⟨mem_univ _, hx⟩)))
  have hDP : P ⊆ D := fun _ h => mem_union_left _ (mem_union_left _ (mem_union_right _ h))
  have hDU : U ⊆ D := fun _ h => mem_union_left _ (mem_union_left _ (mem_union_left _ h))
  have hcount : D.card ≤ U.card + P.card + B.card + Q.card := by
    exact (card_union_le _ _).trans (Nat.add_le_add_right
      ((card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _)) _)
  refine ⟨D, K ∪ M, ?_, hF, ?_⟩
  · intro v hv
    have hX : v ∈ X := by by_contra h; exact hv (hDU (mem_sdiff.mpr ⟨mem_univ _, h⟩))
    have hR : v ∈ R := mem_sdiff.mpr ⟨hX, fun h =>
      (mem_union.mp h).elim (fun hs => hv (hDS hs)) (fun hp => hv (hDP hp))⟩
    obtain ⟨s, hs, he⟩ := (mem_openNeighbors G).mp hX
    by_cases hnR : ∃ w ∈ R, G.Adj v w
    · obtain ⟨w, hw, hvw⟩ := hdom v hR (fun h => hv (mem_union_right _ h)) hnR
      have hNE : s ≠ w := fun h => (mem_sdiff.mp (hQR hw)).2 (mem_union_left _ (h ▸ hs))
      have hsub : ({s, w} : Finset V) ⊆ G.neighborFinset v ∩ D := by
        intro x hx
        rcases mem_insert.mp hx with rfl | hx
        · exact mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr he, hDS hs⟩
        · have h := mem_singleton.mp hx
          subst x
          exact mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hvw, mem_union_right _ hw⟩
      simpa [card_pair hNE] using card_le_card hsub
    · have hall : G.neighborFinset v ⊆ D := by
        intro w hw
        by_contra h
        have hwX : w ∈ X := by by_contra he; exact h (hDU (mem_sdiff.mpr ⟨mem_univ _, he⟩))
        have hwR : w ∈ R := mem_sdiff.mpr ⟨hwX, fun hm =>
          (mem_union.mp hm).elim (fun hs => h (hDS hs)) (fun hp => h (hDP hp))⟩
        exact hnR ⟨w, hwR, (G.mem_neighborFinset _ _).mp hw⟩
      rw [inter_eq_left.mpr hall, card_neighborFinset_eq_degree]
      have hpos := he.degree_pos_left
      have hne : G.degree v ≠ 1 := fun h => hv (hDP (mem_filter.mpr ⟨mem_univ _, h⟩))
      omega
  · change D.card ≤ U.card + (K ∪ M).card + P.card
    rw [card_union_of_disjoint hdis, hKcard]
    omega

#print axioms conjecture393a

end GraffitiBatch
