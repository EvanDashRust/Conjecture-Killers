import Mathlib.Tactic

/-! A finite obstruction and an unbounded family for Araki, Conjecture 6.2. -/

namespace OuterplanarCIST

open BitVec

abbrev Core := Fin 25

def triangleList : List (Core × Core × Core) :=
  [(0, 1, 2), (0, 1, 4), (0, 2, 3), (0, 3, 6),
   (0, 4, 11), (0, 6, 7), (0, 7, 8), (0, 8, 9),
   (0, 9, 10), (0, 10, 11), (1, 2, 5), (1, 4, 12),
   (1, 5, 16), (1, 8, 13), (1, 8, 14), (1, 12, 13),
   (1, 14, 15), (1, 15, 16), (2, 3, 21), (2, 5, 17),
   (2, 8, 18), (2, 8, 19), (2, 17, 18), (2, 19, 20),
   (2, 20, 21), (3, 6, 21), (4, 11, 12), (5, 16, 17),
   (6, 7, 22), (6, 21, 22), (7, 8, 19), (7, 19, 22),
   (8, 9, 13), (8, 14, 18), (9, 10, 23), (9, 13, 23),
   (10, 11, 23), (11, 12, 23), (12, 13, 23), (14, 15, 24),
   (14, 18, 24), (15, 16, 24), (16, 17, 24), (17, 18, 24),
   (19, 20, 22), (20, 21, 22)]

abbrev Face := Fin 46

def triangle (f : Face) : Core × Core × Core := triangleList[f]

def OnFace (f : Face) (u : Core) : Prop :=
  u = (triangle f).1 ∨ u = (triangle f).2.1 ∨ u = (triangle f).2.2

instance (f : Face) (u : Core) : Decidable (OnFace f u) := by unfold OnFace; infer_instance

def neighborMasks : List (BitVec 25) :=
  [4062, 127285, 4063531, 2097221, 6147,
   196614, 6291593, 4718913, 811655, 8398081,
   8391169, 8393745, 8398866, 8393474, 17072386,
   16859138, 16941090, 17104932, 16924932, 5243268,
   6815748, 5242956, 3670208, 15872, 507904]

def CoreAdj (u v : Core) : Prop := neighborMasks[u.val]!.getLsbD v.val = true

instance (u v : Core) : Decidable (CoreAdj u v) := by unfold CoreAdj; infer_instance

theorem coreAdj_symm : ∀ u v : Core, CoreAdj u v → CoreAdj v u := by decide

theorem coreAdj_irrefl : ∀ u : Core, ¬ CoreAdj u u := by decide

theorem face_clique :
    ∀ (f : Face) (u v : Core), OnFace f u → OnFace f v → u ≠ v → CoreAdj u v := by
  decide +kernel

def boundaryCuts : List (BitVec 25 × BitVec 25) :=
  [(8, 2097221), (16, 6147), (32, 196614), (72, 6291589),
   (1024, 8391169), (2064, 8393731), (3088, 8393219), (4112, 8398851),
   (11792, 8392963), (12288, 8391442), (13840, 8390915), (16384, 17072386),
   (32768, 16859138), (65568, 16941062), (98336, 16924678), (131104, 17104902),
   (376864, 16908550), (393216, 16859428), (442400, 16843014), (524288, 5243268),
   (1048576, 6815748), (1573064, 6291717), (2097152, 5242956), (2097160, 5242949),
   (3145736, 4718661), (3670152, 4194629), (5242952, 2621573), (8393744, 10755),
   (16941088, 344070)]

/-- A cut formulation of connectivity for each of the two color classes. -/
def ColorConnected {V : Type} (adj : V → V → Prop) (color : V → Bool) : Prop :=
  ∀ (hue : Bool) (S : V → Prop),
    (∃ v, color v = hue ∧ S v) →
    (∃ v, color v = hue ∧ ¬ S v) →
    ∃ v w, color v = hue ∧ color w = hue ∧ S v ∧ ¬ S w ∧ adj v w

/-- Vertices of either color have neighbors of the other color. -/
def CrossDominates {V : Type} (adj : V → V → Prop) (color : V → Bool) : Prop :=
  ∀ v, ∃ w, adj v w ∧ color w ≠ color v

private def mixed (mask : BitVec 25) (t : Core × Core × Core) : Bool :=
  let a := mask.getLsbD t.1.val
  let b := mask.getLsbD t.2.1.val
  let c := mask.getLsbD t.2.2.val
  !((a == b) && (b == c))

private def blocks (mask : BitVec 25) (cut : BitVec 25 × BitVec 25) : Bool :=
  ((mask &&& cut.1) == cut.1) && ((mask &&& cut.2) == 0) && !((mask &&& ~~~cut.1) == 0)

private def acceptable (mask : BitVec 25) (cut : BitVec 25 × BitVec 25) : Bool :=
  !(blocks mask cut || blocks (~~~mask) cut)

private def bitPrefix (bits : BitVec 25) (depth : ℕ) : BitVec 25 :=
  BitVec.ofNat 25 (bits.toNat % 2^depth)

private theorem prefix_bit (bits : BitVec 25) (depth i : ℕ) (hi : i < 25) :
    (bitPrefix bits depth).getLsbD i = (decide (i < depth) && bits.getLsbD i) := by
  change (bits.toNat % 2^depth % 2^25).testBit i =
    (decide (i < depth) && bits.toNat.testBit i)
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  simp [hi]

private theorem prefix_step (bits : BitVec 25) (depth : ℕ) :
    bitPrefix bits (depth + 1) =
      if bits.getLsbD depth then bitPrefix bits depth ||| ((1 : BitVec 25) <<< depth)
      else bitPrefix bits depth := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hshift : (((1 : BitVec 25) <<< depth).getLsbD i) = decide (i = depth) := by
    rw [BitVec.getLsbD_shiftLeft]
    change (decide (i < 25) && !decide (i < depth) && (1#25).getLsbD (i - depth)) = _
    rw [BitVec.getLsbD_one]
    by_cases hEq : i = depth
    · subst i
      simp [hi]
    · by_cases hlt : i < depth
      · simp [hEq, hlt]
      · have hsub : i - depth ≠ 0 := by omega
        simp [hEq, hsub]
  rw [prefix_bit _ _ _ hi]
  by_cases hb : bits.getLsbD depth = true
  · rw [ite_eq_left hb, BitVec.getLsbD_or, hshift, prefix_bit _ _ _ hi]
    by_cases hEq : i = depth
    · subst i
      simp [hb]
    · have h : i < depth + 1 ↔ i < depth := by omega
      simp [hEq, h]
  · rw [ite_eq_right hb, prefix_bit _ _ _ hi]
    by_cases hEq : i = depth
    · subst i
      simp [Bool.eq_false_of_not_eq_true hb]
    · have h : i < depth + 1 ↔ i < depth := by omega
      simp [h]

private def lastIndex (t : Core × Core × Core) : ℕ := max t.1.val (max t.2.1.val t.2.2.val)

private def casesAt : ℕ → List (BitVec 25)
  | 0 => [0]
  | d + 1 =>
    let current := triangleList.filter fun t => lastIndex t == d
    ((casesAt d).flatMap fun m => [m, m ||| ((1 : BitVec 25) <<< d)]).filter
      fun m => current.all (mixed m)

private theorem surviving_prefix (bits : BitVec 25) (hm : triangleList.all (mixed bits) = true)
    (d : ℕ) (hd : d ≤ 25) : bitPrefix bits d ∈ casesAt d := by
  induction d with
  | zero =>
    simp [casesAt]
    change BitVec.ofNat 25 (bits.toNat % 1) = 0
    rw [Nat.mod_one]
    rfl
  | succ d ih =>
    apply List.mem_filter.mpr
    constructor
    · apply List.mem_flatMap.mpr
      refine ⟨bitPrefix bits d, ih (by omega), ?_⟩
      rw [prefix_step bits d]
      split <;> simp
    · rw [List.all_eq_true]
      intro t ht
      obtain ⟨hmem, hl⟩ := List.mem_filter.mp ht
      have hl' : lastIndex t = d := beq_iff_eq.mp hl
      have hma (x : Core) (hx : x.val ≤ d) :
          (bitPrefix bits (d+1)).getLsbD x.val = bits.getLsbD x.val := by
        rw [prefix_bit _ _ _ x.isLt]
        simp [show x.val < d+1 by omega]
      have h₁ : t.1.val ≤ d := by
        rw [← hl']; exact le_max_left _ _
      have h₂ : t.2.1.val ≤ d := by
        rw [← hl']; exact (le_max_left _ _).trans (le_max_right _ _)
      have h₃ : t.2.2.val ≤ d := by
        rw [← hl']; exact (le_max_right _ _).trans (le_max_right _ _)
      simpa only [mixed, hma _ h₁, hma _ h₂, hma _ h₃] using List.all_eq_true.mp hm t hmem

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
private theorem cases_blocked :
    (casesAt 25).all (fun mask => !(boundaryCuts.all (acceptable mask))) = true := by
  decide +kernel

private theorem finiteObstruction (mask : BitVec 25) :
    (triangleList.all (mixed mask) && boundaryCuts.all (acceptable mask)) = false := by
  by_contra h
  have hh := Bool.and_eq_true_iff.mp (Bool.eq_true_of_not_eq_false h)
  have hprefix : bitPrefix mask 25 = mask := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [prefix_bit _ _ _ hi]
    simp [hi]
  have hm := surviving_prefix mask hh.1 25 (by decide)
  rw [hprefix] at hm
  have hc := List.all_eq_true.mp cases_blocked mask hm
  simp [hh.2] at hc

private theorem boundaryCertified :
    ∀ cut ∈ boundaryCuts, (∃ u : Core, cut.1.getLsbD u.val = true) ∧
      ∀ u v : Core, cut.1.getLsbD u.val = true → cut.1.getLsbD v.val = false →
        CoreAdj u v → cut.2.getLsbD v.val = true := by
  decide +kernel

private def encode (c : Core → Bool) : BitVec 25 :=
  (BitVec.ofBoolListLE (List.ofFn c)).setWidth 25

@[simp] private theorem bit_encode (c : Core → Bool) (i : Core) :
    (encode c).getLsbD i.val = c i := by
  rw [encode, BitVec.getLsbD_setWidth, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD]
  have hi : i.val < (List.ofFn c).length := by simp [i.isLt]
  rw [List.getElem?_eq_getElem hi, List.getElem_ofFn]
  simp [i.isLt]

private theorem mask_nonzero {b : BitVec 25} (h : b ≠ 0) :
    ∃ u : Core, b.getLsbD u.val = true := by
  by_contra! hn
  apply h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simpa using hn ⟨i, hi⟩

private theorem blocked_forbidden (c : Core → Bool) (hc : ColorConnected CoreAdj c)
    (hue : Bool) (mask : BitVec 25) (hm : ∀ i : Core, mask.getLsbD i.val = (c i == hue))
    (cut : BitVec 25 × BitVec 25) (hcut : cut ∈ boundaryCuts) :
    blocks mask cut = false := by
  by_contra h
  have htrue : blocks mask cut = true := Bool.eq_true_of_not_eq_false h
  simp only [blocks, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at htrue
  obtain ⟨⟨hS, hB⟩, hout⟩ := htrue
  have hcolo (u : Core) (hu : cut.1.getLsbD u.val = true) : c u = hue := by
    have hb := congrArg (fun b : BitVec 25 => b.getLsbD u.val) hS
    rw [BitVec.getLsbD_and, hm, hu] at hb
    simpa using hb
  have hn (u : Core) (hu : cut.2.getLsbD u.val = true) : c u ≠ hue := by
    have hb := congrArg (fun b : BitVec 25 => b.getLsbD u.val) hB
    rw [BitVec.getLsbD_and, hm, hu] at hb
    simpa using hb
  let S := fun u : Core => cut.1.getLsbD u.val = true
  obtain ⟨u, hu⟩ := (boundaryCertified cut hcut).1
  obtain ⟨v, hv⟩ := mask_nonzero (b := mask &&& ~~~cut.1) (by simpa using hout)
  rw [BitVec.getLsbD_and, hm, BitVec.getLsbD_not] at hv
  have hv₁ : c v = hue := by simpa using (Bool.and_eq_true_iff.mp hv).1
  have hv₂ : ¬ S v := by simpa [S, v.isLt] using (Bool.and_eq_true_iff.mp hv).2
  obtain ⟨x, y, _, hy, hxS, hyS, hxy⟩ := hc hue S ⟨u, hcolo u hu, hu⟩ ⟨v, hv₁, hv₂⟩
  have hyNot : cut.1.getLsbD y.val = false := Bool.eq_false_of_not_eq_true hyS
  exact hn y ((boundaryCertified cut hcut).2 x y hxS hyNot hxy) hy

theorem base_obstruction (c : Core → Bool) (hc : ColorConnected CoreAdj c)
    (hf : ∀ (f : Face) (hue : Bool), ∃ u, OnFace f u ∧ c u = hue) : False := by
  have hallFaces : triangleList.all (mixed (encode c)) = true := by
    rw [List.all_eq_true]
    intro t ht
    obtain ⟨f, rfl⟩ := List.mem_iff_get.mp ht
    change mixed (encode c) (triangle f) = true
    simp only [mixed, bit_encode, Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne]
    by_contra! h
    have hmono : ∀ u, OnFace f u → c u = c (triangle f).1 := by
      intro u hu
      rcases hu with hu | hu | hu
      · rw [hu]
      · rw [hu, h.1]
      · rw [hu, ← h.2, ← h.1]
    obtain ⟨u, hu, huColor⟩ := hf f (!c (triangle f).1)
    rw [hmono u hu] at huColor
    exact Bool.not_ne_self _ huColor.symm
  have hallCuts : boundaryCuts.all (acceptable (encode c)) = true := by
    rw [List.all_eq_true]
    intro cut ht
    have hp := blocked_forbidden c hc true (encode c) (by intro u; rw [bit_encode]; cases c u <;> rfl) cut ht
    have hn := blocked_forbidden c hc false (~~~encode c) (by
      intro u
      rw [BitVec.getLsbD_not, bit_encode]
      simp [u.isLt]) cut ht
    simp [acceptable, hp, hn]
  simpa [hallFaces, hallCuts] using finiteObstruction (encode c)

/-- n records the number of concentric triangular layers added outside the base. -/
inductive Vertex (n : ℕ)
  | core (u : Core)
  | center (f : Face)
  | rim (layer : Fin n) (u : Fin 3)
  deriving DecidableEq

private def bridge (outer inner : Fin 3) : Prop := inner = outer ∨ inner = outer + 1

def Adj {n : ℕ} : Vertex n → Vertex n → Prop
  | .core u, .core v => CoreAdj u v
  | .core u, .center f | .center f, .core u => OnFace f u
  | .center _, .center _ => False
  | .core u, .rim l j | .rim l j, .core u =>
    l.val = 0 ∧ ((u = 0 ∧ bridge j 0) ∨ (u = 1 ∧ bridge j 1))
  | .center f, .rim l j | .rim l j, .center f =>
    l.val = 0 ∧ f = 0 ∧ bridge j 2
  | .rim l i, .rim m j =>
    (l = m ∧ i ≠ j) ∨ (l.val + 1 = m.val ∧ bridge j i) ∨
      (m.val + 1 = l.val ∧ bridge i j)

theorem adj_symm {n : ℕ} {u v : Vertex n} (h : Adj u v) : Adj v u := by
  cases u <;> cases v <;> simp only [Adj] at h ⊢
  all_goals first | exact h | exact coreAdj_symm _ _ h | tauto

theorem adj_irrefl {n : ℕ} (u : Vertex n) : ¬ Adj u u := by
  cases u <;> simp [Adj, coreAdj_irrefl]

private def region {n : ℕ} : Vertex n → Option Face
  | .core _ => none
  | .center f => some f
  | .rim _ _ => some 0

private theorem outer_edge_face {n : ℕ} {v : Vertex n} {u : Core} {f : Face}
    (hr : region v = some f) (he : Adj v (.core u)) : OnFace f u := by
  cases v with
  | core v => cases hr
  | center g =>
    have e : g = f := Option.some.inj hr
    exact e ▸ he
  | rim k j =>
    have e : 0 = f := Option.some.inj hr
    subst f
    rcases he.2 with ⟨hu, _⟩ | ⟨hu, _⟩
    · exact Or.inl hu
    · exact Or.inr (Or.inl hu)

private theorem exterior_edge_same_region {n : ℕ} {u v : Vertex n} {f g : Face}
    (hu : region u = some f) (hv : region v = some g) (he : Adj u v) : f = g := by
  cases u <;> cases v <;> simp_all [region, Adj]

private theorem different_face (f : Face) : ∃ g : Face, g ≠ f := by
  by_cases h : f = 0
  · exact ⟨1, h.symm ▸ (by decide : (1 : Face) ≠ 0)⟩
  · exact ⟨0, Ne.symm h⟩

private theorem faces_mixed {n : ℕ} (color : Vertex n → Bool)
    (hconn : ColorConnected Adj color) (hdom : CrossDominates Adj color)
    (f : Face) (hue : Bool) :
    ∃ u, OnFace f u ∧ color (.core u) = hue := by
  by_contra! hno
  let inside := fun v : Vertex n => region v = some f
  have no_cross {a b : Vertex n} (ha : inside a) (hb : ¬ inside b)
      (hbColor : color b = hue) : ¬ Adj a b := by
    intro he
    cases b with
    | core u => exact hno u (outer_edge_face ha he) hbColor
    | center g =>
      exact hb (congrArg some (exterior_edge_same_region ha (rfl : region (.center g : Vertex n) = some g) he).symm)
    | rim l i =>
      exact hb (congrArg some (exterior_edge_same_region ha (rfl : region (.rim l i) = some 0) he).symm)
  have noHueInside (a : Vertex n) (ha : inside a) : color a ≠ hue := by
    intro hcolor
    have noHueOutside (b : Vertex n) (hb : ¬ inside b) : color b ≠ hue := by
      intro hcb
      obtain ⟨x, y, _, hy, hx, hy', hxy⟩ := hconn hue inside ⟨a, hcolor, ha⟩ ⟨b, hcb, hb⟩
      exact no_cross hx hy' hy hxy
    obtain ⟨g, hg⟩ := different_face f
    have hb : ¬ inside (.center g) := fun e => hg (Option.some.inj e)
    obtain ⟨v, hv, hvC⟩ := hdom (.center g)
    have hvHue : color v = hue := by
      have hc := noHueOutside (.center g) hb
      cases hc₁ : color v <;> cases hc₂ : color (.center g) <;> cases hue <;> simp_all
    have hvIn : inside v := by
      by_contra h
      exact noHueOutside v h hvHue
    cases v with
    | core u => cases hvIn
    | center f' => exact hv
    | rim l i =>
      have hfg : f = g := exterior_edge_same_region hvIn
        (rfl : region (.center g : Vertex n) = some g) (adj_symm hv)
      exact hg hfg.symm
  obtain ⟨w, hcw, hw⟩ := hdom (.center f)
  have hwHue : color w = hue := by
    have hc := noHueInside (.center f) rfl
    cases hc₁ : color w <;> cases hc₂ : color (.center f) <;> cases hue <;> simp_all
  by_cases hin : inside w
  · exact noHueInside w hin hwHue
  · exact no_cross (rfl : inside (.center f)) hin hwHue hcw

private theorem restrict_connected {n : ℕ} (color : Vertex n → Bool)
    (hconn : ColorConnected Adj color)
    (hMixed : ∀ (f : Face) (hue : Bool), ∃ u, OnFace f u ∧ color (.core u) = hue) :
    ColorConnected CoreAdj (fun u => color (.core u)) := by
  classical
  let project : Vertex n → Core
    | .core u => u
    | .center f => (hMixed f (color (.center f))).choose
    | .rim l i => (hMixed 0 (color (.rim l i))).choose
  have hpColor (v : Vertex n) : color (.core (project v)) = color v := by
    cases v with
    | core u => rfl
    | center f => exact (hMixed f (color (.center f))).choose_spec.2
    | rim l i => exact (hMixed 0 (color (.rim l i))).choose_spec.2
  have hpFace {v : Vertex n} {f : Face} (h : region v = some f) : OnFace f (project v) := by
    cases v with
    | core u => cases h
    | center g => exact (Option.some.inj h) ▸ (hMixed g (color (.center g))).choose_spec.1
    | rim l i => exact (Option.some.inj h) ▸ (hMixed 0 (color (.rim l i))).choose_spec.1
  have hpAdj {v w : Vertex n} (he : Adj v w) (hne : project v ≠ project w) :
      CoreAdj (project v) (project w) := by
    cases v with
    | core u =>
      cases w with
      | core v => exact he
      | center g => exact face_clique g _ _ he (hpFace (v := .center g) (f := g) rfl) hne
      | rim l i =>
        exact face_clique 0 _ _ (outer_edge_face rfl (adj_symm he))
          (hpFace (v := .rim l i) (f := 0) rfl) hne
    | center f =>
      cases w with
      | core u => exact face_clique f _ _ (hpFace (v := .center f) (f := f) rfl) he hne
      | center f' => exact he.elim
      | rim l i =>
        have hfg : f = 0 := exterior_edge_same_region rfl rfl he
        exact face_clique f _ _ (hpFace (v := .center f) (f := f) rfl)
          (hpFace (v := .rim l i) (f := f) (congrArg some hfg.symm)) hne
    | rim l i =>
      cases w with
      | core u => exact face_clique 0 _ _ (hpFace (v := .rim l i) (f := 0) rfl) (outer_edge_face rfl he) hne
      | center f =>
        have hfg : 0 = f := exterior_edge_same_region rfl rfl he
        exact face_clique f _ _ (hpFace (v := .rim l i) (f := f) (congrArg some hfg))
          (hpFace (v := .center f) (f := f) rfl) hne
      | rim m j =>
        exact face_clique 0 _ _ (hpFace (v := .rim l i) (f := 0) rfl)
          (hpFace (v := .rim m j) (f := 0) rfl) hne
  intro hue S hIn hOut
  obtain ⟨u, hu, hSu⟩ := hIn
  obtain ⟨v, hv, hSv⟩ := hOut
  obtain ⟨a, b, ha, hb, hSa, hSb, hab⟩ := hconn hue (fun w => S (project w))
    ⟨.core u, hu, hSu⟩ ⟨.core v, hv, hSv⟩
  exact ⟨project a, project b, (hpColor a).trans ha, (hpColor b).trans hb, hSa, hSb,
    hpAdj hab (fun e => hSb (e ▸ hSa))⟩

/-- Every graph in the family lacks a bipartition into connected dominating sets,
the necessary condition for having two completely independent spanning trees. -/
theorem no_connected_dominating_partition (n : ℕ) :
    ¬ ∃ color : Vertex n → Bool, ColorConnected Adj color ∧ CrossDominates Adj color := by
  rintro ⟨color, hconn, hdom⟩
  have hMixed := faces_mixed color hconn hdom
  exact base_obstruction _ (restrict_connected color hconn hMixed) hMixed

#print axioms base_obstruction
#print axioms no_connected_dominating_partition

end OuterplanarCIST
