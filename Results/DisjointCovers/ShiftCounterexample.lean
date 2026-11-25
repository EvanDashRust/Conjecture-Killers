import Checker

namespace DisjointCovers

/-- The modulus occupying a position in the alternate notation. -/
def label (cs : List Class) (x : Nat) : Nat :=
  ((cs.find? (hit x)).map Prod.fst).getD 0

private def rowCount (w : Nat) (row : Nat → Nat) (m : Nat) : Nat :=
  (List.range w).countP (fun x => decide (row x = m))

private def boxCount (w : Nat) (lower upper : Nat → Nat) (m : Nat) : Nat :=
  rowCount w lower m + rowCount w upper m

/-- In a two-row rectangle, three noncollinear points have two distinct
columns in one row and a point in the other row. -/
private def HasNoncollinearHits (w : Nat) (lower upper : Nat → Nat) (m : Nat) : Prop :=
  (∃ x y z : Fin w, x ≠ y ∧ lower x = m ∧ lower y = m ∧ upper z = m) ∨
  (∃ x y z : Fin w, x ≠ y ∧ upper x = m ∧ upper y = m ∧ lower z = m)

/-- Definition 7.2 specialized to a rectangle with two rows and prescribed
modulus labels. There is one linear congruence per used modulus.
The lower coefficient bound is supplied explicitly. -/
def TwoRowIRDCSWith (minCoeff w : Nat) (lower upper : Nat → Nat) : Prop :=
  2 ≤ w ∧ ∀ m, 0 < boxCount w lower upper m →
    ∃ a b c : Nat, minCoeff ≤ a ∧ a < m ∧ minCoeff ≤ b ∧ b < m ∧ Nat.gcd a b = 1 ∧
      (∀ x < w,
        (lower x = m ↔ (a*x) % m = c % m) ∧
        (upper x = m ↔ (a*x+b) % m = c % m)) ∧
      HasNoncollinearHits w lower upper m

/-- The coefficient convention used in the worked examples. -/
abbrev TwoRowIRDCS := TwoRowIRDCSWith 1

private theorem rowCount_pos {w x m : Nat} {row : Nat → Nat}
    (hx : x < w) (hm : row x = m) : 0 < rowCount w row m :=
  List.countP_pos_iff.mpr ⟨x, List.mem_range.mpr hx, by simp [hm]⟩

private theorem rowCount_two {w m : Nat} {row : Nat → Nat}
    {x y : Fin w} (hne : x ≠ y) (hx : row x = m) (hy : row y = m) :
    2 ≤ rowCount w row m := by
  have hv : x.val ≠ y.val := fun he => hne (Fin.ext he)
  have hnodup : ([x.val, y.val] : List Nat).Nodup := by simp [List.nodup_cons, hv]
  have hsub : [x.val, y.val] ⊆ (List.range w).filter (fun z => decide (row z = m)) := by
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · simp [x.isLt, hx]
    · have he : z = y.val := by simpa using hz
      subst z
      simp [y.isLt, hy]
  simpa [rowCount, List.countP_eq_length_filter] using hnodup.length_le_of_subset hsub

private structure Necessary (w : Nat) (lower upper : Nat → Nat) : Prop where
  separated : ∀ x < w, lower x ≠ upper x
  enough : ∀ m, 0 < boxCount w lower upper m → 3 ≤ boxCount w lower upper m

private theorem necessary_of_cover {w : Nat} {lower upper : Nat → Nat}
    (h : TwoRowIRDCS w lower upper) : Necessary w lower upper := by
  constructor
  · intro x hx he
    let m := lower x
    have hp : 0 < boxCount w lower upper m := by
      have := rowCount_pos (row := lower) hx (show lower x = m from rfl)
      unfold boxCount
      omega
    obtain ⟨a, b, c, _, _, hb, hbm, _, hrows, _⟩ := h.2 m hp
    have hl := (hrows x hx).1.mp (show lower x = m from rfl)
    have hu := (hrows x hx).2.mp he.symm
    have hzero := Nat.sub_mod_eq_zero_of_mod_eq (hu.trans hl.symm)
    rw [Nat.add_sub_cancel_left, Nat.mod_eq_of_lt hbm] at hzero
    omega
  · intro m hm
    obtain ⟨_, _, _, _, _, _, _, _, _, hthree⟩ := h.2 m hm
    rcases hthree with ⟨x, y, z, hxy, hx, hy, hz⟩ | ⟨x, y, z, hxy, hx, hy, hz⟩
    · have := rowCount_two hxy hx hy
      have := rowCount_pos z.isLt hz
      unfold boxCount
      omega
    · have := rowCount_two hxy hx hy
      have := rowCount_pos z.isLt hz
      unfold boxCount
      omega

private theorem Necessary.swap {w : Nat} {lower upper : Nat → Nat}
    (h : Necessary w lower upper) : Necessary w upper lower := by
  refine ⟨fun x hx => Ne.symm (h.separated x hx), ?_⟩
  intro m hm
  simpa [boxCount, Nat.add_comm] using h.enough m (by simpa [boxCount, Nat.add_comm] using hm)

/-- The two length-20 covers, using residues on [0,20). -/
def shiftLeft : List Class := [(4,1), (6,4), (8,7), (9,2), (10,8), (11,3), (12,0), (13,6)]
def shiftRight : List Class := [(4,2), (6,3), (8,5), (9,7), (10,1), (11,8), (12,0), (13,4)]

theorem shift_left_cover : Cover 20 shiftLeft := cover_of_check (by decide)
theorem shift_right_cover : Cover 20 shiftRight := cover_of_check (by decide)

private def obstructed (w : Nat) (lower upper : Nat → Nat) : Bool :=
  ((List.range w).any fun x => decide (lower x = upper x)) ||
  ((List.range 14).any fun m =>
    let count := boxCount w lower upper m
    decide (0 < count ∧ count < 3))

private theorem not_necessary_of_obstructed {w : Nat} {lower upper : Nat → Nat}
    (h : obstructed w lower upper = true) : ¬ Necessary w lower upper := by
  intro hn
  simp only [obstructed, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq,
    List.mem_range] at h
  rcases h with ⟨x, hx, he⟩ | ⟨m, _, hpos, hlt⟩
  · exact hn.separated x hx he
  · exact (Nat.not_le_of_lt hlt) (hn.enough m hpos)

private def cropBlocked (i j w : Nat) : Bool :=
  if 2 ≤ w then obstructed w (fun x => label shiftLeft (i+x))
    (fun x => label shiftRight (j+x)) else true

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem crops_checked :
    (List.range 19).all (fun i => (List.range 19).all (fun j =>
      (List.range (21-max i j)).all (cropBlocked i j))) = true := by
  decide

/-- Even allowing arbitrary equal-width contiguous subintervals, neither order
of the rows can produce a two-dimensional IRDCS. -/
theorem no_common_width_crop (i j w : Nat)
    (hw : 2 ≤ w) (hi : i+w ≤ 20) (hj : j+w ≤ 20) :
    ¬ TwoRowIRDCS w (fun x => label shiftLeft (i+x)) (fun x => label shiftRight (j+x)) ∧
    ¬ TwoRowIRDCS w (fun x => label shiftRight (j+x)) (fun x => label shiftLeft (i+x)) := by
  have ci := List.all_eq_true.mp crops_checked i (List.mem_range.mpr (by omega))
  have cj := List.all_eq_true.mp ci j (List.mem_range.mpr (by omega))
  have ck := List.all_eq_true.mp cj w (List.mem_range.mpr (by omega))
  simp only [cropBlocked, hw, ite_true] at ck
  have hn := not_necessary_of_obstructed ck
  exact ⟨fun h => hn (necessary_of_cover h), fun h => hn (necessary_of_cover h).swap⟩

/-- Emanuel's §7.3 hypothesis. The common modulus list can be supplied in
increasing order. A common pair means that some residues agree. -/
def ShiftPremises (n : Nat) (left right : List Class) : Prop :=
  Cover n left ∧ Cover n right ∧ left.map Prod.fst = right.map Prod.fst ∧
  left ≠ right ∧ (∃ c, c ∈ left ∧ c ∈ right) ∧
  n-1 ∉ left.map Prod.fst ∧ n-1 ∉ right.map Prod.fst

/-- A successful shift in either direction would make the rows agree with a
two-dimensional cover on their overlap of width n-k. -/
def CanShift (n : Nat) (left right : List Class) : Prop :=
  ∃ k < n,
    TwoRowIRDCS (n-k) (fun x => label left (k+x)) (label right) ∨
    TwoRowIRDCS (n-k) (label left) (fun x => label right (k+x))

theorem shift_premises_hold : ShiftPremises 20 shiftLeft shiftRight := by
  refine ⟨shift_left_cover, shift_right_cover, by decide, by decide, ?_, by decide, by decide⟩
  exact ⟨(12,0), by decide, by decide⟩

theorem shift_pair_not_reflections :
    shiftLeft.map (fun c => (c.1, (19-c.2)%c.1)) ≠ shiftRight := by
  decide

/-- Negative resolution of the open question in Emanuel's thesis, §7.3. -/
theorem emanuel_shift_conjecture_false :
    ¬ (∀ n left right, ShiftPremises n left right → CanShift n left right) := by
  intro h
  obtain ⟨k, hk, hcase⟩ := h 20 shiftLeft shiftRight shift_premises_hold
  rcases hcase with hl | hr
  · apply (no_common_width_crop k 0 (20-k) hl.1 (by omega) (by omega)).1
    simpa only [Nat.zero_add] using hl
  · apply (no_common_width_crop 0 k (20-k) hr.1 (by omega) (by omega)).1
    simpa only [Nat.zero_add] using hr

#print axioms emanuel_shift_conjecture_false
#print axioms no_common_width_crop

end DisjointCovers
