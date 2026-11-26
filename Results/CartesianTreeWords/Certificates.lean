import Basic

namespace CartesianTreeWords

def leech (a : Letter) (j : Nat) : Letter :=
  ([0, 1, 2, 1, 0, 2, 1, 2, 0, 1, 2, 1, 0] : List Letter).getD j 0 + a

def markerCode (a : Letter) (j : Nat) : Letter :=
  let block : List Letter :=
    if a = 0 then [0, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 1]
    else if a = 1 then [0, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 1]
    else [0, 2, 2, 2, 1, 2, 1, 1, 2, 2, 2, 1]
  block.getD j 0

private def squareB (w : Word) (i p : Nat) : Bool :=
  (List.range p).all (fun j => w (i+j) == w (i+p+j))

private theorem squareB_spec (w : Word) (i p : Nat) :
    squareB w i p = true ↔ Square w i p := by
  simp [squareB, Square, List.all_eq_true]

private def minimaB (w : Word) (i p : Nat) : Bool :=
  (List.range p).all (fun a =>
    (List.range (p-a)).all (fun k =>
      firstMin w (i+a) (k+1) == firstMin w (i+p+a) (k+1)))

private theorem minimaB_spec (w : Word) (i p : Nat) :
    minimaB w i p = true ↔ SameMinima w w i (i+p) p := by
  simp only [minimaB, SameMinima, List.all_eq_true, List.mem_range, beq_iff_eq]
  constructor
  · intro h a k hk ha
    have q := h a (by omega) (k-1) (by omega)
    have : k-1+1 = k := by omega
    simpa only [this] using q
  · intro h a ha k hk
    exact h a (k+1) (by omega) (by omega)

private def freeB (w : Word) (n : Nat) : Bool :=
  (List.range n).all (fun i =>
    (List.range n).all (fun k => if i+2*(k+1) ≤ n then !squareB w i (k+1) else true))

private theorem freeB_of_free {w : Word} {n : Nat} (h : SquareFreeUpTo w n) :
    freeB w n = true := by
  unfold freeB
  apply List.all_eq_true.mpr
  intro i _
  apply List.all_eq_true.mpr
  intro k _
  split
  · rename_i hk
    have hn := h i (k+1) (by omega) hk
    cases he : squareB w i (k+1) with
    | false => rfl
    | true => exact (hn ((squareB_spec _ _ _).mp he)).elim
  · rfl

private def shortB (L stop first : Nat) (test : Word → Nat → Nat → Bool)
    (w : Word) (n : Nat) : Bool :=
  (List.range L).all (fun i => (List.range stop).all (fun p =>
    if first ≤ p ∧ i+2*p ≤ L*n then !test w i p else true))

private def ShortCertificate (L stop first : Nat) (test : Word → Nat → Nat → Bool)
    (code : Code) : Prop :=
  ∀ a b c d e : Letter, ∀ m : Fin 6,
    freeB (pack a b c d e) m.val = true →
      shortB L stop first test (expand L code (pack a b c d e)) m.val = true

set_option maxHeartbeats 7000000
set_option maxRecDepth 16000

private theorem leech_small : ShortCertificate 13 26 1 squareB leech := by
  unfold ShortCertificate
  decide +kernel

private theorem cartesian_small : ShortCertificate 12 12 3 minimaB markerCode := by
  unfold ShortCertificate
  decide +kernel

private theorem small_cover {L n i p : Nat} (hL : 0 < L)
    (hEnd : i+2*p ≤ L*n) (hSmall : i%L+2*p ≤ L*5) :
    ∃ m ≤ 5, i/L + m ≤ n ∧ i%L+2*p ≤ L*m := by
  have hq : i/L ≤ n := (Nat.div_le_iff_le_mul_add_pred hL).mpr (by omega)
  have hd := Nat.div_add_mod i L
  have hs : L*(n-i/L) = L*n-L*(i/L) := by rw [Nat.mul_sub]
  by_cases hs5 : n-i/L ≤ 5
  · exact ⟨n-i/L, hs5, by omega, by omega⟩
  · exact ⟨5, by omega, by omega, hSmall⟩

private theorem short_checked {L stop first n i p : Nat} {test : Word → Nat → Nat → Bool}
    {code : Code} {w : Word} (hc : ShortCertificate L stop first test code)
    (hL : 0 < L) (hw : SquareFreeUpTo w n) (hEnd : i+2*p ≤ L*n)
    (hSmall : i%L+2*p ≤ L*5) (hp : first ≤ p) (hStop : p < stop) :
    ∃ (v : Word), test v (i%L) p = false ∧
      ∀ j < 2*p, v (i%L+j) = expand L code w (i+j) := by
  obtain ⟨m, hm, hn, hend⟩ := small_cover hL hEnd hSmall
  let q := i/L
  let v := pack (w q) (w (q+1)) (w (q+2)) (w (q+3)) (w (q+4))
  have good : freeB v m = true := freeB_of_free (pack_free hw hm hn)
  have hcert := hc (w q) (w (q+1)) (w (q+2)) (w (q+3)) (w (q+4)) ⟨m, by omega⟩ good
  have hi : i%L ∈ List.range L := List.mem_range.mpr (Nat.mod_lt _ hL)
  have hp' : p ∈ List.range stop := List.mem_range.mpr hStop
  have hout := List.all_eq_true.mp (List.all_eq_true.mp hcert _ hi) _ hp'
  refine ⟨expand L code v, ?_, ?_⟩
  · rw [ite_eq_left (And.intro hp hend)] at hout
    change (!test (expand L code v) (i%L) p) = true at hout
    cases ht : test (expand L code v) (i%L) p with
    | false => rfl
    | true => simp [ht] at hout
  · intro j hj
    have heq := expand_pack hL code w q (i%L+j) m hm (by omega)
    have hi' : q*L+(i%L+j) = i+j := by
      have h := Nat.div_add_mod i L
      rw [Nat.mul_comm L (i/L)] at h
      change i/L*L+(i%L+j)=i+j
      omega
    simpa only [hi'] using heq.symm

theorem no_short_leech_square {w : Word} {n i p : Nat}
    (h : SquareFreeUpTo w n) (hp : 0 < p) (hlen : i+2*p ≤ 13*n) (hs : p < 26) :
    ¬ Square (expand 13 leech w) i p := by
  intro sq
  obtain ⟨v, hv, equal⟩ := short_checked leech_small (by decide) h hlen (by omega) hp hs
  have hsquare : Square v (i%13) p := by
    intro j hj
    calc
      v (i%13+j) = expand 13 leech w (i+j) := equal j (by omega)
      _ = expand 13 leech w (i+p+j) := sq j hj
      _ = v (i%13+p+j) := by
        simpa only [Nat.add_assoc] using (equal (p+j) (by omega)).symm
  have ht := (squareB_spec _ _ _).mpr hsquare
  rw [hv] at ht
  contradiction

theorem no_short_cartesian_square {w : Word} {n i p : Nat}
    (h : SquareFreeUpTo w n) (hp : 3 ≤ p) (hlen : i+2*p ≤ 12*n) (hs : p < 12) :
    ¬ SameMinima (expand 12 markerCode w) (expand 12 markerCode w) i (i+p) p := by
  intro sq
  obtain ⟨v, hv, equal⟩ := short_checked cartesian_small (by decide) h hlen (by omega) hp hs
  have hsquare : SameMinima v v (i%12) (i%12+p) p := by
    intro a k hk hsize
    have h1 : firstMin v (i%12+a) k = firstMin (expand 12 markerCode w) (i+a) k := by
      apply firstMin_congr
      intro j hj
      simpa only [Nat.add_assoc] using equal (a+j) (by omega)
    have h2 : firstMin v (i%12+p+a) k = firstMin (expand 12 markerCode w) (i+p+a) k := by
      apply firstMin_congr
      intro j hj
      simpa only [Nat.add_assoc] using equal (p+a+j) (by omega)
    rw [h1,h2]
    exact sq a k hk hsize
  have ht := (minimaB_spec _ _ _).mpr hsquare
  rw [hv] at ht
  contradiction

theorem leech_first (a : Letter) : leech a 0 = a := by
  simp [leech]

/-- No unaligned factor of two blocks is a codeword. -/
theorem leech_sync :
    ∀ (a b c : Letter) (r : Fin 13), 0 < r.val →
      ¬ (∀ j : Fin 13, expand 13 leech (pack a b 0 0 0) (r.val+j.val) = leech c j.val) := by
  decide

theorem marker_at_zero (a : Letter) : markerCode a 0 = 0 := by
  decide +revert

theorem marker_in_payload :
    ∀ (a : Letter) (j : Fin 12), 0 < j.val → markerCode a j.val ≠ 0 := by
  decide

/-- Two range-minimum queries distinguish the payload near either end. -/
theorem marker_distinguishes :
    ∀ (a b : Letter) (r : Fin 2),
      firstMin (markerCode a) (1+7*r.val) 4 = firstMin (markerCode b) (1+7*r.val) 4 →
      firstMin (markerCode a) (2+7*r.val) 3 = firstMin (markerCode b) (2+7*r.val) 3 →
      a = b := by
  decide

end CartesianTreeWords
