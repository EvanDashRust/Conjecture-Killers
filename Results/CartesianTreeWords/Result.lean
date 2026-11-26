import Certificates

namespace CartesianTreeWords

private theorem leech_square_aligned {w : Word} {i p : Nat} (hp : 26 ≤ p)
    (sq : Square (expand 13 leech w) i p) : p%13 = 0 := by
  let a := (i+12)/13
  let b := (a*13+p)/13
  let r := p%13
  have hNear : i ≤ a*13 ∧ a*13 < i+13 := by dsimp [a]; omega
  have hb : a*13+p = b*13+r := by dsimp [b,r]; omega
  by_cases hr : r = 0
  · exact hr
  · exfalso
    have hpos : 0 < r := Nat.pos_of_ne_zero hr
    apply leech_sync (w b) (w (b+1)) (w a) ⟨r, Nat.mod_lt _ (by decide)⟩ hpos
    intro j
    have ej := sq (a*13-i+j.val) (by omega)
    have h1 : i+(a*13-i+j.val) = a*13+j.val := by omega
    have h2 : i+p+(a*13-i+j.val) = b*13+(r+j.val) := by omega
    rw [h1, h2, expand_block (by decide : 0 < 13) leech w a _ j.isLt,
      expand_shift (by decide : 0 < 13) leech w b (r+j.val)] at ej
    have qRange : (r+j.val)/13 < 2 := by dsimp [r]; omega
    change expand 13 leech (pack (w b) (w (b+1)) 0 0 0) (r+j.val) = leech (w a) j.val
    rw [ej]
    have casesQ : (r+j.val)/13 = 0 ∨ (r+j.val)/13 = 1 := by omega
    rcases casesQ with hh | hh <;> simp [expand, hh, pack, shift]

theorem leech_preserves {w : Word} {n : Nat} (hw : SquareFreeUpTo w n) :
    SquareFreeUpTo (expand 13 leech w) (13*n) := by
  intro i p hp hEnd sq
  by_cases hSmall : p < 26
  · exact no_short_leech_square hw hp hEnd hSmall sq
  · have hmod := leech_square_aligned (by omega) sq
    let a := (i+12)/13
    let q := p/13
    have hNear : i ≤ a*13 ∧ a*13 < i+13 := by dsimp [a]; omega
    have heq : p = 13*q := by dsimp [q]; omega
    have hBound : a+2*q ≤ n := by omega
    apply hw a q (by omega) hBound
    intro j hj
    have e := sq ((a+j)*13-i) (by omega)
    have h1 : i+((a+j)*13-i) = (a+j)*13+0 := by omega
    have h2 : i+p+((a+j)*13-i) = (a+q+j)*13+0 := by omega
    rw [h1, h2, expand_block (by decide : 0 < 13) leech w (a+j) 0 (by decide),
      expand_block (by decide : 0 < 13) leech w (a+q+j) 0 (by decide),
      leech_first, leech_first] at e
    exact e

private theorem expands_eq_zero (w : Word) (i : Nat) :
    expand 12 markerCode w i = 0 ↔ i%12 = 0 := by
  unfold expand
  constructor
  · intro h
    by_cases hi : i%12 = 0
    · exact hi
    · have hpos : 0 < i%12 := Nat.pos_of_ne_zero hi
      exact (marker_in_payload (w (i/12)) ⟨i%12, by omega⟩ hpos h).elim
  · intro h
    rw [h, marker_at_zero]

private theorem marker_minimum (w : Word) (i : Nat) :
    firstMin (expand 12 markerCode w) i 12 = (12-i%12)%12 := by
  apply firstMin_of_unique_zero
  · omega
  · apply (expands_eq_zero _ _).mpr
    omega
  · intro j hj hne hz
    have h := (expands_eq_zero _ _).mp hz
    omega

private theorem cartesian_square_aligned {w : Word} {i p : Nat} (hp : 12 ≤ p)
    (sq : SameMinima (expand 12 markerCode w) (expand 12 markerCode w) i (i+p) p) :
    p%12 = 0 := by
  have h := sq 0 12 (by decide) (by omega)
  simp only [Nat.add_zero, marker_minimum] at h
  omega

private theorem minimum_inside_block (w : Word) (a j k : Nat) (h : j+k ≤ 12) :
    firstMin (expand 12 markerCode w) (a*12+j) k = firstMin (markerCode (w a)) j k := by
  apply firstMin_congr
  intro t ht
  rw [Nat.add_assoc]
  exact expand_block (by decide) markerCode w a (j+t) (by omega)

theorem marker_preserves {w : Word} {n : Nat} (hw : SquareFreeUpTo w n) :
    CartesianFreeUpTo (expand 12 markerCode w) (12*n) := by
  intro i p hp hEnd sq
  by_cases hSmall : p < 12
  · exact no_short_cartesian_square hw hp hEnd hSmall sq
  · have hmod := cartesian_square_aligned (by omega) sq
    let q := p/12
    have heq : p = 12*q := by dsimp [q]; omega
    let a := if i%12 ≤ 8 then i/12 else i/12+1
    let cut : Fin 2 := if i%12 ≤ 8 then 1 else 0
    let j0 := 1+7*cut.val
    have hCut : i ≤ a*12+j0 ∧ a*12+j0+4 ≤ i+12 ∧ j0+4 ≤ 12 ∧ a*12 < i+12 := by
      dsimp [a, j0, cut]
      split <;> omega
    apply hw a q (by omega) (by omega)
    intro j hj
    let offset := (a+j)*12+j0-i
    have h1 : i+offset = (a+j)*12+j0 := by dsimp [offset]; omega
    have h2 : i+p+offset = (a+q+j)*12+j0 := by omega
    have e1 := sq offset 4 (by decide) (by dsimp [offset]; omega)
    have e2 := sq (offset+1) 3 (by decide) (by dsimp [offset]; omega)
    rw [h1, h2, minimum_inside_block _ _ _ _ hCut.2.2.1,
      minimum_inside_block _ _ _ _ hCut.2.2.1] at e1
    have hh1 : i+(offset+1) = (a+j)*12+(j0+1) := by omega
    have hh2 : i+p+(offset+1) = (a+q+j)*12+(j0+1) := by omega
    rw [hh1, hh2, minimum_inside_block _ _ _ _ (by omega),
      minimum_inside_block _ _ _ _ (by omega)] at e2
    have hj0 : j0+1 = 2+7*cut.val := by dsimp [j0]; omega
    rw [hj0] at e2
    exact marker_distinguishes (w (a+j)) (w (a+q+j)) cut e1 e2

private def iterate : Nat → Word
  | 0 => fun _ => 0
  | k+1 => expand 13 leech (iterate k)

private def prefixLength : Nat → Nat
  | 0 => 1
  | k+1 => 13*prefixLength k

private theorem prefix_length_ge (k : Nat) : k < prefixLength k := by
  induction k with
  | zero => decide
  | succ k ih =>
      rw [prefixLength]
      omega

private theorem iterate_free (k : Nat) : SquareFreeUpTo (iterate k) (prefixLength k) := by
  induction k with
  | zero =>
      intro i p hp hEnd
      change i+2*p ≤ 1 at hEnd
      omega
  | succ k ih => exact leech_preserves ih

private theorem iterate_step_agrees (k i : Nat) (hi : i < prefixLength k) :
    iterate k i = iterate (k+1) i := by
  induction k generalizing i with
  | zero =>
      change i < 1 at hi
      have : i = 0 := by omega
      subst i
      decide
  | succ k ih =>
      change i < 13*prefixLength k at hi
      change leech (iterate k (i/13)) (i%13) = leech (iterate (k+1) (i/13)) (i%13)
      rw [ih (i/13) (by omega)]

private theorem prefix_length_mono {k m : Nat} (hkm : k ≤ m) :
    prefixLength k ≤ prefixLength m := by
  induction m with
  | zero => simp [Nat.eq_zero_of_le_zero hkm]
  | succ m ih =>
      by_cases hk : k = m+1
      · exact hk ▸ Nat.le_refl _
      · have h := ih (by omega)
        rw [prefixLength]
        omega

private theorem iterate_agrees {k m i : Nat} (hkm : k ≤ m) (hi : i < prefixLength k) :
    iterate k i = iterate m i := by
  induction m with
  | zero => rw [Nat.eq_zero_of_le_zero hkm]
  | succ m ih =>
      by_cases hk : k = m+1
      · rw [hk]
      · have hm : k ≤ m := by omega
        have hlen := prefix_length_mono hm
        exact (ih hm).trans (iterate_step_agrees m i (by omega))

def squareFreeSource (i : Nat) : Letter := iterate i i

theorem source_square_free (n : Nat) : SquareFreeUpTo squareFreeSource n := by
  intro i p hp hEnd sq
  apply iterate_free n i p hp (by have := prefix_length_ge n; omega)
  intro j hj
  have e := sq j hj
  unfold squareFreeSource at e
  rw [iterate_agrees (by omega : i+j ≤ n) (prefix_length_ge _),
      iterate_agrees (by omega : i+p+j ≤ n) (prefix_length_ge _)] at e
  exact e

def infiniteWord : Word := expand 12 markerCode squareFreeSource

/-- The ternary Cartesian-tree entry (threshold 3) conjectured in Table 2. -/
theorem infinite_ternary_cartesian_square_free :
    ∃ w : Word, ∀ i p, 3 ≤ p → ¬ SameCartesian w i (i+p) p := by
  refine ⟨infiniteWord, ?_⟩
  intro i p hp hc
  exact marker_preserves (source_square_free (i+2*p)) i p hp (by omega)
    (sameCartesian_minima hc)

#print axioms infinite_ternary_cartesian_square_free

end CartesianTreeWords
