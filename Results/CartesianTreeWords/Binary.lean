import Result

namespace CartesianTreeWords

/-- A seven-uniform morphism with output alphabet `0 < 1`. -/
def binaryCode (a : Letter) (j : Nat) : Fin 2 :=
  let block : List (Fin 2) :=
    if a = 0 then [0, 0, 1, 0, 1, 0, 1]
    else if a = 1 then [1, 0, 0, 1, 0, 0, 0]
    else [1, 1, 1, 0, 1, 1, 0]
  block.getD j 0

/-- Embed the binary alphabet in the common ordered alphabet, preserving each rank. -/
def binaryRank (a : Fin 2) : Letter := ⟨a.val, by omega⟩

private def binaryCodeRank (a : Letter) (j : Nat) : Letter :=
  binaryRank (binaryCode a j)

set_option maxHeartbeats 7000000 in
set_option maxRecDepth 16000 in
private theorem binary_short : ShortCertificate 7 14 4 minimaB binaryCodeRank := by
  unfold ShortCertificate
  decide +kernel

/-- A codeword cannot have the same minima as an unaligned window across two
distinct adjacent codewords. -/
private theorem binary_sync :
    ∀ (a b c : Letter) (r : Fin 7), a ≠ b → 0 < r.val →
      ¬ (∀ (u k : Fin 7), u.val+(k.val+1) ≤ 7 →
        firstMin (binaryCodeRank c) u.val (k.val+1) =
          firstMin (expand 7 binaryCodeRank (pack a b 0 0 0)) (r.val+u.val) (k.val+1)) := by
  decide +kernel

/-- The length-four prefix and the length-three suffix each identify the input
letter by their first-minimum offsets. -/
private theorem binary_distinguishes :
    ∀ (a b : Letter) (r : Fin 2),
      firstMin (binaryCodeRank a) (4*r.val) (4-r.val) =
        firstMin (binaryCodeRank b) (4*r.val) (4-r.val) → a = b := by
  decide +kernel

private theorem binary_minimum_inside_block (w : Word) (a j k : Nat) (h : j+k ≤ 7) :
    firstMin (expand 7 binaryCodeRank w) (a*7+j) k =
      firstMin (binaryCodeRank (w a)) j k := by
  apply firstMin_congr
  intro t ht
  rw [Nat.add_assoc]
  exact expand_block (by decide) binaryCodeRank w a (j+t) (by omega)

private theorem binary_square_aligned {w : Word} {n i p : Nat}
    (hw : SquareFreeUpTo w n) (hp : 14 ≤ p) (hEnd : i+2*p ≤ 7*n)
    (sq : SameMinima (expand 7 binaryCodeRank w) (expand 7 binaryCodeRank w) i (i+p) p) :
    p%7 = 0 := by
  let a := (i+6)/7
  let b := (a*7+p)/7
  let r := p%7
  have near : i ≤ a*7 ∧ a*7 < i+7 := by dsimp [a]; omega
  have hb : a*7+p = b*7+r := by dsimp [b, r]; omega
  by_cases hr : r = 0
  · exact hr
  exfalso
  have hrpos : 0 < r := Nat.pos_of_ne_zero hr
  have hab : w b ≠ w (b+1) := by
    intro h
    apply hw b 1 (by decide) (by omega)
    intro j hj
    have hj0 : j = 0 := by omega
    simpa [hj0] using h
  apply binary_sync (w b) (w (b+1)) (w a) ⟨r, by dsimp [r]; omega⟩ hab hrpos
  intro u k hwin
  have e := sq (a*7-i+u.val) (k.val+1) (by omega) (by omega)
  have h1 : i+(a*7-i+u.val) = a*7+u.val := by omega
  have h2 : i+p+(a*7-i+u.val) = b*7+(r+u.val) := by omega
  rw [h1, h2, binary_minimum_inside_block _ _ _ _ hwin] at e
  refine e.trans (firstMin_congr ?_)
  intro t ht
  have he : b*7+(r+u.val)+t = b*7+(r+u.val+t) := by omega
  rw [he, expand_shift (by decide : 0 < 7)]
  change expand 7 binaryCodeRank (shift w b) (r+u.val+t) =
    expand 7 binaryCodeRank (pack (w b) (w (b+1)) 0 0 0) (r+u.val+t)
  have hBlock : (r+u.val+t)/7 = 0 ∨ (r+u.val+t)/7 = 1 := by
    dsimp [r]
    omega
  rcases hBlock with h | h <;> simp [expand, h, shift, pack]

private theorem binary_preserves {w : Word} {n i p : Nat}
    (hw : SquareFreeUpTo w n) (hp : 4 ≤ p) (hEnd : i+2*p ≤ 7*n) :
    ¬ SameMinima (expand 7 binaryCodeRank w) (expand 7 binaryCodeRank w) i (i+p) p := by
  intro sq
  by_cases hSmall : p < 14
  · exact no_short_cartesian_square_of_certificate binary_short (by decide)
      hw hp hEnd hSmall (by omega) sq
  have hmod := binary_square_aligned hw (by omega) hEnd sq
  let q := p/7
  have hperiod : p = 7*q := by dsimp [q]; omega
  let a := if i%7 ≤ 4 then i/7 else i/7+1
  let cut : Fin 2 := if i%7 ≤ 4 then 1 else 0
  let start := 4*cut.val
  let len := 4-cut.val
  have hCut : i ≤ a*7+start ∧ a*7+start+len ≤ i+7 ∧
      start+len ≤ 7 ∧ a*7 < i+7 ∧ 0 < len := by
    dsimp [a, start, len, cut]
    split <;> omega
  apply hw a q (by omega) (by omega)
  intro j hj
  let offset := (a+j)*7+start-i
  have h1 : i+offset = (a+j)*7+start := by dsimp [offset]; omega
  have h2 : i+p+offset = (a+q+j)*7+start := by omega
  have e := sq offset len hCut.2.2.2.2 (by dsimp [offset]; omega)
  rw [h1, h2, binary_minimum_inside_block _ _ _ _ hCut.2.2.1,
    binary_minimum_inside_block _ _ _ _ hCut.2.2.1] at e
  exact binary_distinguishes (w (a+j)) (w (a+q+j)) cut e

def infiniteBinaryWord (i : Nat) : Fin 2 := binaryCode (squareFreeSource (i/7)) (i%7)

/-- The binary Cartesian-tree entry (threshold 4) conjectured in Table 2. -/
theorem infinite_binary_cartesian_square_free :
    ∃ w : Nat → Fin 2, ∀ i p, 4 ≤ p → ¬ SameCartesian (binaryRank ∘ w) i (i+p) p := by
  refine ⟨infiniteBinaryWord, ?_⟩
  intro i p hp hc
  exact binary_preserves (source_square_free (i+2*p)) hp (by omega)
    (sameCartesian_minima hc)

#print axioms infinite_binary_cartesian_square_free

end CartesianTreeWords
