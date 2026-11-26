import Std

namespace CartesianTreeWords

abbrev Letter := Fin 3
abbrev Word := Nat → Letter

def Square (w : Word) (i p : Nat) : Prop :=
  ∀ j < p, w (i + j) = w (i + p + j)

def SquareFreeUpTo (w : Word) (n : Nat) : Prop :=
  ∀ i p, 0 < p → i + 2 * p ≤ n → ¬ Square w i p

/-- Leftmost minimum, returned as an offset within a nonempty interval. -/
def firstMin (w : Word) (i : Nat) : Nat → Nat
  | 0 => 0
  | 1 => 0
  | k + 2 =>
      let p := firstMin w i (k + 1)
      if (w (i + (k + 1))).val < (w (i + p)).val then k + 1 else p

def IsFirstMin (w : Word) (i len p : Nat) : Prop :=
  p < len ∧
    (∀ q < len, (w (i+p)).val ≤ (w (i+q)).val) ∧
    (∀ q < p, (w (i+p)).val < (w (i+q)).val)

theorem firstMin_spec (w : Word) (i len : Nat) (hlen : 0 < len) :
    IsFirstMin w i len (firstMin w i len) := by
  induction len with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero =>
        simp only [firstMin, IsFirstMin]
        refine ⟨by omega, ?_, by omega⟩
        intro q hq
        have : q = 0 := by omega
        subst q
        exact Nat.le_refl _
    | succ k =>
        have old := ih (by omega)
        let p := firstMin w i (k+1)
        change IsFirstMin w i (k+1) p at old
        obtain ⟨hp, hlow, hfirst⟩ := old
        rw [firstMin]
        change IsFirstMin w i (k+1+1)
          (if (w (i+(k+1))).val < (w (i+p)).val then k+1 else p)
        split
        · rename_i h
          refine ⟨by omega, ?_, ?_⟩
          · intro q hq
            by_cases heq : q = k+1
            · subst q
              exact Nat.le_refl _
            · have hq' := hlow q (by omega)
              omega
          · intro q hq
            have hq' := hlow q hq
            omega
        · rename_i h
          refine ⟨by omega, ?_, hfirst⟩
          intro q hq
          by_cases heq : q = k+1
          · subst q
            omega
          · exact hlow q (by omega)

theorem firstMin_unique {w : Word} {i n p q : Nat}
    (hp : IsFirstMin w i n p) (hq : IsFirstMin w i n q) : p = q := by
  by_cases hl : p < q
  · have a := hp.2.1 q hq.1
    have b := hq.2.2 p hl
    omega
  · by_cases hg : q < p
    · have a := hq.2.1 p hp.1
      have b := hp.2.2 q hg
      omega
    · omega

theorem firstMin_of_unique_zero {w : Word} {i len offset : Nat}
    (hoffset : offset < len) (hz : w (i+offset) = 0)
    (hn : ∀ j < len, j ≠ offset → w (i+j) ≠ 0) :
    firstMin w i len = offset := by
  apply firstMin_unique (firstMin_spec w i len (by omega))
  refine ⟨hoffset, ?_, ?_⟩
  · intro j _
    rw [hz]
    exact Nat.zero_le _
  · intro j hj
    rw [hz]
    have hj0 := hn j (by omega) (by omega)
    have hval : (w (i+j)).val ≠ 0 := fun h => hj0 (Fin.ext h)
    exact Nat.pos_of_ne_zero hval

theorem firstMin_congr {w v : Word} {i j len : Nat}
    (h : ∀ t < len, w (i+t) = v (j+t)) :
    firstMin w i len = firstMin v j len := by
  by_cases hlen : 0 < len
  · obtain ⟨hp, hlow, hfirst⟩ := firstMin_spec w i len hlen
    apply firstMin_unique _ (firstMin_spec v j len hlen)
    refine ⟨hp, ?_, ?_⟩
    · intro q hq
      rw [← h _ hp, ← h q hq]
      exact hlow q hq
    · intro q hq
      rw [← h _ hp, ← h q (by omega)]
      exact hfirst q hq
  · have : len = 0 := by omega
    simp [this, firstMin]

def SameMinima (w v : Word) (i j len : Nat) : Prop :=
  ∀ a k, 0 < k → a + k ≤ len → firstMin w (i+a) k = firstMin v (j+a) k

def CartesianFreeUpTo (w : Word) (n : Nat) : Prop :=
  ∀ i p, 3 ≤ p → i + 2*p ≤ n → ¬ SameMinima w w i (i+p) p

inductive Tree where
  | empty
  | node (left right : Tree)

def Tree.size : Tree → Nat
  | .empty => 0
  | .node l r => l.size + 1 + r.size

/-- An ordered Cartesian tree with leftmost tie-breaking. -/
inductive IsCartesian (w : Word) : Nat → Tree → Prop where
  | empty (i : Nat) : IsCartesian w i .empty
  | node {i : Nat} {l r : Tree} :
      IsFirstMin w i (Tree.size (.node l r)) l.size →
      IsCartesian w i l → IsCartesian w (i+l.size+1) r →
      IsCartesian w i (.node l r)

def SameCartesian (w : Word) (i j len : Nat) : Prop :=
  ∃ t : Tree, t.size = len ∧ IsCartesian w i t ∧ IsCartesian w j t

private theorem firstMin_restrict {w : Word} {i len p a k : Nat}
    (hmin : IsFirstMin w i len p) (ha : a ≤ p) (hkp : p < a+k) (hend : a+k ≤ len) :
    firstMin w (i+a) k = p-a := by
  apply firstMin_unique (firstMin_spec w (i+a) k (by omega))
  refine ⟨by omega, ?_, ?_⟩
  · intro q hq
    have h1 : i+a+(p-a) = i+p := by omega
    have h2 : i+a+q = i+(a+q) := by omega
    rw [h1, h2]
    exact hmin.2.1 (a+q) (by omega)
  · intro q hq
    have h1 : i+a+(p-a) = i+p := by omega
    have h2 : i+a+q = i+(a+q) := by omega
    rw [h1, h2]
    exact hmin.2.2 (a+q) (by omega)

theorem isCartesian_minima {w v : Word} {i j : Nat} {t : Tree}
    (h1 : IsCartesian w i t) (h2 : IsCartesian v j t) : SameMinima w v i j t.size := by
  induction t generalizing i j with
  | empty =>
      intro a k hk hend
      simp [Tree.size] at hend
      omega
  | node l r ihl ihr =>
      cases h1 with
      | node hwi hwl hwr =>
        cases h2 with
        | node hvj hvl hvr =>
          intro a k hk hend
          simp only [Tree.size] at hend
          by_cases hLeft : a+k ≤ l.size
          · exact ihl hwl hvl a k hk hLeft
          · by_cases hRight : l.size < a
            · have hw : i+a = (i+l.size+1)+(a-(l.size+1)) := by omega
              have hv : j+a = (j+l.size+1)+(a-(l.size+1)) := by omega
              rw [hw,hv]
              exact ihr hwr hvr (a-(l.size+1)) k hk (by omega)
            · rw [firstMin_restrict hwi (by omega) (by omega) hend,
                  firstMin_restrict hvj (by omega) (by omega) hend]

theorem sameCartesian_minima {w : Word} {i j len : Nat}
    (h : SameCartesian w i j len) : SameMinima w w i j len := by
  obtain ⟨t, rfl, hi, hj⟩ := h
  exact isCartesian_minima hi hj

abbrev Code := Letter → Nat → Letter

def expand (L : Nat) (code : Code) (w : Word) : Word :=
  fun t => code (w (t/L)) (t%L)

def shift (w : Word) (a : Nat) : Word :=
  fun j => w (a+j)

def pack (a b c d e : Letter) : Word
  | 0 => a | 1 => b | 2 => c | 3 => d | _ => e

theorem pack_shift (w : Word) (s j : Nat) (hj : j < 5) :
    pack (w s) (w (s+1)) (w (s+2)) (w (s+3)) (w (s+4)) j = w (s+j) := by
  match j with
  | 0 | 1 | 2 | 3 | 4 => rfl
  | j+5 => omega

theorem pack_free {w : Word} {n s m : Nat}
    (h : SquareFreeUpTo w n) (hm : m ≤ 5) (hend : s+m ≤ n) :
    SquareFreeUpTo (pack (w s) (w (s+1)) (w (s+2)) (w (s+3)) (w (s+4))) m := by
  intro i p hp bound sq
  apply h (s+i) p hp (by omega)
  intro j hj
  have eq := sq j hj
  rw [pack_shift w s _ (by omega), pack_shift w s _ (by omega)] at eq
  simpa [Nat.add_assoc] using eq

theorem expand_shift {L : Nat} (hL : 0 < L) (code : Code) (w : Word) (s i : Nat) :
    expand L code w (s*L+i) = expand L code (shift w s) i := by
  have hd : (s*L+i)/L = s+i/L := by
    rw [Nat.mul_comm s L, Nat.add_comm, Nat.add_mul_div_left _ _ hL]
    omega
  have hr : (s*L+i)%L = i%L := by simp [Nat.add_mod]
  simp [expand, shift, hd, hr]

theorem expand_pack {L : Nat} (hL : 0 < L) (code : Code) (w : Word) (s i m : Nat)
    (hm : m ≤ 5) (hi : i < L*m) :
    expand L code w (s*L+i) =
      expand L code (pack (w s) (w (s+1)) (w (s+2)) (w (s+3)) (w (s+4))) i := by
  rw [expand_shift hL]
  unfold expand shift
  have hdiv : i/L < m := (Nat.div_lt_iff_lt_mul hL).mpr (by simpa [Nat.mul_comm] using hi)
  rw [pack_shift _ _ _ (by omega)]

theorem expand_block {L : Nat} (hL : 0 < L) (code : Code) (w : Word) (s i : Nat)
    (hi : i < L) : expand L code w (s*L+i) = code (w s) i := by
  rw [expand_shift hL]
  simp [expand, shift, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi]

end CartesianTreeWords
