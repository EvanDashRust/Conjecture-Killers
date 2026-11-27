import LocalExit
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.ChineseRemainder

namespace Selfridge.Prefix

inductive Mode
  | free
  | fixed (e : ℕ) (a : ℤ)
  | variable (r d : ℤ)

abbrev Pattern (n : ℕ) := Fin n → Mode

def hits (p r d : ℤ) : Mode → Prop
  | .free => True
  | .fixed e a => r ≡ a [ZMOD p^e]
  | .variable root digit => r = root ∧ d = digit

def wellFormed (h : ℕ) : Mode → Prop
  | .free => True
  | .fixed e _ => 0 < e ∧ e ≤ h
  | .variable _ _ => True

def lifted (p : ℤ) (h : ℕ) (L : ℤ → ℕ) (x : ℤ) (k : ℕ) : Mode → Prop
  | .free => True
  | .fixed e a => x ≡ a [ZMOD p^e]
  | .variable r d => h ≤ k ∧ k < L r ∧ x ≡ r + p^k*d [ZMOD p^(k+1)]

/-- A single auxiliary modulus serves every root.  Its resource at a root
and a nonzero auxiliary residue is the selected core exponent. -/
def auxiliaryHit {n : ℕ} (p : Fin n → ℤ) (q : ℤ) (h : Fin n → ℕ)
    (allocate : Fin n → ℤ → ℤ → ℕ) (x : ℤ) : Prop :=
  x ≡ 0 [ZMOD q] ∨ ∃ i r j, 0 ≤ r ∧ r < p i ^ h i ∧ 0 < j ∧ j < q ∧
      x ≡ j [ZMOD q] ∧ x ≡ r [ZMOD p i ^ allocate i r j]

/-- Integer coverage in conjunction-of-congruences form.  CRT identifies
each realized conjunction with one ordinary residue class. -/
theorem single_auxiliary_lift {n : ℕ} (p : Fin n → ℤ) (hp : ∀ i, 1 < p i)
    (q : ℤ) (hq : 1 < q) (h : Fin n → ℕ)
    (allocate : Fin n → ℤ → ℤ → ℕ) (L : Fin n → ℤ → ℕ)
    (bound : ∀ i r j, 0 ≤ r → r < p i ^ h i → 0 < j → j < q → allocate i r j ≤ L i r)
    (patterns : Finset (Pattern n))
    (well : ∀ t ∈ patterns, ∀ i, wellFormed (h i) (t i))
    (cover : ∀ r d : Fin n → ℤ,
      (∀ i, 0 ≤ r i ∧ r i < p i ^ h i ∧ 0 < d i ∧ d i < p i) →
      ∃ t ∈ patterns, ∀ i, hits (p i) (r i) (d i) (t i))
    (x : ℤ) :
    auxiliaryHit p q h allocate x ∨
      ∃ t ∈ patterns, ∃ k : Fin n → ℕ, ∀ i, lifted (p i) (h i) (L i) x (k i) (t i) := by
  classical
  by_cases hit : auxiliaryHit p q h allocate x
  · exact Or.inl hit
  right
  let j := x % q
  have jq : x ≡ j [ZMOD q] := (Int.mod_modEq x q).symm
  have j0 : 0 < j := by
    have hj : 0 ≤ j := Int.emod_nonneg x (by omega)
    by_contra! bad
    exact hit (Or.inl ((show j = 0 by omega) ▸ jq))
  have jlt : j < q := Int.emod_lt_of_pos x (by omega)
  let r (i : Fin n) := x % (p i ^ h i)
  have roots (i : Fin n) : 0 ≤ r i ∧ r i < p i ^ h i := by
    have hpi := hp i
    have pos : 0 < p i ^ h i := pow_pos (by omega) _
    exact ⟨Int.emod_nonneg _ (ne_of_gt pos), Int.emod_lt_of_pos _ pos⟩
  have rootEq (i : Fin n) : x ≡ r i [ZMOD p i ^ h i] := (Int.mod_modEq _ _).symm
  have exits (i : Fin n) : ∃ k : ℕ, ∃ d : ℤ, h i ≤ k ∧ k < L i (r i) ∧
      0 < d ∧ d < p i ∧ x ≡ r i + p i ^ k * d [ZMOD p i ^ (k+1)] := by
    apply Selfridge.first_nonzero_exit (hp i) (rootEq i)
    intro hx
    apply hit
    right
    refine ⟨i, r i, j, (roots i).1, (roots i).2, j0, jlt, jq, ?_⟩
    exact hx.of_dvd (pow_dvd_pow _ (bound i (r i) j (roots i).1 (roots i).2 j0 jlt))
  choose k d spec using exits
  obtain ⟨t, ht, matchAt⟩ := cover r d (fun i => ⟨(roots i).1, (roots i).2, (spec i).2.2.1, (spec i).2.2.2.1⟩)
  refine ⟨t, ht, k, fun i => ?_⟩
  have good := well t ht i
  have hitAt := matchAt i
  cases e : t i with
  | free => trivial
  | fixed depth phase =>
    simp only [e, wellFormed] at good
    simp only [e, hits] at hitAt
    exact ((rootEq i).of_dvd (pow_dvd_pow _ good.2)).trans hitAt
  | «variable» root digit =>
    simp only [e, hits] at hitAt
    rcases hitAt with ⟨hr, hd⟩
    exact hr ▸ hd ▸ ⟨(spec i).1, (spec i).2.1, (spec i).2.2.2.2⟩

/-- A positive exponent no greater than the height is a fixed mode.
All larger exponents designate a variable mode. Zero designates a free mode. -/
def decodeMode (h e : ℕ) := min e (h+1)

theorem decode_fixed {h e : ℕ} (le : e ≤ h) : decodeMode h e = e := by
  unfold decodeMode
  omega

theorem decode_variable {h k : ℕ} (le : h ≤ k) : decodeMode h (k+1) = h+1 := by
  unfold decodeMode
  omega

theorem exponentVector_unique {a b : ℕ →₀ ℕ}
    (ha : ∀ p ∈ a.support, Nat.Prime p) (hb : ∀ p ∈ b.support, Nat.Prime p)
    (eq : a.prod (· ^ ·) = b.prod (· ^ ·)) : a = b := by
  simpa only [Nat.factorization_prod_pow_eq_self ha, Nat.factorization_prod_pow_eq_self hb] using
    congrArg Nat.factorization eq

/-- Any terminal rectangle works with q-1 divisor labels of its CRT period.
The last statement gives exactly the two congruences defining its selected class. -/
theorem terminal_divisor_gadget {q m x r : ℤ} (hq : 1 < q)
    (D : ℤ → ℤ) (divisor : ∀ j, 0 < j → j < q → D j ∣ m)
    (hx : x ≡ r [ZMOD m]) :
    x ≡ 0 [ZMOD q] ∨ ∃ j, 0 < j ∧ j < q ∧ x ≡ j [ZMOD q] ∧ x ≡ r [ZMOD D j] := by
  let j := x % q
  have jj : x ≡ j [ZMOD q] := (Int.mod_modEq _ _).symm
  have lo : 0 ≤ j := Int.emod_nonneg _ (by omega)
  have hi : j < q := Int.emod_lt_of_pos _ (by omega)
  by_cases h0 : j = 0
  · exact Or.inl (h0 ▸ jj)
  · exact Or.inr ⟨j, by omega, hi, jj, hx.of_dvd (divisor j (by omega) hi)⟩

/-- Prime exponent extraction for a product over labelled, distinct prime coordinates. -/
theorem core_exponent {n : ℕ} {P : Fin n → ℕ}
    (hP : ∀ i, Nat.Prime (P i)) (inj : Function.Injective P) (v : Fin n → ℕ)
    (i : Fin n) : (∏ j, P j ^ v j).factorization (P i) = v i := by
  rw [Nat.factorization_prod_apply (fun j _ => pow_ne_zero _ (hP j).ne_zero)]
  rw [Finset.sum_eq_single i]
  · exact Nat.factorization_pow_self (hP i)
  · intro j _ ne
    rw [(hP j).factorization_pow, Finsupp.single_eq_of_ne]
    exact fun h => ne (inj h.symm)
  · simp

def copyExponent (k : ℕ) : Mode → ℕ
  | .free => 0
  | .fixed e _ => e
  | .variable _ _ => k+1

def shape (h : ℕ) : Mode → ℕ
  | .free => 0
  | .fixed e _ => e
  | .variable _ _ => h+1

def legalCopy (h k : ℕ) : Mode → Prop
  | .free => k = 0
  | .fixed e _ => k = 0 ∧ 0 < e ∧ e ≤ h
  | .variable _ _ => h ≤ k

theorem decode_copy {h k : ℕ} (m : Mode) (ok : legalCopy h k m) :
    decodeMode h (copyExponent k m) = shape h m := by
  cases m with
  | free => simp [copyExponent, decodeMode, shape]
  | fixed e a => exact decode_fixed ok.2.2
  | «variable» r d => exact decode_variable ok

/-- Two enumerated core copies with equal numerical moduli are identical
if their patterns have distinct mode vectors and inactive copy indices are zero. -/
theorem core_copy_unique {n : ℕ} {P : Fin n → ℕ} (hP : ∀ i, Nat.Prime (P i))
    (inj : Function.Injective P) (h : Fin n → ℕ) (S : Set (Pattern n))
    (labels : ∀ t ∈ S, ∀ u ∈ S, (∀ i, shape (h i) (t i) = shape (h i) (u i)) → t = u)
    {t u : Pattern n} (ht : t ∈ S) (hu : u ∈ S) {k l : Fin n → ℕ}
    (tk : ∀ i, legalCopy (h i) (k i) (t i)) (ul : ∀ i, legalCopy (h i) (l i) (u i))
    (eq : (∏ i, P i ^ copyExponent (k i) (t i)) = ∏ i, P i ^ copyExponent (l i) (u i)) :
    t = u ∧ k = l := by
  have ex (i) : copyExponent (k i) (t i) = copyExponent (l i) (u i) := by
    simpa only [core_exponent hP inj] using congrArg (fun z : ℕ => z.factorization (P i)) eq
  have tu := labels t ht u hu (fun i => (decode_copy _ (tk i)).symm.trans
    ((congrArg (decodeMode (h i)) (ex i)).trans (decode_copy _ (ul i))))
  subst u
  refine ⟨rfl, funext (fun i => ?_)⟩
  have a := tk i
  have b := ul i
  have c := ex i
  cases d : t i <;> simp only [d, legalCopy, copyExponent, Nat.succ.injEq] at a b c <;> omega

/-- CRT transfers an actual cover to every choice of fixed roots. -/
theorem ordinary_cover_to_roots {n : ℕ} (P h : Fin n → ℕ)
    (hp : ∀ i, 0 < P i) (co : ∀ i j, i ≠ j → (P i).Coprime (P j))
    (S : Finset ℕ) (phase : ℕ → ℕ) (expo : ℕ → Fin n → ℕ)
    (bounds : ∀ m ∈ S, ∀ i, expo m i ≤ h i)
    (parts : ∀ m ∈ S, ∀ i, P i ^ expo m i ∣ m)
    (cover : ∀ x : ℕ, ∃ m ∈ S, x ≡ phase m [MOD m]) (r : Fin n → ℕ) :
    ∃ m ∈ S, ∀ i, r i ≡ phase m [MOD P i ^ expo m i] := by
  classical
  let x := Nat.chineseRemainderOfFinset r (fun i => P i ^ h i) Finset.univ
    (fun i _ => (pow_pos (hp i) _).ne') (fun i _ j _ ij => ((co i j ij).pow_left _).pow_right _)
  obtain ⟨m, hm, hc⟩ := cover x.val
  refine ⟨m, hm, fun i => ?_⟩
  exact (((x.property i (Finset.mem_univ i)).of_dvd (pow_dvd_pow _ (bounds m hm i))).symm).trans
    (hc.of_dvd (parts m hm i))

#print axioms core_exponent
#print axioms core_copy_unique
#print axioms ordinary_cover_to_roots
#print axioms single_auxiliary_lift
#print axioms decode_fixed
#print axioms decode_variable
#print axioms exponentVector_unique
#print axioms terminal_divisor_gadget
end Selfridge.Prefix
