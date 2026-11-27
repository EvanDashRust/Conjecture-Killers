import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

namespace Selfridge

/-- A finite indexed system of distinct odd congruence classes covering all integers. -/
def OddCover {ι : Type} [Finite ι] (m : ι → Nat) (r : ι → Int) : Prop :=
  Function.Injective m ∧
  (∀ i, 1 < m i ∧ Odd (m i)) ∧
  (∀ x : Int, ∃ i, x ≡ r i [ZMOD (m i : Int)])

/-- Close a single residual class modulo M using q distinct divisors of M.
The correction uses only moduli q*d and keeps the original classes. -/
theorem close_residual_class {ι : Type} [Finite ι] {q M : Nat} {a : Int}
    (q_gt : 1 < q) (q_odd : Odd q) (M_odd : Odd M) (cop : q.Coprime M)
    (m : ι → Nat) (r : ι → Int) (inj : Function.Injective m)
    (valid : ∀ i, 1 < m i ∧ Odd (m i))
    (fresh : ∀ i, ¬ q ∣ m i)
    (near_cover : ∀ x : Int, (∃ i, x ≡ r i [ZMOD (m i : Int)]) ∨ x ≡ a [ZMOD (M : Int)])
    (d : Fin q → Nat) (d_inj : Function.Injective d) (d_dvd : ∀ j, d j ∣ M) :
    ∃ m' : ι ⊕ Fin q → Nat, ∃ r' : ι ⊕ Fin q → Int,
      (∀ i, m' (.inl i) = m i ∧ r' (.inl i) = r i) ∧
      (∀ j, m' (.inr j) = q * d j) ∧ OddCover m' r' := by
  have d_odd (j : Fin q) : Odd (d j) := Odd.of_dvd_nat M_odd (d_dvd j)
  have co (j : Fin q) : q.Coprime (d j) := cop.coprime_dvd_right (d_dvd j)
  let crt (j : Fin q) := Nat.chineseRemainder (co j) j.val (a % (d j : Int)).toNat
  let m' : ι ⊕ Fin q → Nat := Sum.elim m fun j => q * d j
  let r' : ι ⊕ Fin q → Int := Sum.elim r fun j => ((crt j).val : Int)
  refine ⟨m', r', fun _ => ⟨rfl, rfl⟩, fun _ => rfl, ?_, ?_, ?_⟩
  · intro u v heq
    cases u with
    | inl i =>
      cases v with
      | inl k => exact congrArg Sum.inl (inj heq)
      | inr j => exact (fresh i ⟨d j, heq⟩).elim
    | inr j =>
      cases v with
      | inl i => exact (fresh i ⟨d j, heq.symm⟩).elim
      | inr k =>
        change q * d j = q * d k at heq
        exact congrArg Sum.inr (d_inj (Nat.eq_of_mul_eq_mul_left (by omega) heq))
  · intro u
    cases u with
    | inl i => exact valid i
    | inr j =>
      have dp : 0 < d j := (d_odd j).pos
      exact ⟨lt_of_lt_of_le q_gt (Nat.le_mul_of_pos_right q dp), q_odd.mul (d_odd j)⟩
  · intro x
    rcases near_cover x with ⟨i, hi⟩ | hx
    · exact ⟨.inl i, hi⟩
    · have qpos : (0 : Int) < q := by omega
      have xnonneg := Int.emod_nonneg x qpos.ne'
      let j : Fin q := ⟨(x % (q : Int)).toNat, by
        have := Int.emod_lt_of_pos x qpos
        omega⟩
      have xj : x ≡ (j.val : Int) [ZMOD (q : Int)] := by
        change x ≡ (((x % (q : Int)).toNat : Nat) : Int) [ZMOD (q : Int)]
        rw [Int.toNat_of_nonneg xnonneg]
        exact (Int.mod_modEq x q).symm
      have xd : x ≡ a [ZMOD (d j : Int)] := hx.of_dvd (by exact_mod_cast d_dvd j)
      have dp : (0 : Int) < d j := by exact_mod_cast (d_odd j).pos
      have jr : ((crt j).val : Int) ≡ (j.val : Int) [ZMOD (q : Int)] :=
        Int.natCast_modEq_iff.mpr (crt j).prop.1
      have ar : ((crt j).val : Int) ≡ a [ZMOD (d j : Int)] := by
        have h := Int.natCast_modEq_iff.mpr (crt j).prop.2
        rw [Int.toNat_of_nonneg (Int.emod_nonneg a dp.ne')] at h
        exact h.trans (Int.mod_modEq a (d j))
      have hm := (Int.modEq_and_modEq_iff_modEq_mul (by simpa using co j)).mp
        ⟨xj.trans jr.symm, xd.trans ar.symm⟩
      exact ⟨.inr j, by simpa [m', r'] using hm⟩

#print axioms close_residual_class
end Selfridge
