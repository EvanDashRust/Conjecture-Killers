import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

namespace Selfridge

/-- A residue in a fixed prefix that leaves by depth L has a first nonzero exit digit. -/
theorem first_nonzero_exit {p x r : Int} {h L : Nat}
    (pp : 1 < p) (hp : x ≡ r [ZMOD p^h]) (hL : ¬ x ≡ r [ZMOD p^L]) :
    ∃ k : Nat, ∃ digit : Int, h ≤ k ∧ k < L ∧
      0 < digit ∧ digit < p ∧ x ≡ r + p^k * digit [ZMOD p^(k+1)] := by
  let fails (j : Nat) : Prop := ¬ x ≡ r [ZMOD p^j]
  have exists_failure : ∃ j, fails j := ⟨L, hL⟩
  let j := Nat.find exists_failure
  have failure : fails j := Nat.find_spec exists_failure
  have jl : j ≤ L := Nat.find_min' exists_failure hL
  have hj : h < j := by
    by_contra hlarge
    exact failure (hp.of_dvd (pow_dvd_pow p (by omega)))
  let k := j - 1
  have kj : k + 1 = j := by omega
  have kmin : x ≡ r [ZMOD p^k] := by
    by_contra hn
    have jne : j ≤ k := Nat.find_min' exists_failure hn
    omega
  obtain ⟨t, ht⟩ := kmin.symm.dvd
  let d := t % p
  have dp : d < p := Int.emod_lt_of_pos t (by omega)
  have dn : 0 ≤ d := Int.emod_nonneg t (by omega)
  have d_ne : d ≠ 0 := by
    intro hd
    have hpt : p ∣ t := Int.dvd_iff_emod_eq_zero.2 hd
    obtain ⟨v,hv⟩ := hpt
    have hdiv : p ^ j ∣ x-r := by
      refine ⟨v, ?_⟩
      rw [← kj, pow_succ, ht, hv, mul_assoc]
    exact failure (Int.modEq_of_dvd hdiv).symm
  refine ⟨k, d, by omega, by omega, by omega, dp, ?_⟩
  have htd : t ≡ d [ZMOD p] := (Int.mod_modEq t p).symm
  have hc : r + p^k*t ≡ r + p^k*d [ZMOD p^k*p] :=
    (htd.mul_left' (c:=p^k)).add_left r
  have re : r + p^k*t = x := by omega
  rwa [pow_succ, ← re]

#print axioms first_nonzero_exit
end Selfridge
