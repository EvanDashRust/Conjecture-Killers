import Extremal
open Arxiv.«1601.03081»
namespace CrystalCampaign.StageTwo

private theorem copIndex (K : ℕ) : (K+1).Coprime (2*K+1) := by
  have dl:=Nat.gcd_dvd_left (K+1) (2*K+1)
  have dr:=Nat.gcd_dvd_right (K+1) (2*K+1)
  have hd:=dvd_mul_of_dvd_right dl 2
  rw [show 2*(K+1)=(2*K+1)+1 by omega] at hd
  exact Nat.dvd_one.mp ((Nat.dvd_add_iff_right dr).mpr hd)

private theorem positivePower {D p i : ℕ} (hp : p.Prime) (dn : 1<D) (dvd : D∣p^i) :
    ∃ t j : ℕ, t.Prime ∧ 0<j ∧ D=t^j := by
  obtain ⟨j,_,eq⟩:=(Nat.dvd_prime_pow hp).mp dvd
  cases j with
  | zero => simp at eq; omega
  | succ a => exact ⟨p,a+1,hp,by omega,eq⟩

/-- Every nontrivial divisor disjoint from another nontrivial divisor of P^i Q^j
is a prime power. No squarefreeness or positivity of i,j is needed. -/
private theorem supportedPower {D Z p q i j : ℕ} (hp : p.Prime) (hq : q.Prime)
    (dd : 1<D) (zz : 1<Z) (co : D.Coprime Z)
    (d : D∣p^i*q^j) (z : Z∣p^i*q^j) : ∃ t e : ℕ, t.Prime ∧ 0<e ∧ D=t^e := by
  let t:=Z.minFac
  have pt : t.Prime := Nat.minFac_prime (by omega)
  have tz : t∣Z := Nat.minFac_dvd _
  have td : ¬t∣D := fun hd => Nat.not_coprime_of_dvd_of_dvd pt.one_lt hd tz co
  rcases pt.dvd_mul.mp (tz.trans z) with one | two
  · have eqt:=(Nat.prime_dvd_prime_iff_eq pt hp).mp (pt.dvd_of_dvd_pow one)
    exact positivePower hq dd ((hp.coprime_pow_of_not_dvd (eqt ▸ td)).dvd_of_dvd_mul_left d)
  · have eqt:=(Nat.prime_dvd_prime_iff_eq pt hq).mp (pt.dvd_of_dvd_pow two)
    exact positivePower hp dd ((hq.coprime_pow_of_not_dvd (eqt ▸ td)).dvd_of_dvd_mul_right d)

private theorem sharedPrimeForcesOne {K t e : ℕ} (hp : t.Prime) (kp : 0<K)
    (eq : (K+2)*(2*K+1)=t^e) : K=1 := by
  have d1 : K+2∣t^e := eq ▸ dvd_mul_right ..
  have d2 : 2*K+1∣t^e := eq ▸ dvd_mul_left ..
  have primeOfPower (d : ℕ) (gt : 1<d) (dv : d∣t^e) : t∣d := by
    obtain ⟨j,_,ej⟩:=(Nat.dvd_prime_pow hp).mp dv
    cases j with
    | zero => simp at ej; omega
    | succ j => rw [ej,pow_succ]; exact dvd_mul_left ..
  have t1:=primeOfPower _ (by omega) d1
  have t2:=primeOfPower _ (by omega) d2
  have three (d : ℕ) (x : d∣K+2) (y : d∣2*K+1) : d∣3 := by
    apply (Nat.dvd_add_iff_right y).mpr
    rw [show 2*K+1+3=2*(K+2) by omega]
    exact dvd_mul_of_dvd_right x 2
  have tt := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3)).mp (three t t1 t2)
  subst t
  by_contra bad
  have nine (d : ℕ) (gt : 3<d) (dv : d∣3^e) : 9∣d := by
    obtain ⟨j,_,ej⟩:=(Nat.dvd_prime_pow (by decide : Nat.Prime 3)).mp dv
    cases j with
    | zero => simp at ej; omega
    | succ j =>
      cases j with
      | zero => norm_num at ej; omega
      | succ j => rw [ej,pow_succ,pow_succ]; exact ⟨3^j,by grind only⟩
  exact (by decide : ¬9∣3) (three 9 (nine _ (by omega) d1) (nine _ (by omega) d2))

/-- Complete classification on n+1=2 p^i q^j for arbitrary primes and exponents. -/
theorem only35OfTwoPrimeHalfSuccessor {n a b p q i j : ℕ} (hp : p.Prime) (hq : q.Prime)
    (ns : n+1=2*(p^i*q^j)) (c : IsCrystalWithComponents n a b) :
    n=35 ∧ ({a,b}:Finset ℕ)={5,7} := by
  obtain ⟨_,_,_,hn,k,⟨K,hk⟩,k3,eq,hd⟩:=(quotientCriterion ..).mp c
  subst k
  have kp : 0<K := by omega
  obtain ⟨w,hw⟩:=hd
  have parts : p^i*q^j=(K+1)*(2*K+1)*w := by
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0<2)
    calc
      _ = n+1 := ns.symm
      _ = _ := by rw [eq,hw]; grind only
  have d : K+1∣p^i*q^j := ⟨(2*K+1)*w,by rw [parts]; ac_rfl⟩
  have z : 2*K+1∣p^i*q^j := ⟨(K+1)*w,by rw [parts]; ac_rfl⟩
  obtain ⟨t,e,pt,ep,he⟩:=supportedPower hp hq (by omega) (by omega) (copIndex K) d z
  obtain ⟨s,v,f⟩:=halfOffsets c eq
  have ext:=primePowerExtremal f pt ep he
  have N : p^i*q^j=(K+1)*((K+2)*(2*K+1)) := by
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0<2)
    calc
      _ = n+1 := ns.symm
      _ = _ := by rw [ext]; unfold extremalProduct; grind only
  have next : (K+1).Coprime (K+2) := (neighboringCoprime (n:=K+1) (a:=K+2) (b:=K+1) (dvd_refl _) (dvd_refl _)).symm
  have cp : (K+1).Coprime ((K+2)*(2*K+1)) := Nat.coprime_mul_iff_right.mpr ⟨next,copIndex K⟩
  have zp : 1<(K+2)*(2*K+1) := lt_of_lt_of_le (by omega : 1<K+2) (Nat.le_mul_of_pos_right _ (by omega))
  obtain ⟨t',e',pt',_,he'⟩:=supportedPower hp hq zp (by omega) cp.symm
    (N ▸ dvd_mul_left ..) d
  have K1:=sharedPrimeForcesOne pt' kp he'
  subst K
  norm_num [extremalProduct] at ext
  rw [ext] at eq hn
  refine ⟨ext,equalSumProduct (show a+b=5+7 by omega) (show a*b=5*7 by omega)⟩

theorem twoPrimeHalfSuccessorClassification {n p q i j : ℕ} (hp : p.Prime) (hq : q.Prime)
    (ns : n+1=2*(p^i*q^j)) : (∃ a b : ℕ, IsCrystalWithComponents n a b) ↔ n=35 := by
  constructor
  · rintro ⟨a,b,c⟩
    exact (only35OfTwoPrimeHalfSuccessor hp hq ns c).1
  · rintro rfl
    exact ⟨5,7,isCrystalWithComponents_35_5_7⟩

theorem twoPrimeHalfSuccessorUniqueness {n a b c d p q i j : ℕ} (hp : p.Prime) (hq : q.Prime)
    (ns : n+1=2*(p^i*q^j)) (h1 : IsCrystalWithComponents n a b) (h2 : IsCrystalWithComponents n c d) :
    ({a,b}:Finset ℕ)={c,d} := (only35OfTwoPrimeHalfSuccessor hp hq ns h1).2.trans
      (only35OfTwoPrimeHalfSuccessor hp hq ns h2).2.symm

#print axioms only35OfTwoPrimeHalfSuccessor
#print axioms twoPrimeHalfSuccessorClassification
#print axioms twoPrimeHalfSuccessorUniqueness
end CrystalCampaign.StageTwo
