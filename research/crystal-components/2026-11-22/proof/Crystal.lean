import Upstream
import Mathlib.Data.Nat.Prime.Pow

open Arxiv.«1601.03081»

namespace CrystalCampaign

theorem original_iff (n a b : ℕ) : IsCrystalWithComponents n a b ↔
    Odd n ∧ 1 < a ∧ 1 < b ∧ n = a*b ∧ 2*(a+1)*(b+1) ∣ (a+b)^2+(a*b+1)^2 := Iff.rfl

theorem fixedProduct (n a b : ℕ) : IsCrystalWithComponents n a b ↔
    Odd n ∧ 1 < a ∧ 1 < b ∧ n = a*b ∧ n+1+(a+b) ∣ (n+1)^2 := by
  rw [isCrystalWithComponents_iff_mul_sq_dvd]
  have h : (a+1)*(b+1) = a*b+1+(a+b) := by grind
  rw [h]
  grind

/-- A Vieta step reduces the smaller positive coordinate and preserves the conic. -/
theorem conicStep (w x y : ℤ) (hx : 1 < x) (hxy : x ≤ y)
    (he : (x+y-1)^2 = w*x*y) :
    let z := w*x - 2*x + 2 - y
    0 < z ∧ z < x ∧ (z+x-1)^2 = w*z*x ∧ z+x-1 = w*x-(x+y-1) := by
  dsimp
  let z := w*x - 2*x + 2 - y
  have hprod : z*y = (x-1)^2 := by dsimp [z]; grind
  have hs : 0 < (x-1)^2 := by exact sq_pos_of_pos (by omega)
  have hz : 0 < z := by
    by_contra! hn
    have := mul_nonpos_of_nonpos_of_nonneg hn (show 0 ≤ y by omega)
    omega
  have hlt : z < x := by
    by_contra! hn
    have hm := mul_le_mul_of_nonneg_right hn (show 0 ≤ y by omega)
    have hm' := mul_le_mul_of_nonneg_left hxy (show 0 ≤ x by omega)
    grind
  refine ⟨hz, hlt, ?_, ?_⟩
  · grind
  · grind

/-- Descent propagates divisibility from the terminal coordinate x=1. -/
theorem conicDiv (w x y : ℤ) (hx : 0 < x) (hxy : x ≤ y)
    (he : (x+y-1)^2 = w*x*y) : w ∣ x+y-1 := by
  induction h : x.toNat using Nat.strong_induction_on generalizing x y with
  | h m ih =>
    by_cases hb : x = 1
    · subst x
      have hz : y*(y-w)=0 := by grind
      have hw : y=w := by rcases mul_eq_zero.mp hz with hh | hh <;> omega
      simp [hw]
    · let z := w*x - 2*x + 2 - y
      obtain ⟨hz, hlt, he', hsum⟩ := conicStep w x y (by omega) hxy he
      have hd : w ∣ z+x-1 := ih z.toNat (by dsimp [z]; omega) z x hz (by dsimp [z]; omega) he' rfl
      obtain ⟨q, hq⟩ := hd
      refine ⟨x-q, ?_⟩
      change z+x-1 = w*x-(x+y-1) at hsum
      grind

#print axioms original_iff
#print axioms fixedProduct
#print axioms conicStep
#print axioms conicDiv

/-- The conic divisibility invariant transported back to the upstream crystal predicate. -/
theorem indexFactorization {n a b : ℕ} (hc : IsCrystalWithComponents n a b) :
    ∃ w h : ℕ, 0 < w ∧ 2 ≤ h ∧ a+b = 2*w*h ∧ n+1 = (a+b)*(2*h-1) := by
  obtain ⟨hn, ha, hb, hnab, w, hw⟩ := (isCrystalWithComponents_iff_sum_sq_dvd n a b).mp hc
  have ho : Odd (a*b) := hnab ▸ hn
  obtain ⟨i, hi⟩ := Nat.Odd.of_mul_left ho
  have hor : Odd (b*a) := by simpa [Nat.mul_comm] using ho
  obtain ⟨j, hj⟩ := Nat.Odd.of_mul_left hor
  have hs : (i+j+1)^2 = w*((i+1)*(j+1)) := by grind
  have hwpos : 0 < w := by
    by_contra! hnw
    have : w = 0 := by omega
    simp [this] at hs
  have he : ((i:ℤ)+(j:ℤ)+1)^2 = (w:ℤ)*(((i:ℤ)+1)*((j:ℤ)+1)) := by exact_mod_cast hs
  have hd : (w:ℤ) ∣ (i:ℤ)+j+1 := by
    by_cases hle : i ≤ j
    · have z := conicDiv (w:ℤ) (i+1) (j+1) (by omega) (by omega) (by grind)
      convert z using 1; grind
    · have z := conicDiv (w:ℤ) (j+1) (i+1) (by omega) (by omega) (by grind)
      convert z using 1; grind
  have hd' : w ∣ i+j+1 := by exact_mod_cast hd
  obtain ⟨h, hh⟩ := hd'
  have hcancel : w*(w*h^2) = w*((i+1)*(j+1)) := by
    calc
      _ = (w*h)^2 := by grind
      _ = (i+j+1)^2 := by rw [hh]
      _ = _ := hs
  have hxy := Nat.eq_of_mul_eq_mul_left hwpos hcancel
  have hlow : 2 ≤ h := by
    by_contra! hlt
    have hcases : h = 0 ∨ h = 1 := by omega
    rcases hcases with h0 | h1
    · simp [h0] at hh
    · have hzero : i*j=0 := by grind
      rcases Nat.mul_eq_zero.mp hzero with iz | jz <;> omega
  refine ⟨w, h, hwpos, hlow, by grind, ?_⟩
  have htwo : 2*h-1+1 = 2*h := by omega
  have key : n+1+(a+b) = (a+b)*(2*h) := by grind
  rw [← htwo, Nat.mul_add, Nat.mul_one] at key
  omega

/-- For a fixed product it suffices to examine odd k with k(k+1) dividing n+1. -/
theorem quotientCriterion (n a b : ℕ) : IsCrystalWithComponents n a b ↔
    Odd n ∧ 1<a ∧ 1<b ∧ n=a*b ∧
    ∃ k : ℕ, Odd k ∧ 3≤k ∧ n+1=(a+b)*k ∧ k+1 ∣ a+b := by
  constructor
  · intro hc
    obtain ⟨w,h,_,hl,hs,ht⟩ := indexFactorization hc
    refine ⟨hc.1,hc.2.1,hc.2.2.1,hc.2.2.2.1,2*h-1,?_,by omega,ht,w,?_⟩
    · exact ⟨h-1,by omega⟩
    · have h2 : 2*h-1+1=2*h := by omega
      rw [h2]; grind
  · rintro ⟨hn,ha,hb,hp,k,_,_,ht,w,hw⟩
    apply (isCrystalWithComponents_iff_sum_sq_dvd n a b).mpr
    refine ⟨hn,ha,hb,hp,w,?_⟩
    have he : (a+1)*(b+1) = (a+b)*(k+1) := by grind
    calc
      _ = (a+b)*((k+1)*w) := by rw [← hw, pow_two]
      _ = _ := by rw [he]; grind

theorem componentsCoprime {n a b : ℕ} (hc : IsCrystalWithComponents n a b) :
    Nat.Coprime a b := by
  obtain ⟨_,_,_,hn,k,_,_,ht,_⟩ := (quotientCriterion n a b).mp hc
  have ga := Nat.gcd_dvd_left a b
  have gb := Nat.gcd_dvd_right a b
  have gsum := Nat.dvd_add ga gb
  have gt : a.gcd b ∣ n+1 := ht ▸ dvd_mul_of_dvd_left gsum k
  have gn : a.gcd b ∣ n := hn ▸ dvd_mul_of_dvd_left ga b
  exact Nat.dvd_one.mp ((Nat.dvd_add_iff_right gn).mpr gt)

#print axioms isCrystalWithComponents_iff_product_dvd
#print axioms isCrystalWithComponents_iff_sum_sq_dvd
#print axioms isCrystalWithComponents_iff_mul_sq_dvd
#print axioms indexFactorization
#print axioms quotientCriterion
#print axioms componentsCoprime

/-- A prime power dividing a coprime product lies entirely on one side. -/
theorem primePowerSide {a b p : ℕ} (e : ℕ) (hp : p.Prime) (hc : Nat.Coprime a b)
    (hd : p^e ∣ a*b) : p^e ∣ a ∨ p^e ∣ b := by
  by_cases ha : p ∣ a
  · have hn : ¬ p ∣ b := fun hb => Nat.not_coprime_of_dvd_of_dvd hp.one_lt ha hb hc
    exact Or.inl ((hp.coprime_pow_of_not_dvd hn).symm.dvd_of_dvd_mul_right hd)
  · exact Or.inr ((hp.coprime_pow_of_not_dvd ha).symm.dvd_of_dvd_mul_left hd)

/-- A proper nontrivial factor is too small to contain the whole product. -/
private theorem properSide {a b : ℕ} (ha : 0<a) (hb : 1<b) : ¬ a*b ∣ a := by
  intro hd
  have hle := Nat.le_of_dvd ha hd
  have hlt := Nat.mul_lt_mul_of_pos_left hb ha
  simp at hlt
  omega

private theorem matchBlocks {a b P Q : ℕ} (hP : 0<P) (hQ : 0<Q)
    (ha : 0<a) (hb : 0<b) (hprod : a*b=P*Q) (h1 : P ∣ a) (h2 : Q ∣ b) :
    a=P ∧ b=Q := by
  have hle := Nat.le_of_dvd ha h1
  have hle' := Nat.le_of_dvd hb h2
  have he : a=P := by
    by_contra! hne
    have hl := Nat.mul_lt_mul_of_pos_right (show P<a by omega) hQ
    have hu := Nat.mul_le_mul_left a hle'
    omega
  subst a
  exact ⟨rfl,Nat.eq_of_mul_eq_mul_left hP hprod⟩

theorem twoPrimeComponents {n a b p q : ℕ} (i j : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q) (hn : n=p^i*q^j)
    (hc : IsCrystalWithComponents n a b) : ({a,b} : Finset ℕ) = {p^i,q^j} := by
  have hab := componentsCoprime hc
  have ha := hc.2.1
  have hb := hc.2.2.1
  have hnab : a*b=p^i*q^j := hc.2.2.2.1.symm.trans hn
  have hd1 : p^i ∣ a*b := hnab ▸ dvd_mul_right _ _
  have hd2 : q^j ∣ a*b := hnab ▸ dvd_mul_left _ _
  have hPQ := Nat.coprime_pow_primes i j hp hq hpq
  have hP := Nat.pow_pos hp.pos (n := i)
  have hQ := Nat.pow_pos hq.pos (n := j)
  rcases primePowerSide i hp hab hd1 with pa | pb <;>
    rcases primePowerSide j hq hab hd2 with qa | qb
  · exact False.elim (properSide (by omega : 0<a) hb (hnab ▸ hPQ.mul_dvd_of_dvd_of_dvd pa qa))
  · obtain ⟨rfl,rfl⟩ := matchBlocks hP hQ (by omega) (by omega) hnab pa qb
    rfl
  · have hba : b*a=p^i*q^j := by rw [Nat.mul_comm b a,hnab]
    obtain ⟨rfl,rfl⟩ := matchBlocks hP hQ (by omega) (by omega) hba pb qa
    ext z; simp [or_comm]
  · have ht : b*a ∣ b := by simpa [Nat.mul_comm b a, hnab] using hPQ.mul_dvd_of_dvd_of_dvd pb qb
    exact False.elim (properSide (by omega : 0<b) ha ht)

/-- Original Finset conclusion for all two-prime-support products, with unrestricted exponents. -/
theorem twoPrimeUniqueness {n a b c d p q : ℕ} (i j : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q) (hn : n=p^i*q^j)
    (hab : IsCrystalWithComponents n a b) (hcd : IsCrystalWithComponents n c d) :
    ({a,b} : Finset ℕ) = {c,d} :=
  (twoPrimeComponents i j hp hq hpq hn hab).trans (twoPrimeComponents i j hp hq hpq hn hcd).symm

/-- The strictly nontrivial coprime blocks cannot split a prime power. -/
theorem noPrimePower {n a b p : ℕ} (e : ℕ) (hp : p.Prime) (hn : n=p^e) :
    ¬ IsCrystalWithComponents n a b := by
  intro hc
  have he : p^e = a*b := hn.symm.trans hc.2.2.2.1
  have hs := primePowerSide e hp (componentsCoprime hc) (he ▸ dvd_refl _)
  rw [he] at hs
  rcases hs with ha | hb
  · exact properSide (by have := hc.2.1; omega) hc.2.2.1 ha
  · rw [Nat.mul_comm] at hb
    exact properSide (by have := hc.2.2.1; omega) hc.2.1 hb

/-- The weakened integrality-and-coprimality test really admits two pairs. -/
theorem relaxedCollision :
    17765 = 55*323 ∧ 17765 = 95*187 ∧ Nat.Coprime 55 323 ∧ Nat.Coprime 95 187 ∧
    17766=(55+323)*47 ∧ 17766=(95+187)*63 ∧ ¬48 ∣ 55+323 ∧ ¬64 ∣ 95+187 := by decide

theorem example119 : IsCrystalWithComponents 119 7 17 := by
  exact ⟨⟨59,rfl⟩,by decide,by decide,rfl,by decide⟩

#print axioms primePowerSide
#print axioms twoPrimeComponents
#print axioms twoPrimeUniqueness
#print axioms noPrimePower
#print axioms relaxedCollision
#print axioms example119
#print axioms isCrystalWithComponents_35_5_7
/-- Natural-number square test. The witness u represents the integral half-difference
(s-r)/2 and enforces the parity, sign and nontriviality checks without truncated subtraction. -/
def Admissible (n k : ℕ) : Prop :=
  Odd n ∧ Odd k ∧ 3≤k ∧ ∃ s r u : ℕ,
    n+1=s*k ∧ k+1 ∣ s ∧ s^2=r^2+4*n ∧ s=2*u+r ∧ 1<u

theorem admissible_iff (n k : ℕ) : Admissible n k ↔
    ∃ a b : ℕ, IsCrystalWithComponents n a b ∧ n+1=(a+b)*k := by
  constructor
  · rintro ⟨hn,hk,hkl,s,r,u,ht,hs,hr,hpar,hu⟩
    have hprod : n=u*(u+r) := by grind
    have hsum : s=u+(u+r) := by omega
    rw [hsum] at ht hs
    exact ⟨u,u+r,(quotientCriterion ..).mpr ⟨hn,hu,by omega,hprod,k,hk,hkl,ht,hs⟩,ht⟩
  · rintro ⟨a,b,hc,ht⟩
    obtain ⟨hn,ha,hb,hp,j,hj,hjl,ht',hs⟩ := (quotientCriterion ..).mp hc
    have heq : j=k := Nat.eq_of_mul_eq_mul_left (by omega : 0 < a+b) (ht'.symm.trans ht)
    subst j
    refine ⟨hn,hj,hjl,a+b,?_⟩
    by_cases hab : a≤b
    · have hb' : b=a+(b-a) := by omega
      exact ⟨b-a,a,ht,hs,by grind,by omega,ha⟩
    · have ha' : a=b+(a-b) := by omega
      exact ⟨a-b,b,ht,hs,by grind,by omega,hb⟩

theorem equalSumProduct {a b c d : ℕ} (hs : a+b=c+d) (hp : a*b=c*d) :
    ({a,b} : Finset ℕ) = {c,d} := by
  have hz : ((a:ℤ)-c)*((a:ℤ)-d)=0 := by
    have hi : (a:ℤ)+b=(c:ℤ)+d := by exact_mod_cast hs
    have hj : (a:ℤ)*b=(c:ℤ)*d := by exact_mod_cast hp
    grind
  rcases mul_eq_zero.mp hz with h | h
  · have e : a=c := by omega
    have f : b=d := by omega
    rw [e,f]
  · have e : a=d := by omega
    have f : b=c := by omega
    rw [e,f]; ext v; simp [or_comm]

/-- Equivalence only. Neither universal proposition is assumed as an axiom or proved outright. -/
theorem uniqueness_iff_oneIndex :
    (∀ n a b c d : ℕ, IsCrystalWithComponents n a b → IsCrystalWithComponents n c d →
        ({a,b} : Finset ℕ) = {c,d}) ↔
    (∀ n k l : ℕ, Admissible n k → Admissible n l → k=l) := by
  constructor
  · intro h n k l hk hl
    obtain ⟨a,b,h1,hk'⟩ := (admissible_iff n k).mp hk
    obtain ⟨c,d,h2,hl'⟩ := (admissible_iff n l).mp hl
    have he := h n a b c d h1 h2
    have ha : a=c ∨ a=d := by
      have hh : a ∈ ({c,d} : Finset ℕ) := he ▸ (by simp : a ∈ ({a,b} : Finset ℕ))
      simpa using hh
    have hprod := h1.2.2.2.1.symm.trans h2.2.2.2.1
    have hpos := h1.2.1
    have hsum : a+b=c+d := by
      rcases ha with e | e
      · subst c
        have := Nat.eq_of_mul_eq_mul_left (by omega : 0<a) hprod
        omega
      · subst d
        rw [Nat.mul_comm c a] at hprod
        have := Nat.eq_of_mul_eq_mul_left (by omega : 0<a) hprod
        omega
    rw [← hsum] at hl'
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0<a+b) (hk'.symm.trans hl')
  · intro h n a b c d h1 h2
    obtain ⟨_,ha,_,hp,k,_,hk,ht,_⟩ := (quotientCriterion ..).mp h1
    obtain ⟨_,_,_,hp',l,_,_,ht',_⟩ := (quotientCriterion ..).mp h2
    have he := h n k l ((admissible_iff n k).mpr ⟨a,b,h1,ht⟩)
                       ((admissible_iff n l).mpr ⟨c,d,h2,ht'⟩)
    subst l
    exact equalSumProduct (Nat.eq_of_mul_eq_mul_right (by omega : 0<k) (ht.symm.trans ht')) (hp.symm.trans hp')

/-- Cubic size obstruction. Every single component must pass this inequality. -/
theorem componentSize {n a b : ℕ} (hc : IsCrystalWithComponents n a b) :
    2*(a+b)+1 ≤ a^2 := by
  obtain ⟨hn,ha,hb,hp,k,hk,_,ht,_⟩ := (quotientCriterion ..).mp hc
  obtain ⟨i,hi⟩ := Nat.Odd.of_mul_left (hp ▸ hn)
  obtain ⟨j,hj⟩ := hk
  have hid : (a+b)*a=a^2+n := by rw [hp]; grind only
  have hlt : k<a := by
    by_contra! hge
    have hle := Nat.mul_le_mul_left (a+b) hge
    have hsq : a ≤ a^2 := by simpa [pow_two] using Nat.mul_le_mul_left a (show 1≤a by omega)
    rw [hid,← ht] at hle
    omega
  have hgap : k+2≤a := by omega
  have hle := Nat.mul_le_mul_left (a+b) hgap
  rw [Nat.mul_add, ← ht, hid, Nat.mul_comm (a+b) 2] at hle
  omega

#print axioms admissible_iff
#print axioms equalSumProduct
#print axioms uniqueness_iff_oneIndex
#print axioms componentSize
/-- Two prime-power factors on the n+1 side are forced to involve different primes. -/
private theorem primeDvdNontrivial {m p e : ℕ} (hp : p.Prime) (hm : 1<m) (hd : m ∣ p^e) : p ∣ m := by
  obtain ⟨j,_,rfl⟩ := (Nat.dvd_prime_pow hp).mp hd
  cases j with
  | zero => simp at hm
  | succ i => exact ⟨p^i, by rw [pow_succ, Nat.mul_comm]⟩

theorem noDoublePrimePowerSuccessor {n a b p : ℕ} (e : ℕ) (hp : p.Prime)
    (hn : n+1=2*p^e) : ¬ IsCrystalWithComponents n a b := by
  intro hc
  obtain ⟨w,h,_,hh,hs,ht⟩ := indexFactorization hc
  let k := 2*h-1
  have hk : 1<k := by dsimp [k]; omega
  have htwo : 2*h=k+1 := by dsimp [k]; omega
  have hfact : p^e=w*h*k := by
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0<2)
    change 2*p^e=2*(w*h*(2*h-1))
    rw [← hn,ht,hs]; grind only
  have h1 : h ∣ p^e := ⟨w*k,by rw [hfact]; grind only⟩
  have h2 : k ∣ p^e := ⟨w*h,by rw [hfact]; grind only⟩
  have pa := primeDvdNontrivial hp hh h1
  have pb := primeDvdNontrivial hp hk h2
  have pt : p ∣ k+1 := htwo ▸ dvd_mul_of_dvd_right pa 2
  exact hp.not_dvd_one ((Nat.dvd_add_iff_right pb).mpr pt)

theorem swap {n a b : ℕ} (hc : IsCrystalWithComponents n a b) : IsCrystalWithComponents n b a := by
  obtain ⟨hn,ha,hb,hp,hd⟩ := (fixedProduct ..).mp hc
  apply (fixedProduct ..).mpr
  exact ⟨hn,hb,ha,by simpa [Nat.mul_comm] using hp,by simpa [Nat.add_comm b a] using hd⟩

/-- Orient a three-block split by putting R on the second side. If the two singleton
alternatives fail the component-size test, only {P*Q,R} can occur. -/
private theorem threeOriented {n a b P Q R : ℕ} (hc : IsCrystalWithComponents n a b)
    (hn : n=P*Q*R) (hP : 0<P) (hQ : 0<Q) (hR : 0<R)
    (cPQ : Nat.Coprime P Q) (cPR : Nat.Coprime P R) (cQR : Nat.Coprime Q R)
    (pSide : P∣a ∨ P∣b) (qSide : Q∣a ∨ Q∣b) (rSide : R∣b)
    (pSmall : P^2 ≤ 2*(P+Q*R)) (qSmall : Q^2 ≤ 2*(Q+P*R)) : a=P*Q ∧ b=R := by
  have ha := hc.2.1
  have hb := hc.2.2.1
  have tp := hc.2.2.2.1.symm.trans hn
  have sz := componentSize hc
  rcases pSide with pa | pb <;> rcases qSide with qa | qb
  · exact matchBlocks (Nat.mul_pos hP hQ) hR (by omega) (by omega) tp
      (cPQ.mul_dvd_of_dvd_of_dvd pa qa) rSide
  · have he : a*b=P*(Q*R) := by rw [tp,Nat.mul_assoc]
    obtain ⟨e,f⟩ := matchBlocks hP (Nat.mul_pos hQ hR) (by omega) (by omega) he pa
      (cQR.mul_dvd_of_dvd_of_dvd qb rSide)
    rw [e,f] at sz
    omega
  · have he : a*b=Q*(P*R) := by rw [tp]; grind only
    obtain ⟨e,f⟩ := matchBlocks hQ (Nat.mul_pos hP hR) (by omega) (by omega) he qa
      (cPR.mul_dvd_of_dvd_of_dvd pb rSide)
    rw [e,f] at sz
    omega
  · have allD : P*Q*R ∣ b := (cPR.mul_left cQR).mul_dvd_of_dvd_of_dvd
        (cPQ.mul_dvd_of_dvd_of_dvd pb qb) rSide
    have hd : b*a ∣ b := by rw [Nat.mul_comm b a,tp]; exact allD
    exact False.elim (properSide (by omega : 0<b) ha hd)

theorem threePrimeComponents {n a b p q r : ℕ} (i j k : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (pq : p≠q) (pr : p≠r) (qr : q≠r)
    (hn : n=p^i*q^j*r^k)
    (hsizeP : (p^i)^2 ≤ 2*(p^i+q^j*r^k)) (hsizeQ : (q^j)^2 ≤ 2*(q^j+p^i*r^k))
    (hc : IsCrystalWithComponents n a b) : ({a,b} : Finset ℕ) = {p^i*q^j,r^k} := by
  have hab := componentsCoprime hc
  have tp := hc.2.2.2.1.symm.trans hn
  have pd : p^i ∣ a*b := ⟨q^j*r^k,by rw [tp,Nat.mul_assoc]⟩
  have qd : q^j ∣ a*b := ⟨p^i*r^k,by rw [tp]; grind only⟩
  have rd : r^k ∣ a*b := ⟨p^i*q^j,by rw [tp,Nat.mul_comm (r^k)]⟩
  have ps := primePowerSide i hp hab pd
  have qs := primePowerSide j hq hab qd
  have cPQ := Nat.coprime_pow_primes i j hp hq pq
  have cPR := Nat.coprime_pow_primes i k hp hr pr
  have cQR := Nat.coprime_pow_primes j k hq hr qr
  rcases primePowerSide k hr hab rd with ra | rb
  · obtain ⟨e,f⟩ := threeOriented (swap hc) hn (Nat.pow_pos hp.pos) (Nat.pow_pos hq.pos)
        (Nat.pow_pos hr.pos) cPQ cPR cQR ps.symm qs.symm ra hsizeP hsizeQ
    rw [e,f]; ext z; simp [or_comm]
  · obtain ⟨e,f⟩ := threeOriented hc hn (Nat.pow_pos hp.pos) (Nat.pow_pos hq.pos)
        (Nat.pow_pos hr.pos) cPQ cPR cQR ps qs rb hsizeP hsizeQ
    rw [e,f]

#print axioms noDoublePrimePowerSuccessor
#print axioms swap
#print axioms threePrimeComponents
theorem threePrimeUniqueness {n a b c d p q r : ℕ} (i j k : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (pq : p≠q) (pr : p≠r) (qr : q≠r)
    (hn : n=p^i*q^j*r^k)
    (hsizeP : (p^i)^2 ≤ 2*(p^i+q^j*r^k)) (hsizeQ : (q^j)^2 ≤ 2*(q^j+p^i*r^k))
    (hab : IsCrystalWithComponents n a b) (hcd : IsCrystalWithComponents n c d) :
    ({a,b} : Finset ℕ) = {c,d} :=
  (threePrimeComponents i j k hp hq hr pq pr qr hn hsizeP hsizeQ hab).trans
    (threePrimeComponents i j k hp hq hr pq pr qr hn hsizeP hsizeQ hcd).symm

theorem example1455 : IsCrystalWithComponents 1455 15 97 := by
  exact ⟨⟨727,rfl⟩,by decide,by decide,rfl,by decide⟩

#print axioms threePrimeUniqueness
#print axioms example1455
/-- No two crystal decompositions can exchange a factor of 3, even for composite x,y. -/
theorem noExchangeThree {n x y : ℕ} (h1 : IsCrystalWithComponents n x (3*y))
    (h2 : IsCrystalWithComponents n y (3*x)) : False := by
  obtain ⟨hn,hx,_,hn1,k,hk,_,hkEq,_⟩ := (quotientCriterion ..).mp h1
  obtain ⟨_,hy,_,_,l,hl,_,hlEq,_⟩ := (quotientCriterion ..).mp h2
  let S := x+3*y
  let T := y+3*x
  let g := S.gcd T
  change n+1 = S*k at hkEq
  change n+1 = T*l at hlEq
  have gs : g ∣ S := Nat.gcd_dvd_left .. 
  have gt : g ∣ T := Nat.gcd_dvd_right ..
  have gsN : g ∣ n+1 := hkEq ▸ dvd_mul_of_dvd_left gs _
  have gx : g.Coprime x := by
    have dN := (Nat.gcd_dvd_left g x).trans gsN
    have dn : g.gcd x ∣ n := hn1 ▸ dvd_mul_of_dvd_left (Nat.gcd_dvd_right g x) _
    exact Nat.dvd_one.mp ((Nat.dvd_add_iff_right dn).mpr dN)
  have id1 : 3*T = S+8*x := by dsimp [S,T]; grind only
  have g8x : g ∣ 8*x := (Nat.dvd_add_iff_right gs).mpr (id1 ▸ dvd_mul_of_dvd_right gt 3)
  have g8 := gx.dvd_of_dvd_mul_right g8x
  have hS : S ∣ n+1 := ⟨k,hkEq⟩
  have hT : T ∣ n+1 := ⟨l,hlEq⟩
  have L := Nat.le_of_dvd (Nat.succ_pos n) (Nat.lcm_dvd hS hT)
  have gg : g * S.lcm T = S*T := Nat.gcd_mul_lcm ..
  have hst : 4*(n+1)<S*T := by
    have hxy : 1<x*y := lt_of_lt_of_le hx (by simpa using Nat.mul_le_mul_left x (show 1≤y by omega))
    have hn' : n=3*(x*y) := by rw [hn1]; grind only
    have h16 : 16*(x*y) ≤ S*T := by
      by_cases h : x≤y
      · have he : S*T=16*(x*y)+3*(y-x)^2 := by
          have : y=x+(y-x) := by omega
          dsimp [S,T]; grind only
        omega
      · have he : S*T=16*(x*y)+3*(x-y)^2 := by
          have : x=y+(x-y) := by omega
          dsimp [S,T]; grind only
        omega
    rw [hn']; omega
  have h4 : 4<g := by
    by_contra! hle
    have ha := Nat.mul_le_mul_right (S.lcm T) hle
    rw [gg] at ha
    omega
  obtain ⟨z,hz⟩ := g8
  have ge : g=8 := by
    by_cases hh : z≥2
    · have hh' := Nat.mul_le_mul_left g hh
      omega
    · have : z=0 ∨ z=1 := by omega
      rcases this with hh | hh <;> simp_all
  obtain ⟨A,hA⟩ := gs
  obtain ⟨B,hB⟩ := gt
  rw [ge] at hA hB
  have heq : A*k=B*l := by
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0<8)
    rw [← Nat.mul_assoc, ← Nat.mul_assoc, ← hA, ← hB]
    exact hkEq.symm.trans hlEq
  have hm := congrArg (fun v : ℕ => v%2) heq
  change A*k%2 = B*l%2 at hm
  rw [Nat.mul_mod,Nat.mul_mod B, Nat.odd_iff.mp hk,Nat.odd_iff.mp hl] at hm
  simp at hm
  have ox := Nat.Odd.of_mul_left (hn1 ▸ hn)
  obtain ⟨v,hv⟩ := ox
  omega

#print axioms noExchangeThree
/-- All positive-exponent products with full prime-power blocks 3, p^i and q^j
have unique crystal components. The implication also covers zero exponents. -/
theorem singleThreeUniqueness {n a b c d p q : ℕ} (i j : ℕ)
    (hp : p.Prime) (hq : q.Prime) (pq : p≠q) (p3 : p≠3) (q3 : q≠3)
    (hn : n=3*p^i*q^j)
    (h1 : IsCrystalWithComponents n a b) (h2 : IsCrystalWithComponents n c d) :
    ({a,b} : Finset ℕ) = {c,d} := by
  let P := p^i
  let Q := q^j
  have posP : 0<P := Nat.pow_pos hp.pos
  have posQ : 0<Q := Nat.pow_pos hq.pos
  have t3 : Nat.Prime 3 := by decide
  have cpq : Nat.Coprime P Q := Nat.coprime_pow_primes i j hp hq pq
  have cp3 : Nat.Coprime P 3 := ((Nat.coprime_primes hp t3).mpr p3).pow_left i
  have cq3 : Nat.Coprime Q 3 := ((Nat.coprime_primes hq t3).mpr q3).pow_left j
  change n=3*P*Q at hn
  have oriented (x y : ℕ) (hc : IsCrystalWithComponents n x y) (hy3 : 3∣y) :
      (x=P ∧ y=3*Q) ∨ (x=Q ∧ y=3*P) := by
    have hx := hc.2.1
    have hy := hc.2.2.1
    have tp := hc.2.2.2.1.symm.trans hn
    have co := componentsCoprime hc
    have pd : P∣x*y := ⟨3*Q,by rw [tp]; grind only⟩
    have qd : Q∣x*y := ⟨3*P,by rw [tp]; grind only⟩
    rcases primePowerSide i hp co pd with px | py <;> rcases primePowerSide j hq co qd with qx | qy
    · have he : x*y=(P*Q)*3 := by rw [tp]; grind only
      obtain ⟨_,f⟩ := matchBlocks (Nat.mul_pos posP posQ) (by decide : 0<3)
        (by omega) (by omega) he (cpq.mul_dvd_of_dvd_of_dvd px qx) hy3
      have hh := componentSize (swap hc)
      rw [f] at hh; omega
    · exact Or.inl (matchBlocks posP (Nat.mul_pos (by decide : 0<3) posQ) (by omega) (by omega)
        (by rw [tp]; grind only) px (cq3.symm.mul_dvd_of_dvd_of_dvd hy3 qy))
    · exact Or.inr (matchBlocks posQ (Nat.mul_pos (by decide : 0<3) posP) (by omega) (by omega)
        (by rw [tp]; grind only) qx (cp3.symm.mul_dvd_of_dvd_of_dvd hy3 py))
    · have hd : 3*P*Q∣y := (cq3.symm.mul_left cpq).mul_dvd_of_dvd_of_dvd
          (cp3.symm.mul_dvd_of_dvd_of_dvd hy3 py) qy
      have hbad : y*x ∣ y := by rw [Nat.mul_comm y x,tp]; exact hd
      exact False.elim (properSide (by omega : 0<y) hx hbad)
  have classify (x y : ℕ) (hc : IsCrystalWithComponents n x y) :
      (({x,y}:Finset ℕ)={P,3*Q} ∧ IsCrystalWithComponents n P (3*Q)) ∨
      (({x,y}:Finset ℕ)={Q,3*P} ∧ IsCrystalWithComponents n Q (3*P)) := by
    have hd : 3∣x*y := ⟨P*Q,by rw [← hc.2.2.2.1,hn,Nat.mul_assoc]⟩
    rcases t3.dvd_or_dvd hd with h3x | h3y
    · rcases oriented y x (swap hc) h3x with ⟨e,f⟩ | ⟨e,f⟩
      · refine Or.inl ⟨?_,by simpa [e,f] using swap hc⟩
        rw [e,f]; ext z; simp [or_comm]
      · refine Or.inr ⟨?_,by simpa [e,f] using swap hc⟩
        rw [e,f]; ext z; simp [or_comm]
    · rcases oriented x y hc h3y with ⟨e,f⟩ | ⟨e,f⟩
      · exact Or.inl ⟨by rw [e,f],by simpa [e,f] using hc⟩
      · exact Or.inr ⟨by rw [e,f],by simpa [e,f] using hc⟩
  rcases classify a b h1 with ⟨e,he⟩ | ⟨e,he⟩ <;> rcases classify c d h2 with ⟨f,hf⟩ | ⟨f,hf⟩
  · exact e.trans f.symm
  · exact False.elim (noExchangeThree he hf)
  · exact False.elim (noExchangeThree hf he)
  · exact e.trans f.symm

#print axioms singleThreeUniqueness
end CrystalCampaign
