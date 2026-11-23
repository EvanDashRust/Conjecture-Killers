import Cells
open Arxiv.«1601.03081»
namespace CrystalCampaign.StageTwo

def SupportedBy (n p q s : ℕ) : Prop :=
  ∀ v : ℕ, v.Prime → v ∣ n → v=p ∨ v=q ∨ v=s

theorem supportedOfProduct {n p q s : ℕ} (i j k : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hs : s.Prime) (hn : n=p^i*q^j*s^k) : SupportedBy n p q s := by
  intro v hv hd; rw [hn] at hd
  rcases hv.dvd_or_dvd hd with h | h
  · rcases hv.dvd_or_dvd h with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hv hp).mp (hv.dvd_of_dvd_pow h))
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hv hq).mp (hv.dvd_of_dvd_pow h)))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hv hs).mp (hv.dvd_of_dvd_pow h)))

theorem cellsDivide {n u r x y : ℕ} (e : Exchange n u r x y) :
    u ∣ n ∧ r ∣ n ∧ x ∣ n ∧ y ∣ n := by
  have hp:=e.first.2.2.2.1
  exact ⟨⟨x*r*y,by rw [hp]; ac_rfl⟩,⟨u*x*y,by rw [hp]; ac_rfl⟩,
    ⟨u*r*y,by rw [hp]; ac_rfl⟩,⟨u*r*x,by rw [hp]; ac_rfl⟩⟩

private theorem disjointPrimes {p q a b : ℕ} (co : a.Coprime b) (hp : p.Prime)
    (ha : p∣a) (hb : q∣b) : p≠q := by
  intro e; subst q; exact Nat.not_coprime_of_dvd_of_dvd hp.one_lt ha hb co

private theorem forbidFour {n p q s i j k l : ℕ} (sp : SupportedBy n p q s)
    (hi : i.Prime) (hj : j.Prime) (hk : k.Prime) (hl : l.Prime)
    (ii : i∣n) (jj : j∣n) (kk : k∣n) (ll : l∣n)
    (ij : i≠j) (ik : i≠k) (il : i≠l) (jk : j≠k) (jl : j≠l) (kl : k≠l) : False := by
  have h1:=sp i hi ii
  have h2:=sp j hj jj
  have h3:=sp k hk kk
  have h4:=sp l hl ll
  grind only

theorem unitCell {n u r x y p q s : ℕ} (sp : SupportedBy n p q s) (e : Exchange n u r x y) :
    u=1 ∨ x=1 := by
  by_contra! h
  obtain ⟨up,_,xp,_,_,_,_,_,ur,ux,uy,rx,ry,xy⟩:=cellProperties e
  have rp:=e.ur
  have yp:=e.xy
  have A:=Nat.minFac_prime h.1
  have B:=Nat.minFac_prime (show r≠1 by omega)
  have C:=Nat.minFac_prime h.2
  have D:=Nat.minFac_prime (show y≠1 by omega)
  obtain ⟨du,dr,dx,dy⟩:=cellsDivide e
  have a:=Nat.minFac_dvd u
  have b:=Nat.minFac_dvd r
  have c:=Nat.minFac_dvd x
  have d:=Nat.minFac_dvd y
  exact forbidFour sp A B C D (a.trans du) (b.trans dr) (c.trans dx) (d.trans dy)
    (disjointPrimes ur A a b) (disjointPrimes ux A a c) (disjointPrimes uy A a d)
    (disjointPrimes rx B b c) (disjointPrimes ry B b d) (disjointPrimes xy C c d)

private theorem primePowerOfSupport (p : ℕ) (hp : p.Prime) (n : ℕ) (hn : 0<n)
    (hs : ∀ q : ℕ, q.Prime → q∣n → q=p) : ∃ i : ℕ, n=p^i := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h1 : n=1
    · exact ⟨0,by simpa using h1⟩
    have eq:=hs _ (Nat.minFac_prime h1) (Nat.minFac_dvd n)
    have hd : p∣n := eq ▸ Nat.minFac_dvd n
    obtain ⟨v,hv⟩ := hd
    have vp : 0<v := by
      by_contra! hz
      have vz : v=0 := by omega
      simp [vz] at hv
      omega
    have small : v<n := by
      have := Nat.mul_lt_mul_of_pos_right hp.one_lt vp
      simpa [hv] using this
    obtain ⟨i,hi⟩:=ih v small vp (fun q hq hqv => hs q hq (hqv.trans ⟨p,by rw [hv]; ac_rfl⟩))
    exact ⟨i+1,by rw [hv,hi,pow_succ,Nat.mul_comm]⟩

theorem singleBlockPrimePower {n r x y p q s : ℕ} (sp : SupportedBy n p q s)
    (e : Exchange n 1 r x y) : ∃ t i : ℕ, t.Prime ∧ 0<i ∧ r=t^i := by
  obtain ⟨_,rp,_,_,_,_,_,_,_,_,_,rx,ry,xy⟩:=cellProperties e
  obtain ⟨_,dr,dx,dy⟩:=cellsDivide e
  have hxr : 1<x := by simpa using e.first.2.1
  have hyr : x<y:=e.xy
  have hrr : 1<r:=e.ur
  have pp:=Nat.minFac_prime (show r≠1 by omega)
  have px:=Nat.minFac_prime (show x≠1 by omega)
  have py:=Nat.minFac_prime (show y≠1 by omega)
  have fr:=Nat.minFac_dvd r
  have fx:=Nat.minFac_dvd x
  have fy:=Nat.minFac_dvd y
  have unique (v : ℕ) (pv : v.Prime) (dv : v∣r) : v=r.minFac := by
    by_contra h
    exact forbidFour sp pv pp px py (dv.trans dr) (fr.trans dr) (fx.trans dx) (fy.trans dy)
      h (disjointPrimes rx pv dv fx) (disjointPrimes ry pv dv fy)
      (disjointPrimes rx pp fr fx) (disjointPrimes ry pp fr fy) (disjointPrimes xy px fx fy)
  obtain ⟨i,hi⟩:=primePowerOfSupport r.minFac pp r rp unique
  refine ⟨_,i,pp,?_,hi⟩
  by_contra! hz
  have iz : i=0 := by omega
  simp [iz] at hi
  omega

/-- The same two unordered pairs, after transposing if necessary, share a single prime-power
exchange parameter. Positive exponents are obtained even from an at-most-three support assumption. -/
theorem threeSupportReduction {n a b c d p q s : ℕ} (sp : SupportedBy n p q s)
    (h1 : IsCrystalWithComponents n a b) (h2 : IsCrystalWithComponents n c d)
    (hne : ({a,b}:Finset ℕ)≠{c,d}) :
    ∃ r x y t i : ℕ, Exchange n 1 r x y ∧ t.Prime ∧ 0<i ∧ r=t^i ∧
      Family a b c d=Family x (r*y) y (r*x) := by
  obtain ⟨u,r,x,y,e,eq⟩:=normalize h1 h2 hne
  rcases unitCell sp e with hu | hx
  · subst u
    obtain ⟨t,i,pt,ip,hi⟩:=singleBlockPrimePower sp e
    exact ⟨r,x,y,t,i,e,pt,ip,hi,by simpa using eq⟩
  · subst x
    have et : Exchange n 1 y u r := ⟨e.xy,e.ur,by simpa [Nat.mul_comm] using e.first,
       by simpa [Nat.mul_comm] using swap e.second⟩
    obtain ⟨t,i,pt,ip,hi⟩:=singleBlockPrimePower sp et
    exact ⟨y,u,r,t,i,et,pt,ip,hi,by simpa [Family,Nat.mul_comm,Finset.pair_comm] using eq⟩

theorem threePrimeUniquenessOfSinglePrimePower
    (exclude : ∀ n t i x y : ℕ, t.Prime → 0<i → ¬ Exchange n 1 (t^i) x y)
    {n a b c d p q s : ℕ} (i j k : ℕ) (hp : p.Prime) (hq : q.Prime) (hs : s.Prime)
    (hn : n=p^i*q^j*s^k) (h1 : IsCrystalWithComponents n a b) (h2 : IsCrystalWithComponents n c d) :
    ({a,b}:Finset ℕ)={c,d} := by
  by_contra h
  obtain ⟨r,x,y,t,v,e,pt,hv,he,_⟩:=threeSupportReduction (supportedOfProduct i j k hp hq hs hn) h1 h2 h
  exact exclude n t v x y pt hv (he ▸ e)

#print axioms supportedOfProduct
#print axioms unitCell
#print axioms singleBlockPrimePower
#print axioms threeSupportReduction
#print axioms threePrimeUniquenessOfSinglePrimePower
end CrystalCampaign.StageTwo
