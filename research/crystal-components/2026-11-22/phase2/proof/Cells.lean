import Transfer
open Arxiv.«1601.03081»
namespace CrystalCampaign.StageTwo

def Family (a b c d : ℕ) : Finset (Finset ℕ) :=
  {({a,b} : Finset ℕ),({c,d} : Finset ℕ)}

/-- Ordered axes; one cell may equal 1. The two original admissibility predicates
carry all factor-domain, product and integrality conditions. -/
structure Exchange (n u r x y : ℕ) : Prop where
  ur : u<r
  xy : x<y
  first : IsCrystalWithComponents n (u*x) (r*y)
  second : IsCrystalWithComponents n (u*y) (r*x)

theorem cellProperties {n u r x y : ℕ} (e : Exchange n u r x y) :
    0<u ∧ 0<r ∧ 0<x ∧ 0<y ∧ Odd u ∧ Odd r ∧ Odd x ∧ Odd y ∧
    u.Coprime r ∧ u.Coprime x ∧ u.Coprime y ∧ r.Coprime x ∧ r.Coprime y ∧ x.Coprime y := by
  have h := e.first
  have hab : Odd ((u*x)*(r*y)) := h.2.2.2.1 ▸ h.1
  have hl := Nat.Odd.of_mul_left hab
  have hr := Nat.Odd.of_mul_right hab
  have h1 := componentsCoprime e.first
  have h2 := componentsCoprime e.second
  simp only [Nat.coprime_mul_iff_left,Nat.coprime_mul_iff_right] at h1 h2
  have ou := Nat.Odd.of_mul_left hl
  have ox := Nat.Odd.of_mul_right hl
  have orr := Nat.Odd.of_mul_left hr
  have oy := Nat.Odd.of_mul_right hr
  have pos (z : ℕ) (o : Odd z) : 0<z := by obtain ⟨i,hi⟩ := o; omega
  exact ⟨pos _ ou,pos _ orr,pos _ ox,pos _ oy,ou,orr,ox,oy,
      h1.1.1,h2.2.1,h1.2.1,h1.1.2.symm,h2.1.2.symm,h1.2.2⟩

structure Conditions (n u r x y k l : ℕ) : Prop where
  product : n=u*r*x*y
  oddN : Odd n
  proper : 1<u*x ∧ 1<r*y ∧ 1<u*y ∧ 1<r*x
  oddK : Odd k
  oddL : Odd l
  k3 : 3≤k
  l3 : 3≤l
  firstEq : n+1=(u*x+r*y)*k
  secondEq : n+1=(u*y+r*x)*l
  firstDvd : k+1 ∣ u*x+r*y
  secondDvd : l+1 ∣ u*y+r*x

theorem conditions_iff {n u r x y : ℕ} (hu : u<r) (hx : x<y) :
    Exchange n u r x y ↔ ∃ k l, Conditions n u r x y k l := by
  constructor
  · intro e
    obtain ⟨hn,ha,hb,hp,k,hk,hk3,ht,hs⟩ := (quotientCriterion ..).mp e.first
    obtain ⟨_,hc,hd,_,l,hl,hl3,ht',hs'⟩ := (quotientCriterion ..).mp e.second
    exact ⟨k,l,⟨by rw [hp]; ac_rfl,hn,⟨ha,hb,hc,hd⟩,hk,hl,hk3,hl3,ht,ht',hs,hs'⟩⟩
  · rintro ⟨k,l,h⟩
    exact ⟨hu,hx,(quotientCriterion ..).mpr ⟨h.oddN,h.proper.1,h.proper.2.1,by rw [h.product]; ac_rfl,
      k,h.oddK,h.k3,h.firstEq,h.firstDvd⟩,
      (quotientCriterion ..).mpr ⟨h.oddN,h.proper.2.2.1,h.proper.2.2.2,by rw [h.product]; ac_rfl,
      l,h.oddL,h.l3,h.secondEq,h.secondDvd⟩⟩

private theorem orient {n u r x y : ℕ} (h1 : IsCrystalWithComponents n (u*x) (r*y))
    (h2 : IsCrystalWithComponents n (u*y) (r*x)) (hnur : u≠r) (hnxy : x≠y) :
    ∃ U R X Y, Exchange n U R X Y ∧
      Family (u*x) (r*y) (u*y) (r*x) = Family (U*X) (R*Y) (U*Y) (R*X) := by
  by_cases hur : u<r <;> by_cases hxy : x<y
  · exact ⟨u,r,x,y,⟨hur,hxy,h1,h2⟩,rfl⟩
  · exact ⟨u,r,y,x,⟨hur,by omega,h2,h1⟩, by simp [Family,Finset.pair_comm]⟩
  · exact ⟨r,u,x,y,⟨by omega,hxy,swap h2,swap h1⟩, by simp [Family,Finset.pair_comm]⟩
  · exact ⟨r,u,y,x,⟨by omega,by omega,swap h1,swap h2⟩, by simp [Family,Finset.pair_comm]⟩

/-- Construct the four cells from two given pairs, and preserve the entire unordered family. -/
theorem normalize {n a b c d : ℕ} (h1 : IsCrystalWithComponents n a b)
    (h2 : IsCrystalWithComponents n c d) (hne : ({a,b}:Finset ℕ)≠{c,d}) :
    ∃ u r x y, Exchange n u r x y ∧ Family a b c d=Family (u*x) (r*y) (u*y) (r*x) := by
  let u:=a.gcd c
  have up : 0<u := Nat.gcd_pos_of_pos_left _ (by have:=h1.2.1; omega)
  obtain ⟨x,hx⟩ := Nat.gcd_dvd_left a c
  obtain ⟨y,hy⟩ := Nat.gcd_dvd_right a c
  change a=u*x at hx
  change c=u*y at hy
  have hcop : x.Coprime y := by
    have hh : u=u*(x.gcd y) := by
      change a.gcd c = _; conv_lhs => rw [hx,hy,Nat.gcd_mul_left]
    exact Nat.eq_of_mul_eq_mul_left up (show u*x.gcd y = u*1 by simpa using hh.symm)
  have equiv := h1.2.2.2.1.symm.trans h2.2.2.2.1
  have hb : x*b=y*d := by
    apply Nat.eq_of_mul_eq_mul_left up
    simpa only [hx,hy,Nat.mul_assoc] using equiv
  have dy : y ∣ x*b := ⟨d,hb⟩
  obtain ⟨r,hr⟩ := hcop.symm.dvd_of_dvd_mul_left dy
  have yp : 0<y := by
    by_contra! hh
    have : y=0 := by omega
    have hc := h2.2.1
    simp [this] at hy; omega
  have hd : d=r*x := by
    apply Nat.eq_of_mul_eq_mul_left yp
    rw [← hb,hr]; ac_rfl
  have hr' : b=r*y := hr.trans (Nat.mul_comm ..)
  rw [hx,hr',hy,hd] at hne ⊢
  rw [hx,hr'] at h1
  rw [hy,hd] at h2
  have une : u≠r := by
    intro he; apply hne; rw [he,Finset.pair_comm]
  have xne : x≠y := by intro he; apply hne; rw [he]
  exact orient h1 h2 une xne

theorem exchangeDistinct {n u r x y : ℕ} (e : Exchange n u r x y) :
    ({u*x,r*y}:Finset ℕ)≠{u*y,r*x} := by
  obtain ⟨up,_,xp,_⟩ := cellProperties e
  have hxy:=Nat.mul_lt_mul_of_pos_left e.xy up
  have hur:=Nat.mul_lt_mul_of_pos_right e.ur xp
  intro he
  have h : u*x ∈ ({u*y,r*x}:Finset ℕ) := he ▸ (by simp : u*x ∈ ({u*x,r*y}:Finset ℕ))
  simp only [Finset.mem_insert,Finset.mem_singleton] at h
  omega

theorem original_iff_noExchange :
    (∀ n a b c d : ℕ, IsCrystalWithComponents n a b → IsCrystalWithComponents n c d →
      ({a,b}:Finset ℕ)={c,d}) ↔ (∀ n u r x y : ℕ, ¬ Exchange n u r x y) := by
  constructor
  · intro h n u r x y e; exact exchangeDistinct e (h n _ _ _ _ e.first e.second)
  · intro h n a b c d h1 h2; by_contra hneq
    obtain ⟨u,r,x,y,e,_⟩:=normalize h1 h2 hneq
    exact h n u r x y e

#print axioms cellProperties
#print axioms conditions_iff
#print axioms normalize
#print axioms exchangeDistinct
#print axioms original_iff_noExchange
end CrystalCampaign.StageTwo
