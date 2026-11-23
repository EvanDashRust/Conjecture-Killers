import Elimination
open Arxiv.«1601.03081»
namespace CrystalCampaign.StageTwo

/-- Both comparisons hold with the chosen ordering of the axes. -/
theorem orderedQuotients {n u r x y k l : ℕ} (hu : u<r) (hx : x<y)
    (h : Conditions n u r x y k l) :
    u*y+r*x<u*x+r*y ∧ k<l := by
  obtain ⟨d,ed⟩:=Nat.exists_eq_add_of_lt hu
  obtain ⟨e,ee⟩:=Nat.exists_eq_add_of_lt hx
  have st : u*y+r*x<u*x+r*y := by rw [ed,ee]; grind only
  refine ⟨st,?_⟩
  by_contra! bad
  have kp := h.k3
  have ineq := Nat.mul_lt_mul_of_pos_right st (show 0<k by omega)
  have le := Nat.mul_le_mul_left (u*y+r*x) bad
  have he:=h.firstEq
  have ht:=h.secondEq
  omega

private theorem gapIdentity {u r x y : ℕ} (hu : u≤r) (hx : x≤y) :
    (u*x+r*y)^2=(u*y+r*x)^2+(r^2-u^2)*(y^2-x^2) := by
  obtain ⟨d,ed⟩:=Nat.exists_eq_add_of_le hu
  obtain ⟨e,ee⟩:=Nat.exists_eq_add_of_le hx
  have C : r^2-u^2=2*u*d+d^2 := by
    rw [ed]
    have : (u+d)^2=u^2+(2*u*d+d^2) := by grind only
    omega
  have D : y^2-x^2=2*x*e+e^2 := by
    rw [ee]
    have : (x+e)^2=x^2+(2*x*e+e^2) := by grind only
    omega
  rw [C,D,ed,ee]
  grind only

/-- Distinct integer values of S/(k+1) force a product-independent gap test. -/
theorem separated {n u r x y : ℕ} (e : Exchange n u r x y) :
    n+1 < (r^2-u^2)*(y^2-x^2) := by
  obtain ⟨k,l,h⟩:=(conditions_iff e.ur e.xy).mp e
  obtain ⟨st,kl⟩:=orderedQuotients e.ur e.xy h
  let S:=u*x+r*y
  let T:=u*y+r*x
  change T<S at st
  obtain ⟨v,hv⟩:=h.firstDvd
  obtain ⟨w,hw⟩:=h.secondDvd
  change S=(k+1)*v at hv
  change T=(l+1)*w at hw
  have wv : w<v := by
    by_contra! bad
    have hh := Nat.mul_le_mul (show k+1≤l+1 by omega) bad
    omega
  have square (s q a : ℕ) (hs : s=(q+1)*a) (hp : n+1=s*q) : s^2=(n+1+s)*a := by
    rw [hp]
    calc
      _ = s*((q+1)*a) := by rw [← hs,pow_two]
      _ = _ := by grind only
  have vs := square S k v hv h.firstEq
  have wt := square T l w hw h.secondEq
  have a1:=Nat.mul_le_mul_left (n+1+S) (show w+1≤v by omega)
  have a2:=Nat.mul_le_mul_right w (show n+1+T≤n+1+S by omega)
  rw [Nat.mul_add,Nat.mul_one,← vs] at a1
  rw [← wt] at a2
  have g := gapIdentity e.ur.le e.xy.le
  change S^2=T^2+_ at g
  omega

/-- Excludes both axes up to the golden-ratio threshold, without a fixed parameter. -/
theorem noBalancedAxes {n u r x y : ℕ} (hr : r^2≤u^2+u*r) (hy : y^2≤x^2+x*y) :
    ¬Exchange n u r x y := by
  intro e
  have s:=separated e
  have p:=e.first.2.2.2.1
  have pn : n=(u*r)*(x*y) := by rw [p]; ac_rfl
  have a:=Nat.mul_le_mul (show r^2-u^2≤u*r by omega) (show y^2-x^2≤x*y by omega)
  omega

/-- Shifting the components of the two pairs by their respective quotients
gives two different products. It cannot by itself define a collision descent. -/
theorem distinctShiftProducts {n u r x y k l : ℕ} (hu : u<r) (hx : x<y)
    (h : Conditions n u r x y k l) : k^2-1<l^2-1 := by
  have v := Nat.pow_lt_pow_left (orderedQuotients hu hx h).2 (by decide : 2≠0)
  have kp := h.k3
  have le:=Nat.pow_le_pow_left kp 2
  omega

#print axioms orderedQuotients
#print axioms separated
#print axioms noBalancedAxes
#print axioms distinctShiftProducts
end CrystalCampaign.StageTwo
