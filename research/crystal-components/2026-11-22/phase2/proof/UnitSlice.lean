import Elimination
import Mathlib.Data.Nat.ModEq
open Arxiv.«1601.03081»
namespace CrystalCampaign.StageTwo

/-- The determinant deficit on a unit axis is an odd integer at least three. -/
theorem unitDeficit {n R x y k l g m A B c : ℕ} (f : Fiber n 1 R x y k l g m A B c) :
    m*c+3≤R := by
  have e:=(conditions_iff f.gap f.spread).mpr ⟨k,l,f.conditions⟩
  obtain ⟨_,rp,xp,yp,_,oR,_⟩:=cellProperties e
  have hx : 1<x := by simpa using f.conditions.proper.1
  have xy : 1<x*y := lt_of_lt_of_le hx (Nat.le_mul_of_pos_right x yp)
  obtain ⟨d,ed⟩:=Nat.exists_eq_add_of_le f.spread.le
  have ident : (x+R*y)*(y+R*x)=(R+1)*(R*x*y)+(R+1)*(x*y)+R*d^2 := by
    rw [ed]; grind only
  have pn : n=R*x*y := by simpa using f.conditions.product
  have comp : (R+1)*(n+1)<(x+R*y)*(y+R*x) := by
    have larger:=Nat.mul_lt_mul_of_pos_left xy (show 0<R+1 by omega)
    rw [ident,pn,Nat.mul_add,Nat.mul_one]
    simp only [Nat.mul_one] at larger
    omega
  have s : x+R*y=g*A := by simpa using f.sumA
  have t : y+R*x=g*B := by simpa using f.sumB
  rw [fiberProduct f,s,t] at comp
  have gBig : (R+1)*m<g := Nat.lt_of_mul_lt_mul_right (show ((R+1)*m)*(g*A*B)<g*(g*A*B) by
    convert comp using 1 <;> ac_rfl)
  have v:=Nat.mul_lt_mul_of_pos_right gBig f.cPos
  have det : g*c+1=R^2 := by simpa using f.det
  have i1 : (R+1)*(m*c+1)=(R+1)*m*c+(R+1) := by grind only
  have i2 : (R+1)*R=R^2+R := by grind only
  have less := Nat.lt_of_mul_lt_mul_left (show (R+1)*(m*c+1)<(R+1)*R by omega)
  obtain ⟨j,hj⟩:=f.evenC
  obtain ⟨w,hw⟩:=oR
  have mc : m*c=m*j+m*j := by rw [hj]; grind only
  omega

/-- A second-order congruence for every R, with the unique least residue specified. -/
theorem unitResidue {n R x y k l g m A B c : ℕ} (f : Fiber n 1 R x y k l g m A B c) :
    (k*l) % R^2 = R-m*c := by
  let h:=R-m*c
  have lim:=unitDeficit f
  have hh : h+m*c=R := Nat.sub_add_cancel (by omega)
  have det : g*c+1=R^2 := by simpa using f.det
  have co:=fiberConic f
  change (1*R)^2*(A^2+B^2)+c^2*(m*g*A*B)=(1*R)*((R^2+1^2)*(A*B))+c^2 at co
  simp only [one_mul,one_pow] at co
  have eqn : R^2*(k^2+l^2)+(m*c)*(g*c)*(k*l)=R*(R^2+1)*(k*l)+(m*c)^2 := by
    rw [f.kEq,f.lEq]
    calc
      _ = m^2*(R^2*(A^2+B^2)+c^2*(m*g*A*B)) := by grind only
      _ = _ := by rw [co]; grind only
  have zi : (R:ℤ)^2*((k:ℤ)^2+l^2)+((m:ℤ)*c)*((g:ℤ)*c)*(k*l)=
      R*(R^2+1)*(k*l)+(m*c)^2 := by exact_mod_cast eqn
  have hd : (g:ℤ)*c+1=(R:ℤ)^2 := by exact_mod_cast det
  have hm : (h:ℤ)+(m:ℤ)*c=R := by exact_mod_cast hh
  have zz : ((R:ℤ)+m*c)*(k*l)-((R:ℤ)+m*c)*h =
      (R:ℤ)^2*((k:ℤ)^2+l^2-((h:ℤ)*k*l+1)) := by
    rw [show (g:ℤ)*c=R^2-1 by omega,show (m:ℤ)*c=R-h by omega] at zi
    rw [show (m:ℤ)*c=R-h by omega]
    grind only
  have md : Nat.ModEq (R^2) ((R+m*c)*h) ((R+m*c)*(k*l)) := by
    apply Nat.modEq_iff_dvd.mpr
    refine ⟨(k:ℤ)^2+l^2-((h:ℤ)*k*l+1),?_⟩
    push_cast
    exact zz
  have ax:=axialCoprime f
  simp only [one_mul] at ax
  have cr : R.Coprime (m*c) := Nat.coprime_mul_iff_right.mpr ⟨ax.2,ax.1⟩
  have addcop : R.Coprime (R+m*c) := by
    have d1:=Nat.gcd_dvd_left R (R+m*c)
    have d2:=Nat.gcd_dvd_right R (R+m*c)
    exact (cr.coprime_dvd_left d1).eq_one_of_dvd ((Nat.dvd_add_iff_right d1).mpr d2)
  have md' := (Nat.ModEq.cancel_left_of_coprime (addcop.pow_left 2) md).symm
  have pos:=Nat.mul_pos f.mPos f.cPos
  have le : R≤R^2 := by rw [pow_two]; exact Nat.le_mul_of_pos_right R (by omega)
  have small : h<R^2 := by omega
  change (k*l)%R^2=h%R^2 at md'
  exact md'.trans (Nat.mod_eq_of_lt small)

theorem fivePrimitiveSlice {n x y k l g m A B c : ℕ} (f : Fiber n 1 5 x y k l g m A B c) :
    m=1 ∧ c=2 ∧ g=12 := by
  have bound:=unitDeficit f
  have cp:=f.cPos
  have mp:=f.mPos
  obtain ⟨v,hv⟩:=f.evenC
  have cmin : 2≤c := by omega
  have lm := Nat.mul_le_mul_left m cmin
  have mm : m=1 := by omega
  have det:=f.det
  simp [mm] at bound
  obtain rfl : c=2 := by omega
  norm_num at det
  exact ⟨mm,rfl,by omega⟩

#print axioms unitDeficit
#print axioms unitResidue
#print axioms fivePrimitiveSlice
end CrystalCampaign.StageTwo
