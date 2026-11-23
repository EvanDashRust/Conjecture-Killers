import UnitSlice
open Arxiv.«1601.03081»
namespace CrystalCampaign.StageTwo

theorem componentOffset {a b k : ℕ} (ha : 1<a) (ok : Odd k) (oa : Odd a)
    (eqn : a*b+1=(a+b)*k) : ∃ d : ℕ, 0<d ∧ a=k+2*d := by
  have small : k<a := by
    by_contra! h
    have hm:=Nat.mul_le_mul_left (a+b) h
    have aa : a≤a*a := by simpa using Nat.mul_le_mul_left a ha.le
    rw [show (a+b)*a=a*a+a*b by grind only,← eqn] at hm
    omega
  obtain ⟨s,hs⟩:=oa
  obtain ⟨t,ht⟩:=ok
  exact ⟨s-t,by omega,by omega⟩

private theorem crossIdentity (U R X Y k l E h : ℤ) (hh : h+E=U*R)
    (ix : E*X+U*l=R*k) (iy : E*Y+U*k=R*l)
    (hp : (U*X+R*Y)*k=U*R*X*Y+1) :
    U^2*(k*l)=h+R^2*((U*X-k)*(U*Y-l)) := by
  have sum : U*(X*k+Y*l)=h*(X*Y)+1 := by
    have e1:=congrArg (fun i:ℤ => Y*i) ix
    have e2:=congrArg (fun i:ℤ => i*(X*Y)) hh
    grind only
  have rx : R*(U*X-k)=h*X-U*l := by
    have hh':=congrArg (fun i:ℤ => i*X) hh
    grind only
  have ry : R*(U*Y-l)=h*Y-U*k := by
    have hh':=congrArg (fun i:ℤ => i*Y) hh
    grind only
  symm
  calc
    _ = h+(R*(U*X-k))*(R*(U*Y-l)) := by grind only
    _ = h+(h*X-U*l)*(h*Y-U*k) := by rw [rx,ry]
    _ = U^2*(k*l)+h*(1+h*(X*Y)-U*(X*k+Y*l)) := by grind only
    _ = _ := by rw [sum]; grind only

/-- The exact lifts use all four positive half-differences. Both lifts are multiples
of four before any search or parameter bound. -/
theorem shiftedFactors {n u r x y k l g m A B c : ℕ} (f : Fiber n u r x y k l g m A B c) :
    ∃ p q s v : ℕ, 0<p ∧ 0<q ∧ 0<s ∧ 0<v ∧
      u*x=k+2*p ∧ u*y=l+2*q ∧ r*y=k+2*s ∧ r*x=l+2*v ∧
      u^2*(k*l)=(u*r-m*c)+r^2*(4*p*q) ∧ r^2*(k*l)=(u*r+m*c)+u^2*(4*s*v) ∧
      4*p*s+1=k^2 ∧ 4*q*v+1=l^2 := by
  have e:=(conditions_iff f.gap f.spread).mpr ⟨k,l,f.conditions⟩
  obtain ⟨_,_,_,_,ou,orr,ox,oy,_⟩:=cellProperties e
  have hk : (u*x)*(r*y)+1=(u*x+r*y)*k := e.first.2.2.2.1 ▸ f.conditions.firstEq
  have hl : (u*y)*(r*x)+1=(u*y+r*x)*l := e.second.2.2.2.1 ▸ f.conditions.secondEq
  obtain ⟨p,pp,ep⟩:=componentOffset f.conditions.proper.1 f.conditions.oddK (ou.mul ox) hk
  obtain ⟨q,qp,eq⟩:=componentOffset f.conditions.proper.2.2.1 f.conditions.oddL (ou.mul oy) hl
  obtain ⟨s,sp,es⟩:=componentOffset f.conditions.proper.2.1 f.conditions.oddK (orr.mul oy) (by simpa [Nat.add_comm,Nat.mul_comm] using hk)
  obtain ⟨v,vp,ev⟩:=componentOffset f.conditions.proper.2.2.2 f.conditions.oddL (orr.mul ox) (by simpa [Nat.add_comm,Nat.mul_comm] using hl)
  have ix : (m*c)*x+u*l=r*k := by
    rw [f.lEq,f.kEq]
    calc
      _ = m*(c*x+u*A) := by grind only
      _ = _ := by rw [f.invX]; ac_rfl
  have iy : (m*c)*y+u*k=r*l := by
    rw [f.lEq,f.kEq]
    calc
      _ = m*(c*y+u*B) := by grind only
      _ = _ := by rw [f.invY]; ac_rfl
  let E:ℤ:=(m:ℤ)*c
  let h:=u*r-m*c
  let H:=u*r+m*c
  have xi : E*x+(u:ℤ)*l=(r:ℤ)*k := by dsimp [E]; exact_mod_cast ix
  have yi : E*y+(u:ℤ)*k=(r:ℤ)*l := by dsimp [E]; exact_mod_cast iy
  have dh : (h:ℤ)+E=(u:ℤ)*r := by dsimp [E]; exact_mod_cast (Nat.sub_add_cancel (positiveDeterminant f).le : h+m*c=u*r)
  have dH : (H:ℤ)+(-E)=(r:ℤ)*u := by dsimp [H,E]; grind only
  have prod : ((u:ℤ)*x+r*y)*k=(u:ℤ)*r*x*y+1 := by
    exact_mod_cast (f.conditions.product ▸ f.conditions.firstEq.symm)
  have a1:=crossIdentity u r x y k l E h dh xi yi prod
  have prod' : ((r:ℤ)*y+u*x)*k=(r:ℤ)*u*y*x+1 := by convert prod using 1 <;> ac_rfl
  have a2:=crossIdentity r u y x k l (-E) H dH (by rw [neg_mul]; omega) (by rw [neg_mul]; omega) prod'
  have lift (a b t d : ℕ) (he : a*b=t+2*d) : (a:ℤ)*b-t=2*d := by
    have hi : (a:ℤ)*b=(t:ℤ)+2*d := by exact_mod_cast he
    omega
  rw [lift _ _ _ _ ep,lift _ _ _ _ eq] at a1
  rw [lift _ _ _ _ es,lift _ _ _ _ ev] at a2
  have group (a b : ℤ) : 2*a*(2*b)=4*a*b := by grind only
  rw [group] at a1 a2
  refine ⟨p,q,s,v,pp,qp,sp,vp,ep,eq,es,ev,?_,?_,?_,?_⟩
  · exact_mod_cast a1
  · exact_mod_cast a2
  · rw [ep,es] at hk
    revert hk; clear * -; intro hk; grind only
  · rw [eq,ev] at hl
    revert hl; clear * -; intro hl; grind only

theorem axisResidues {n u r x y k l g m A B c : ℕ} (f : Fiber n u r x y k l g m A B c) :
    Nat.ModEq (4*r^2) (u^2*(k*l)) (u*r-m*c) ∧
    Nat.ModEq (4*u^2) (r^2*(k*l)) (u*r+m*c) ∧
    (4*r^2)+(u*r-m*c)≤u^2*(k*l) := by
  obtain ⟨p,q,s,v,pp,qp,sp,vp,_,_,_,_,a1,a2,_⟩:=shiftedFactors f
  have first : u^2*(k*l)=u*r-m*c+(4*r^2)*(p*q) := by rw [a1]; ac_rfl
  have second : r^2*(k*l)=u*r+m*c+(4*u^2)*(s*v) := by rw [a2]; ac_rfl
  have mode (w d z : ℕ) : Nat.ModEq d (w+d*z) w := by simp [Nat.ModEq]
  have le:=Nat.le_mul_of_pos_right (4*r^2) (Nat.mul_pos pp qp)
  exact ⟨first ▸ mode ..,second ▸ mode ..,by omega⟩

/-- An unbounded exclusion for unit exchanges, including prime-power R. -/
theorem unitSize {n R x y : ℕ} (e : Exchange n 1 R x y) : 4*R^2+3<x*y := by
  obtain ⟨k,l,g,m,A,B,c,f⟩:=buildFiber e
  obtain ⟨p,q,s,v,pp,qp,sp,vp,ep,eq,_,_,_⟩:=shiftedFactors f
  simp only [one_mul] at ep eq
  obtain ⟨_,_,le⟩:=axisResidues f
  simp only [one_pow,one_mul] at le
  have bd:=unitDeficit f
  have kk:=f.conditions.k3
  have ll:=f.conditions.l3
  have left:=Nat.mul_lt_mul_of_pos_right (show k<x by omega) (show 0<l by omega)
  have right:=Nat.mul_le_mul_left x (show l≤y by omega)
  omega

#print axioms shiftedFactors
#print axioms axisResidues
#print axioms unitSize
end CrystalCampaign.StageTwo
