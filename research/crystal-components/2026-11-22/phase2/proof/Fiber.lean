import Cells
open Arxiv.«1601.03081»
namespace CrystalCampaign.StageTwo

/-- Primitive sums S=gA,T=gB and primitive quotient multiplier m. -/
structure Fiber (n u r x y k l g m A B c : ℕ) : Prop where
  conditions : Conditions n u r x y k l
  gap : u<r
  spread : x<y
  gPos : 0<g
  cPos : 0<c
  mPos : 0<m
  aPos : 0<A
  bPos : 0<B
  oddA : Odd A
  oddB : Odd B
  oddM : Odd m
  evenC : Even c
  reduced : A.Coprime B
  det : g*c+u^2=r^2
  sumA : u*x+r*y=g*A
  sumB : u*y+r*x=g*B
  kEq : k=m*B
  lEq : l=m*A
  invX : c*x+u*A=r*B
  invY : c*y+u*B=r*A
  gGcd : g=(u*x+r*y).gcd (u*y+r*x)
  mGcd : m=k.gcd l

theorem neighboringCoprime {n a b : ℕ} (ha : a∣n+1) (hb : b∣n) : a.Coprime b := by
  have ht:=(Nat.gcd_dvd_left a b).trans ha
  have hn:=(Nat.gcd_dvd_right a b).trans hb
  exact Nat.dvd_one.mp ((Nat.dvd_add_iff_right hn).mpr ht)

theorem buildFiber {n u r x y : ℕ} (e : Exchange n u r x y) :
    ∃ k l g m A B c, Fiber n u r x y k l g m A B c := by
  obtain ⟨k,l,h⟩:=(conditions_iff e.ur e.xy).mp e
  obtain ⟨up,rp,xp,yp,ou,oR,ox,oy,_⟩:=cellProperties e
  let S:=u*x+r*y
  let T:=u*y+r*x
  let g:=S.gcd T
  let C:=r^2-u^2
  have hup:=e.ur
  have det : C+u^2=r^2 := Nat.sub_add_cancel (Nat.pow_le_pow_left hup.le 2)
  have Cpos : 0<C := Nat.sub_pos_of_lt (Nat.pow_lt_pow_left hup (by decide))
  have sp : 0<S := by dsimp [S]; have := Nat.mul_pos up xp; omega
  have tp : 0<T := by dsimp [T]; have := Nat.mul_pos up yp; omega
  have gp : 0<g := Nat.gcd_pos_of_pos_left _ sp
  obtain ⟨A,hs⟩ := Nat.gcd_dvd_left S T
  obtain ⟨B,ht⟩ := Nat.gcd_dvd_right S T
  change S=g*A at hs
  change T=g*B at ht
  have ab : A.Coprime B := by
    have e' : g=g*(A.gcd B) := by change S.gcd T=_; conv_lhs => rw [hs,ht,Nat.gcd_mul_left]
    exact Nat.eq_of_mul_eq_mul_left gp (show g*A.gcd B=g*1 by simpa using e'.symm)
  have ap : 0<A := by by_contra! hz; simp [Nat.eq_zero_of_le_zero hz] at hs; omega
  have bp : 0<B := by by_contra! hz; simp [Nat.eq_zero_of_le_zero hz] at ht; omega
  have tk : n+1=S*k:=h.firstEq
  have tl : n+1=T*l:=h.secondEq
  have ek : A*k=B*l := by
    apply Nat.eq_of_mul_eq_mul_left gp
    rw [← Nat.mul_assoc,← Nat.mul_assoc,← hs,← ht,← tk,← tl]
  have hb : B∣A*k := ⟨l,ek⟩
  obtain ⟨m,km⟩ := ab.symm.dvd_of_dvd_mul_left hb
  have lm : l=m*A := by
    apply Nat.eq_of_mul_eq_mul_left bp
    rw [← ek,km]; ac_rfl
  have km' : k=m*B := km.trans (Nat.mul_comm ..)
  have mg : m=k.gcd l := by rw [km',lm,Nat.gcd_mul_left,show B.gcd A=1 from ab.symm,Nat.mul_one]
  have oMB : Odd (m*B) := km' ▸ h.oddK
  have oMA : Odd (m*A) := lm ▸ h.oddL
  have om := Nat.Odd.of_mul_left oMB
  have oa := Nat.Odd.of_mul_right oMA
  have ob := Nat.Odd.of_mul_right oMB
  have mp : 0<m := by obtain ⟨v,hv⟩:=om; omega
  have gs : g∣S:=⟨A,hs⟩
  have gt : g∣T:=⟨B,ht⟩
  have co : g.Coprime x := neighboringCoprime (tk ▸ dvd_mul_of_dvd_left gs k)
    ⟨u*r*y,by rw [h.product]; ac_rfl⟩
  have inverse (a b : ℕ) : r*(u*b+r*a) = u*(u*a+r*b)+C*a := by
    calc
      _ = r*u*b+r^2*a := by simp only [Nat.mul_add,pow_two]; ac_rfl
      _ = _ := by rw [← det]; simp only [Nat.add_mul,Nat.mul_add,pow_two]; ac_rfl
  have id1 : r*T=u*S+C*x:=inverse x y
  have id2 : r*S=u*T+C*y:=inverse y x
  have gd := co.dvd_of_dvd_mul_right ((Nat.dvd_add_iff_right (dvd_mul_of_dvd_right gs u)).mpr
      (id1 ▸ dvd_mul_of_dvd_right gt r))
  obtain ⟨c,hc⟩:=gd
  have cp : 0<c := by by_contra! hz; simp [Nat.eq_zero_of_le_zero hz] at hc; omega
  have ix : c*x+u*A=r*B := by
    apply Nat.eq_of_mul_eq_mul_left gp
    calc
      _ = u*S+C*x := by rw [hs,hc]; simp only [Nat.mul_add]; ac_rfl
      _ = r*T := id1.symm
      _ = _ := by rw [ht]; ac_rfl
  have iy : c*y+u*B=r*A := by
    apply Nat.eq_of_mul_eq_mul_left gp
    calc
      _ = u*T+C*y := by rw [ht,hc]; simp only [Nat.mul_add]; ac_rfl
      _ = r*S := id2.symm
      _ = _ := by rw [hs]; ac_rfl
  have ec : Even c := by
    have hcx : Even (c*x) := by
      obtain ⟨v,hv⟩ := ou.mul oa
      obtain ⟨w,hw⟩ := oR.mul ob
      rw [Nat.even_iff]; omega
    exact (Nat.even_mul.mp hcx).resolve_right (Nat.not_even_iff_odd.mpr ox)
  exact ⟨k,l,g,m,A,B,c,⟨h,e.ur,e.xy,gp,cp,mp,ap,bp,oa,ob,om,ec,ab,hc ▸ det,hs,ht,km',lm,
    ix,iy,rfl,mg⟩⟩

theorem fiberProduct {n u r x y k l g m A B c : ℕ} (f : Fiber n u r x y k l g m A B c) :
    n+1=m*g*A*B := by rw [f.conditions.firstEq,f.sumA,f.kEq]; ac_rfl

theorem axialCoprime {n u r x y k l g m A B c : ℕ} (f : Fiber n u r x y k l g m A B c) :
    (u*r).Coprime c ∧ (u*r).Coprime m := by
  have e := (conditions_iff f.gap f.spread).mpr ⟨k,l,f.conditions⟩
  obtain ⟨_,_,_,_,_,_,_,_,ur,_⟩:=cellProperties e
  have cd : c ∣ g*c := dvd_mul_left .. 
  have uc : u.Coprime c := by
    let d:=u.gcd c
    have du : d∣u:=Nat.gcd_dvd_left ..
    have dg : d∣g*c:=(Nat.gcd_dvd_right u c).trans cd
    have dd : d∣r^2 := f.det ▸ Nat.dvd_add dg (by rw [pow_two]; exact dvd_mul_of_dvd_left du u)
    exact ((ur.pow_right 2).coprime_dvd_left du).eq_one_of_dvd dd
  have rc : r.Coprime c := by
    let d:=r.gcd c
    have dr : d∣r:=Nat.gcd_dvd_left ..
    have dg : d∣g*c:=(Nat.gcd_dvd_right r c).trans cd
    have dd : d∣u^2 := (Nat.dvd_add_iff_right dg).mpr (f.det ▸ (by rw [pow_two]; exact dvd_mul_of_dvd_left dr r : d∣r^2))
    exact ((ur.symm.pow_right 2).coprime_dvd_left dr).eq_one_of_dvd dd
  have md : m∣n+1:=⟨g*A*B,by rw [fiberProduct f]; ac_rfl⟩
  have ud : u*r∣n:=⟨x*y,by rw [f.conditions.product]; ac_rfl⟩
  exact ⟨Nat.coprime_mul_iff_left.mpr ⟨uc,rc⟩,(neighboringCoprime md ud).symm⟩

#print axioms buildFiber
#print axioms fiberProduct
#print axioms axialCoprime
end CrystalCampaign.StageTwo
