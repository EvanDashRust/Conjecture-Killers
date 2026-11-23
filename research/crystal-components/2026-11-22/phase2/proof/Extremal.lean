import AxisResidues
import Separation
open Arxiv.«1601.03081»
namespace CrystalCampaign.StageTwo

def extremalProduct (K : ℕ) := (2*K+3)*(2*K+1+2*(K*(K+1)))

structure HalfOffsets (n a b K p s : ℕ) : Prop where
  pPos : 0<p
  sPos : 0<s
  left : a=2*K+1+2*p
  right : b=2*K+1+2*s
  product : p*s=K*(K+1)
  successor : K+1 ∣ p+s-1
  nEq : n=a*b

theorem halfOffsets {n a b K : ℕ} (c : IsCrystalWithComponents n a b)
    (h : n+1=(a+b)*(2*K+1)) : ∃ p s, HalfOffsets n a b K p s := by
  obtain ⟨_,ha,hb,hn,k,_,_,hk,hd⟩:=(quotientCriterion ..).mp c
  have index := Nat.eq_of_mul_eq_mul_left (show 0<a+b by omega) (hk.symm.trans h)
  subst k
  have oo : Odd (a*b) := hn ▸ c.1
  have eqn : a*b+1=(a+b)*(2*K+1) := hn ▸ h
  obtain ⟨p,pp,ep⟩:=componentOffset ha ⟨K,rfl⟩ (Nat.Odd.of_mul_left oo) eqn
  obtain ⟨s,sp,es⟩:=componentOffset (b:=a) hb ⟨K,rfl⟩ (Nat.Odd.of_mul_right oo)
    (by simpa [Nat.add_comm,Nat.mul_comm] using eqn)
  have prod : p*s=K*(K+1) := by
    rw [ep,es] at eqn
    revert eqn; clear * -; intro eqn; grind only
  obtain ⟨v,hv⟩:=hd
  have total : K+1 ∣ 2*K+1+p+s := ⟨v,by
    rw [ep,es] at hv
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0<2)
    calc
      _ = (2*K+1+2*p)+(2*K+1+2*s) := by grind only
      _ = _ := by rw [hv]; grind only⟩
  have ident : 2*K+1+p+s=(K+1)*2+(p+s-1) := by omega
  exact ⟨p,s,pp,sp,ep,es,prod,(Nat.dvd_add_iff_right (dvd_mul_right ..)).mpr (ident ▸ total),hn⟩

theorem extremal_bound {n a b K p s : ℕ} (f : HalfOffsets n a b K p s) :
    n≤extremalProduct K := by
  obtain ⟨pp,sp,ep,es,prod,_,hn⟩:=f
  have sum : p+s≤1+p*s := by
    obtain ⟨i,ei⟩:=Nat.exists_eq_add_of_le pp
    obtain ⟨j,ej⟩:=Nat.exists_eq_add_of_le sp
    rw [ei,ej]; grind only
  let k:=2*K+1
  have le:=Nat.mul_le_mul_left (2*k) sum
  calc
    n = k^2+2*k*(p+s)+4*(p*s) := by rw [hn,ep,es]; dsimp [k]; grind only
    _ ≤ k^2+2*k*(1+p*s)+4*(p*s) := by omega
    _ = extremalProduct K := by rw [prod]; unfold extremalProduct k; grind only

theorem extremal_strict : StrictMono extremalProduct := by
  intro K L kl
  have prod:=Nat.mul_le_mul kl.le (show K+1≤L+1 by omega)
  let b:=2*K+1+2*(K*(K+1))
  let d:=2*L+1+2*(L*(L+1))
  have hb : 0<b := by dsimp [b]; omega
  have bd : b≤d := by dsimp [b,d]; omega
  exact lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right (show 2*K+3<2*L+3 by omega) hb)
    (Nat.mul_le_mul_left (2*L+3) bd)

private theorem partnerOne {K p s : ℕ} (pp : 0<p) (sp : 0<s) (prod : p*s=K*(K+1))
    (su : K+1∣p+s-1) (d : K+1∣p) : s=1 := by
  have l:=Nat.mul_le_mul_right s (Nat.le_of_dvd pp d)
  rw [prod,Nat.mul_comm K (K+1)] at l
  have ls:=Nat.le_of_mul_le_mul_left l (by omega)
  have ds : K+1∣s-1 := (Nat.dvd_add_iff_right d).mpr
    (show K+1∣p+(s-1) by rwa [show p+(s-1)=p+s-1 by omega])
  by_contra bad
  have := Nat.le_of_dvd (show 0<s-1 by omega) ds
  omega

theorem primePowerExtremal {n a b K p s t i : ℕ} (f : HalfOffsets n a b K p s)
    (pt : t.Prime) (ip : 0<i) (power : K+1=t^i) : n=extremalProduct K := by
  obtain ⟨pp,sp,ep,es,prod,su,hn⟩:=f
  have dt : t∣K+1 := power ▸ dvd_pow_self _ (by omega)
  have dd : t^i∣p*s := prod ▸ power ▸ dvd_mul_left ..
  have dsides : K+1∣p ∨ K+1∣s := by
    rw [power]
    by_cases tp : t∣p
    · have ts : ¬t∣s := by
        intro h
        have whole:=Nat.dvd_add tp h
        have almost:=dt.trans su
        have eu : p+s-1+1=p+s := by omega
        exact pt.not_dvd_one ((Nat.dvd_add_iff_right almost).mpr (eu ▸ whole))
      exact Or.inl ((pt.coprime_pow_of_not_dvd ts).symm.dvd_of_dvd_mul_right dd)
    · exact Or.inr ((pt.coprime_pow_of_not_dvd tp).symm.dvd_of_dvd_mul_left dd)
  have one : s=1 ∨ p=1 := dsides.imp (partnerOne pp sp prod su)
    (partnerOne sp pp (by simpa [Nat.mul_comm] using prod) (by simpa [Nat.add_comm] using su))
  rcases one with h | h
  · subst s; simp at prod; rw [hn,ep,es,prod]; unfold extremalProduct; grind only
  · subst p; simp at prod; rw [hn,ep,es,prod]; unfold extremalProduct; grind only

/-- A genuine collision cannot have a prime-power half-successor on the larger quotient.
This applies to original pairs directly and is independent of the four cells. -/
theorem noHigherPrimePower {n a b c d K L t i : ℕ}
    (f : IsCrystalWithComponents n a b) (g : IsCrystalWithComponents n c d)
    (ef : n+1=(a+b)*(2*K+1)) (eg : n+1=(c+d)*(2*L+1))
    (less : K<L) (pt : t.Prime) (ip : 0<i) : L+1≠t^i := by
  intro power
  obtain ⟨p,s,hl⟩:=halfOffsets f ef
  obtain ⟨q,v,hr⟩:=halfOffsets g eg
  have a':=extremal_bound hl
  have b':=primePowerExtremal hr pt ip power
  have s':=extremal_strict less
  omega

/-- The smaller positive offset of a larger index is a proper, nontrivial
idempotent modulo its half-successor and still obeys the exact successor test. -/
theorem higherOffset {n a b c d K L : ℕ} (f : IsCrystalWithComponents n a b)
    (g : IsCrystalWithComponents n c d) (ef : n+1=(a+b)*(2*K+1))
    (eg : n+1=(c+d)*(2*L+1)) (less : K<L) :
    ∃ z w : ℕ, 1<z ∧ z≤w ∧ z<L+1 ∧ z*w=L*(L+1) ∧ L+1∣z+w-1 ∧ L+1∣z*(z-1) := by
  obtain ⟨p,s,hl⟩:=halfOffsets f ef
  obtain ⟨q,v,hr⟩:=halfOffsets g eg
  have small:=lt_of_le_of_lt (extremal_bound hl) (extremal_strict less)
  obtain ⟨qp,vp,eq,ev,prod,su,hn⟩:=hr
  have nval : n=(2*L+1+2*q)*(2*L+1+2*v) := by rw [hn,eq,ev]
  have ordered (z w : ℕ) (zp : 0<z) (wp : 0<w) (zw : z≤w) (pr : z*w=L*(L+1))
      (ds : L+1∣z+w-1) (pn : n=(2*L+1+2*z)*(2*L+1+2*w)) :
      1<z ∧ z<L+1 ∧ L+1∣z*(z-1) := by
    have nz : z≠1 := by
      rintro rfl
      simp at pr
      rw [pn,pr] at small
      unfold extremalProduct at small
      rw [show 2*L+1+2*1=2*L+3 by omega] at small
      exact (Nat.lt_irrefl _ small)
    have zl : z<L+1 := by
      by_contra! no
      have big:=Nat.mul_le_mul no (le_trans no zw)
      have lt:=Nat.mul_lt_mul_of_pos_right (show L<L+1 by omega) (show 0<L+1 by omega)
      omega
    have one : z*(z+w-1)=z*(z-1)+z*w := by
      rw [show z+w-1=z-1+w by omega,Nat.mul_add]
    have whole : L+1∣z*(z+w-1):=dvd_mul_of_dvd_right ds z
    have both : L+1∣z*w := pr ▸ dvd_mul_left ..
    exact ⟨by omega,zl,(Nat.dvd_add_iff_left both).mpr (one ▸ whole)⟩
  by_cases h : q≤v
  · obtain ⟨nq,lq,di⟩:=ordered q v qp vp h prod su nval
    exact ⟨q,v,nq,h,lq,prod,su,di⟩
  · have vh : v≤q := by omega
    have dp : v*q=L*(L+1) := (Nat.mul_comm v q).trans prod
    have ds : L+1∣v+q-1 := by simpa [Nat.add_comm] using su
    obtain ⟨nv,lv,di⟩:=ordered v q vp qp vh dp ds (by rw [nval,Nat.mul_comm])
    exact ⟨v,q,nv,vh,lv,dp,ds,di⟩

theorem compositeExample : IsCrystalWithComponents 527 17 31 ∧
    528=(17+31)*11 ∧ 6∣3+10-1 ∧ 3*10=5*6 := by
  refine ⟨(quotientCriterion ..).mpr ⟨by decide,by decide,by decide,rfl,11,by decide,by decide,rfl,by decide⟩,?_⟩
  decide

#print axioms halfOffsets
#print axioms extremal_bound
#print axioms extremal_strict
#print axioms primePowerExtremal
#print axioms noHigherPrimePower
#print axioms higherOffset
#print axioms compositeExample
end CrystalCampaign.StageTwo
