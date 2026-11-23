import Crystal
open Arxiv.«1601.03081»
namespace CrystalCampaign

private theorem divisorBoundFive {A B : ℕ}
    (eqn : 25*(A^2+B^2)=82*A*B+4) (hd : A+1 ∣ 12*B) : A+1 ∣ 3024 := by
  obtain ⟨z,hz⟩ := hd
  have he : 25*((A:ℤ)^2+(B:ℤ)^2)=82*A*B+4 := by exact_mod_cast eqn
  have hw : 12*(B:ℤ)=((A:ℤ)+1)*z := by exact_mod_cast hz
  have h : (A:ℤ)+1 ∣ 3024 := by
    refine ⟨-(3600*((A:ℤ)-1)-11808*B+(z:ℤ)*(300*B+984)),?_⟩
    grind only
  exact_mod_cast h

private def fiveList : List ℕ :=
  (List.range 3024).filter fun a => decide (3≤a ∧ a+1 ∣ 3024)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2500000 in
private theorem gridFive : (fiveList.all fun a => fiveList.all fun b =>
    decide (25*(a^2+b^2) ≠ 82*a*b+4)) = true := by decide

theorem noReducedFive {A B : ℕ} (hA : 3≤A) (hB : 3≤B)
    (eqn : 25*(A^2+B^2)=82*A*B+4) (hd : A+1 ∣ 12*B) (hd' : B+1 ∣ 12*A) : False := by
  have ha := divisorBoundFive eqn hd
  have eqn' : 25*(B^2+A^2)=82*B*A+4 := by grind only
  have hb := divisorBoundFive eqn' hd'
  have mem (v : ℕ) (h : 3≤v) (d : v+1 ∣ 3024) : v∈fiveList := by
    have hv := Nat.le_of_dvd (by decide : 0<3024) d
    simp [fiveList,h,d,show v<3024 by omega]
  have row := List.all_eq_true.mp gridFive A (mem A hA ha)
  have entry := List.all_eq_true.mp row B (mem B hB hb)
  exact (of_decide_eq_true entry) eqn

#print axioms gridFive
#print axioms noReducedFive
/-- All alternative crystal pairs formed by exchanging a factor of five are impossible. -/
theorem noExchangeFive {n x y : ℕ} (h1 : IsCrystalWithComponents n x (5*y))
    (h2 : IsCrystalWithComponents n y (5*x)) : False := by
  obtain ⟨hn,hx,_,hn1,k,hk,k3,hkEq,hkd⟩ := (quotientCriterion ..).mp h1
  obtain ⟨_,hy,_,_,l,hl,l3,hlEq,hld⟩ := (quotientCriterion ..).mp h2
  let S := x+5*y
  let T := y+5*x
  let g := S.gcd T
  change n+1=S*k at hkEq
  change n+1=T*l at hlEq
  change k+1 ∣ S at hkd
  change l+1 ∣ T at hld
  have gs : g ∣ S := Nat.gcd_dvd_left ..
  have gt : g ∣ T := Nat.gcd_dvd_right ..
  have gsN : g ∣ n+1 := hkEq ▸ dvd_mul_of_dvd_left gs _
  have gx : g.Coprime x := by
    have dN := (Nat.gcd_dvd_left g x).trans gsN
    have dn : g.gcd x ∣ n := hn1 ▸ dvd_mul_of_dvd_left (Nat.gcd_dvd_right g x) _
    exact Nat.dvd_one.mp ((Nat.dvd_add_iff_right dn).mpr dN)
  have id1 : 5*T=S+24*x := by dsimp [S,T]; grind only
  have id2 : 5*S=T+24*y := by dsimp [S,T]; grind only
  have gd : g ∣ 24*x := (Nat.dvd_add_iff_right gs).mpr (id1 ▸ dvd_mul_of_dvd_right gt 5)
  have g24 := gx.dvd_of_dvd_mul_right gd
  let L := S.lcm T
  have Ld : L ∣ n+1 := Nat.lcm_dvd ⟨k,hkEq⟩ ⟨l,hlEq⟩
  have Lsmall := Nat.le_of_dvd (Nat.succ_pos n) Ld
  have gg : g*L=S*T := Nat.gcd_mul_lcm ..
  have hst : 7*(n+1)<S*T := by
    have ox := Nat.Odd.of_mul_left (hn1 ▸ hn)
    have oy := Nat.Odd.of_mul_left (h2.2.2.2.1 ▸ hn)
    obtain ⟨i,hi⟩ := ox
    obtain ⟨j,hj⟩ := oy
    have hxy : 9≤x*y := Nat.mul_le_mul (by omega : 3≤x) (by omega : 3≤y)
    have hn' : n=5*(x*y) := by rw [hn1]; grind only
    have h36 : 36*(x*y)≤S*T := by
      by_cases h : x≤y
      · have he : S*T=36*(x*y)+5*(y-x)^2 := by
          have : y=x+(y-x) := by omega
          dsimp [S,T]; grind only
        omega
      · have he : S*T=36*(x*y)+5*(x-y)^2 := by
          have : x=y+(x-y) := by omega
          dsimp [S,T]; grind only
        omega
    rw [hn']; omega
  have g7 : 7<g := by
    by_contra! h
    have e := Nat.mul_le_mul_right L h
    rw [gg] at e; omega
  have ng8 : ¬8∣g := by
    intro hg
    obtain ⟨A,hA⟩ := hg.trans gs
    obtain ⟨B,hB⟩ := hg.trans gt
    have e : A*k=B*l := by
      apply Nat.eq_of_mul_eq_mul_left (by decide : 0<8)
      rw [← Nat.mul_assoc,← Nat.mul_assoc,← hA,← hB]
      exact hkEq.symm.trans hlEq
    have hm := congrArg (fun v : ℕ => v%2) e
    change A*k%2=B*l%2 at hm
    rw [Nat.mul_mod,Nat.mul_mod B,Nat.odd_iff.mp hk,Nat.odd_iff.mp hl] at hm
    simp at hm
    obtain ⟨i,hi⟩ := Nat.Odd.of_mul_left (hn1 ▸ hn)
    omega
  have ge : g=12 := by
    obtain ⟨z,hz⟩ := g24
    have h3 : z≤3 := by
      by_contra! hh
      have := Nat.mul_le_mul_left g (show 4≤z by omega)
      omega
    have hcases : z=0 ∨ z=1 ∨ z=2 ∨ z=3 := by omega
    rcases hcases with h|h|h|h <;> rw [h] at hz <;> omega
  rw [ge] at gg gs gt
  obtain ⟨m,hm⟩ := Ld
  have m1 : m=1 := by
    by_cases he : 2≤m
    · have e := Nat.mul_le_mul_left L he
      omega
    · have hp : m≠0 := by intro hh; simp [hh] at hm
      omega
  have ltN : n+1=L := by simpa [m1] using hm
  obtain ⟨A,hA⟩ := gs
  obtain ⟨B,hB⟩ := gt
  have Sp : 0<S := by dsimp [S]; omega
  have Tp : 0<T := by dsimp [T]; omega
  have e : n+1=S*B := by
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0<12)
    rw [ltN,gg,hB]; grind only
  have eb : k=B := Nat.eq_of_mul_eq_mul_left Sp (hkEq.symm.trans e)
  have e' : n+1=T*A := by
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0<12)
    rw [ltN,gg,hA]; grind only
  have ea : l=A := Nat.eq_of_mul_eq_mul_left Tp (hlEq.symm.trans e')
  have px : 2*x+A=5*B := by omega
  have py : 2*y+B=5*A := by omega
  have heqn : 25*(A^2+B^2)=82*A*B+4 := by
    rw [hA] at e
    grind only
  rw [ea,hB] at hld
  rw [eb,hA] at hkd
  exact noReducedFive (by omega) (by omega) heqn hld hkd

#print axioms noExchangeFive
end CrystalCampaign
