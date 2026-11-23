import UnitSlice
open Arxiv.«1601.03081»
namespace CrystalCampaign.StageTwo

/-- Orbit of an integral automorphism of the weakened R=5 conic. -/
def orbit : ℕ → ℕ × ℕ
  | 0 => (1,1)
  | j+1 => let (b,v):=orbit j; (33*b+100*v,32*b+97*v)

structure OrbitState (b v : ℕ) : Prop where
  vPos : 0<v
  ordered : v≤b
  oddB : Odd b
  oddV : Odd v
  norm : 25*v^2=8*b^2+16*b*v+1

theorem orbitInvariant (j : ℕ) : OrbitState (orbit j).1 (orbit j).2 := by
  induction j with
  | zero => exact ⟨by decide,by decide,⟨0,rfl⟩,⟨0,rfl⟩,by decide⟩
  | succ j ih =>
    let b:=(orbit j).1
    let v:=(orbit j).2
    change OrbitState b v at ih
    change OrbitState (33*b+100*v) (32*b+97*v)
    obtain ⟨vp,vb,⟨s,hs⟩,⟨t,ht⟩,hn⟩:=ih
    exact ⟨by omega,by omega,⟨33*s+100*t+66,by omega⟩,⟨32*s+97*t+64,by omega⟩,by grind only⟩

theorem orbitGrowth (j : ℕ) : j+1≤(orbit j).1 := by
  induction j with
  | zero => decide
  | succ j ih =>
    have h:=(orbitInvariant j).vPos
    change _ ≤ 33*(orbit j).1+100*(orbit j).2
    omega

private theorem afterOne (j : ℕ) : 133≤(orbit (j+1)).1 := by
  have state:=orbitInvariant j
  have hv:=state.vPos
  have hb:=state.ordered
  change 133≤33*(orbit j).1+100*(orbit j).2
  omega

def termX (b v : ℕ) := 2*b-v
def termY (b v : ℕ) := 2*b+5*v
def termA (b v : ℕ) := b+2*v

private theorem pointEquations {b v : ℕ} (s : OrbitState b v) :
    let x:=termX b v
    let y:=termY b v
    let a:=termA b v
    b≤x ∧ x<y ∧ Odd x ∧ Odd y ∧ Odd a ∧ x+5*y=12*a ∧ y+5*x=12*b ∧
      5*x*y+1=12*b*a ∧ Conic 1 5 12 1 a b 2 := by
  dsimp only
  obtain ⟨vp,vb,⟨z,hz⟩,⟨w,hw⟩,hn⟩:=s
  have px : termX b v+v=2*b := Nat.sub_add_cancel (by omega)
  have py : termY b v=2*b+5*v := rfl
  have pa : termA b v=b+2*v := rfl
  have zi : (termX b v:ℤ)+(v:ℤ)=2*b := by exact_mod_cast px
  have hi : 25*(v:ℤ)^2=8*(b:ℤ)^2+16*b*v+1 := by exact_mod_cast hn
  have he : 5*termX b v*termY b v+1=12*b*termA b v := by
    rw [py,pa]
    have i : (5:ℤ)*termX b v*(2*b+5*v)+1=12*b*(b+2*v) := by
      rw [show (termX b v:ℤ)=2*b-v by omega]
      grind only
    exact_mod_cast i
  have ox : Odd (termX b v) := ⟨b-w-1,by omega⟩
  have oy : Odd (termY b v) := ⟨b+5*w+2,by omega⟩
  have oa : Odd (termA b v) := ⟨z+v,by omega⟩
  refine ⟨by omega,by omega,ox,oy,oa,by omega,by omega,he,?_⟩
  apply (conic_iff_product (by decide : 0<2)
    (show 2*termX b v+1*termA b v=5*b by omega)
    (show 2*termY b v+1*b=5*termA b v by omega)).mpr
  simpa [Nat.mul_comm,Nat.mul_assoc,Nat.mul_left_comm] using he

private theorem copFromQuot {a b k : ℕ} (q : a*b+1=(a+b)*k) : a.Coprime b := by
  let d:=a.gcd b
  have da : d∣a := Nat.gcd_dvd_left .. 
  have db : d∣b := Nat.gcd_dvd_right ..
  have dn : d∣a*b:=dvd_mul_of_dvd_left da b
  have de : d∣a*b+1 := q ▸ dvd_mul_of_dvd_left (Nat.dvd_add da db) k
  exact Nat.dvd_one.mp ((Nat.dvd_add_iff_right dn).mpr de)

theorem weakFamily (j : ℕ) :
    let b:=(orbit (j+1)).1
    let v:=(orbit (j+1)).2
    let x:=termX b v
    let y:=termY b v
    let a:=termA b v
    let n:=5*x*y
    j+1≤n ∧ 1<x ∧ x<y ∧ Odd n ∧ Odd b ∧ Odd a ∧ 3≤b ∧ 3≤a ∧
      x.Coprime (5*y) ∧ y.Coprime (5*x) ∧ ({x,5*y}:Finset ℕ)≠{y,5*x} ∧
      n+1=(x+5*y)*b ∧ n+1=(y+5*x)*a ∧
      ¬(b+1∣x+5*y) ∧ ¬(a+1∣y+5*x) := by
  let b:=(orbit (j+1)).1
  let v:=(orbit (j+1)).2
  let x:=termX b v
  let y:=termY b v
  let a:=termA b v
  let n:=5*x*y
  have s : OrbitState b v:=orbitInvariant (j+1)
  obtain ⟨bx,xy,ox,oy,oa,sumA,sumB,prod,con⟩:=pointEquations s
  change b≤x at bx
  change x<y at xy
  change x+5*y=12*a at sumA
  change y+5*x=12*b at sumB
  change n+1=12*b*a at prod
  have vb:=s.vPos
  have large : 133≤b:=afterOne j
  have ba : b≤a := by dsimp [a,termA]; omega
  have hp1 : n+1=(x+5*y)*b := by rw [sumA,prod]; ac_rfl
  have hp2 : n+1=(y+5*x)*a := by rw [sumB,prod]
  have d1 : x.Coprime (5*y) := copFromQuot (k:=b) (by convert hp1 using 1; dsimp [n]; ac_rfl)
  have d2 : y.Coprime (5*x) := copFromQuot (k:=a) (by convert hp2 using 1; dsimp [n]; ac_rfl)
  have neq : ({x,5*y}:Finset ℕ)≠{y,5*x} := by
    intro eq
    have mem : x∈({y,5*x}:Finset ℕ) := eq ▸ (by simp : x∈({x,5*y}:Finset ℕ))
    simp at mem
    omega
  have growth:=orbitGrowth (j+1)
  change j+1+1≤b at growth
  have nx : x≤n := le_trans (show x≤5*x by omega)
    (Nat.le_mul_of_pos_right (5*x) (by omega))
  have on : Odd n := ((by decide : Odd 5).mul ox).mul oy
  refine ⟨show j+1≤n by omega,show 1<x by omega,xy,on,s.oddB,oa,
    show 3≤b by omega,show 3≤a by omega,d1,d2,neq,hp1,hp2,?_⟩
  rw [sumA,sumB]
  cases j with
  | zero => decide
  | succ i =>
    have prev:=afterOne i
    have big : 252<b := by
      change 252<33*(orbit (i+1)).1+100*(orbit (i+1)).2
      omega
    change Conic 1 5 12 1 a b 2 at con
    constructor
    · intro d
      have elim:=successorElimination con (by decide) (by simpa using d)
      norm_num at elim
      have le:=Nat.le_of_dvd (by decide : 0<252) elim
      omega
    · intro d
      have elim:=successorElimination (conicSwap con) (by decide) (by simpa using d)
      norm_num at elim
      have le:=Nat.le_of_dvd (by decide : 0<252) elim
      omega

theorem firstWeakTerm : orbit 1=(133,129) ∧ termX 133 129=137 ∧ termY 133 129=911 ∧
    5*137*911=624035 ∧ (137+5*911)%134=2 ∧ (911+5*137)%392=28 := by decide

set_option maxRecDepth 4096 in
theorem threePrimeRegression : Nat.Prime 5 ∧ Nat.Prime 137 ∧ Nat.Prime 911 ∧
    5*137*911=624035 ∧ ¬ IsCrystalWithComponents 624035 137 4555 ∧
    ¬ IsCrystalWithComponents 624035 911 685 ∧ ¬ IsCrystalWithComponents 17765 55 323 ∧
    ¬ IsCrystalWithComponents 17765 95 187 := by
  refine ⟨by decide,by decide,by decide,rfl,?_,?_,?_,?_⟩
  all_goals
    intro h
    have hd:=h.2.2.2.2
    norm_num at hd

#print axioms orbitInvariant
#print axioms orbitGrowth
#print axioms weakFamily
#print axioms firstWeakTerm
#print axioms threePrimeRegression
end CrystalCampaign.StageTwo
