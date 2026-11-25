import TypeThree
import StrictCoefficients
import Proof

namespace DisjointCovers

private theorem cancel_mul_mod {a m x y : Nat} (hm : 0 < m) (ha : Nat.Coprime m a) :
    (a*x)%m=(a*y)%m ↔ x%m=y%m := by
  constructor
  · intro he
    have hp : (a*(x%m))%m=(a*(y%m))%m := by simpa only [Nat.mul_mod_mod] using he
    have ordered (u v : Nat) (h : u≤v) (hv : v<m) (hmod : (a*v)%m=(a*u)%m) : u=v := by
      have hzero : (a*(v-u))%m=0 := by
        rw [Nat.mul_sub]
        exact Nat.sub_mod_eq_zero_of_mod_eq hmod
      have hdvd : m ∣ v-u := ha.dvd_of_dvd_mul_left (Nat.dvd_of_mod_eq_zero hzero)
      by_cases heq : u=v
      · exact heq
      · have hz : 0 < v-u := by omega
        have := Nat.le_of_dvd hz hdvd
        omega
    rcases Nat.le_total (x%m) (y%m) with h | h
    · exact ordered _ _ h (Nat.mod_lt _ hm) hp.symm
    · exact (ordered _ _ h (Nat.mod_lt _ hm) hp).symm
  · intro he
    rw [← Nat.mul_mod_mod a x m, ← Nat.mul_mod_mod a y m, he]

/-- Equal-parity distinct residues with even modulus admit the literal
strict coefficient bounds in Definition 7.2. -/
theorem strict_residues {m l u : Nat} (hm : 2 ≤ m) (hl : l<m) (hu : u<m)
    (hne : l≠u) (hme : m%2=0) (hlu : l%2=u%2) :
    RealizesResidues 2 m l u := by
  let d := if u≤l then l-u else m+l-u
  have hd : 2≤d := by dsimp [d]; split <;> omega
  have hdm : d+2≤m := by dsimp [d]; split <;> omega
  have hul : (u+d)%m=l := by
    have he : u+d=l ∨ u+d=l+m := by dsimp [d]; split <;> omega
    rcases he with he | he
    · rw [he,Nat.mod_eq_of_lt hl]
    · rw [he,Nat.add_mod_right,Nat.mod_eq_of_lt hl]
  obtain ⟨a,b,ha,ham,hb,hbm,hcop,hmod⟩ := strict_slope m d hd hdm
  have hac : Nat.Coprime m a := by
    apply (Nat.gcd_eq_one_iff).mpr
    intro g hgm hga
    apply (Nat.gcd_eq_one_iff.mp hcop) g hga
    have he := Nat.mod_add_div (a*d) m
    rw [hmod] at he
    have hsub := Nat.dvd_sub (Nat.dvd_mul_right_of_dvd hga d)
      (Nat.dvd_mul_right_of_dvd hgm ((a*d)/m))
    have hrem : a*d - m*((a*d)/m) = b := by omega
    rwa [hrem] at hsub
  have hadd (x : Nat) : (x+d)%m=l ↔ x%m=u := by
    constructor
    · intro he
      have hh := Nat.add_mod_eq_add_mod_right (m-d) (he.trans hul.symm)
      simpa only [Nat.add_assoc,show d+(m-d)=m by omega,Nat.add_mod_right,
        Nat.mod_eq_of_lt hu] using hh
    · intro he
      exact (Nat.add_mod_eq_add_mod_right d (he.trans (Nat.mod_eq_of_lt hu).symm)).trans hul
  refine ⟨a,b,a*l,ha,ham,hb,hbm,hcop,?_⟩
  intro x
  constructor
  · rw [cancel_mul_mod (by omega) hac,Nat.mod_eq_of_lt hl]
  · rw [← hmod,Nat.add_mod_mod,← Nat.mul_add,cancel_mul_mod (by omega) hac,
      Nat.mod_eq_of_lt hl,hadd]

/-- Take a one-dimensional cover on [0,k+1) and view its two length-k
subintervals as the two rows. -/
private def offsetPair (c : Class) : StripClass :=
  ⟨c.1,c.2,if c.2=0 then c.1-1 else c.2-1⟩

private theorem offsetPair_upper_hit (x : Nat) (c : Class)
    (hm : 2 ≤ c.1) (ha : c.2 < c.1) :
    (x+1)%c.1=c.2 ↔ x%c.1=(offsetPair c).upper := by
  have hb := Nat.mod_lt x (by omega : 0<c.1)
  change (x+1)%c.1=c.2 ↔ x%c.1=(if c.2=0 then c.1-1 else c.2-1)
  rw [← Nat.mod_add_mod]
  by_cases ht : x%c.1+1 < c.1
  · rw [Nat.mod_eq_of_lt ht]
    by_cases hz : c.2=0
    · rw [ite_eq_left hz,hz]
      omega
    · rw [ite_eq_right hz]
      omega
  · have he : x%c.1+1=c.1 := by omega
    rw [he,Nat.mod_self]
    by_cases hz : c.2=0
    · rw [ite_eq_left hz,hz]
      omega
    · rw [ite_eq_right hz]
      omega

private theorem paired_strip {k : Nat} {cs : List Class} (h : Cover (k+1) cs)
    (hbound : ∀ c ∈ cs, c.1<k) : Strip k k (cs.map offsetPair) := by
  refine ⟨?_,?_,?_,?_⟩
  · simpa [List.map_map, Function.comp_def, offsetPair] using h.distinct
  · intro c hm
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hm
    obtain ⟨hm,hcan,hh⟩ := h.valid d hd
    have hb := hbound d hd
    change 2 ≤ d.1 ∧ d.2 < d.1 ∧
      (if d.2=0 then d.1-1 else d.2-1) < d.1 ∧
      d.2 ≠ (if d.2=0 then d.1-1 else d.2-1) ∧
      d.2 < k ∧ (if d.2=0 then d.1-1 else d.2-1)<k ∧
      (d.2+d.1 < k ∨ (if d.2=0 then d.1-1 else d.2-1)+d.1 < k)
    by_cases hzero : d.2=0
    · rw [ite_eq_left hzero,hzero]
      exact ⟨hm,by omega,by omega,by omega,by omega,by omega,Or.inl (by omega)⟩
    · rw [ite_eq_right hzero]
      exact ⟨hm,hcan,by omega,by omega,by omega,by omega,Or.inr (by omega)⟩
  · intro x hnonneg hx
    let y := x.toNat
    have he : (y:Int)=x := Int.toNat_of_nonneg hnonneg
    rw [← he,List.countP_map]
    have hpred : (stripHit false (y:Int) ∘ offsetPair) = hit y := by
      funext c
      change decide ((y:Int)%(c.1:Int)=(c.2:Int)) = decide (y%c.1=c.2)
      simp only [Int.ofNat_mod_ofNat,Int.natCast_inj]
    rw [hpred]
    exact h.partition y (by omega)
  · intro x hnonneg hx
    let y := x.toNat
    have he : (y:Int)=x := Int.toNat_of_nonneg hnonneg
    rw [← he,List.countP_map]
    have hpred : List.countP (stripHit true (y:Int) ∘ offsetPair) cs =
        List.countP (hit (y+1)) cs := by
      apply List.countP_congr
      intro c hc
      have hv := h.valid c hc
      simp only [Function.comp_def,stripHit,decide_eq_true_eq,Int.ofNat_mod_ofNat,Int.natCast_inj,
        StripClass.residue,ite_true,hit]
      exact (offsetPair_upper_hit y c hv.1 hv.2.1).symm
    rw [hpred]
    exact h.partition (y+1) (by omega)

/-- Eventual Type 3 existence for the literal inequalities 1 < a,b < m.
Both rows are near covers at every width n at least 262. -/
theorem emanuel_type_three_strict (n : Nat) (hn : 262 ≤ n) :
    ∃ cs, Strip n n cs ∧ TwoRowIRDCSWith 2 n (stripLabel cs false) (stripLabel cs true) ∧
      NearRow n cs false ∧ NearRow n cs true := by
  let k := (n+1)/2
  let j := n/2
  obtain ⟨cs,hcs,hnearL,hnearU,hcop⟩ := coprime_near_strips k (by dsimp [k]; omega)
  obtain ⟨ds,hds,hthree,_,hbound⟩ := multiple_covers_bounded (j+1) (by dsimp [j]; omega)
  have hpair : Strip j j (ds.map offsetPair) :=
    paired_strip hds (fun c hc => by have := hbound c hc; omega)
  have hsep : ∀ c ∈ cs, ∀ d ∈ ds.map offsetPair, c.modulus ≠ d.modulus := by
    intro c hc d hd
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hd
    have h₁ := hcop c hc
    have h₂ := hthree e he
    change c.modulus ≠ e.1
    omega
  obtain ⟨es,he,hl,hu,hparity⟩ := interleave_near hcs hpair hsep hnearL hnearU
  refine ⟨es,he,he.realizes_with (by omega) ?_,hl,hu⟩
  intro c hc
  obtain ⟨hm,hl,hu,hne,_⟩ := he.valid c hc
  obtain ⟨hmod,hres⟩ := hparity c hc
  exact strict_residues hm hl hu hne hmod hres

#print axioms emanuel_type_three_strict

end DisjointCovers
