import Crystal

open Arxiv.«1601.03081»
namespace CrystalCampaign

/-- Cross-divisibility for two coprime-block repartitions of one product. -/
private theorem crossDvd {n u r x y C k l : ℕ} (hc : C+u^2=r^2)
    (hp : n=(u*x)*(r*y)) (ht : n+1=(u*x+r*y)*k) (ht' : n+1=(u*y+r*x)*l)
    (hs : k+1 ∣ u*x+r*y) : k+1 ∣ C*l := by
  have hN : k+1 ∣ n+1 := ht ▸ dvd_mul_of_dvd_left hs k
  have yd : y ∣ n := ⟨u*x*r,by rw [hp]; grind only⟩
  have co : Nat.Coprime (k+1) y := by
    have gt := (Nat.gcd_dvd_left (k+1) y).trans hN
    have gn := (Nat.gcd_dvd_right (k+1) y).trans yd
    exact Nat.dvd_one.mp ((Nat.dvd_add_iff_right gn).mpr gt)
  have hL : k+1 ∣ r*(u*x+r*y)*l := dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hs r) l
  have hR : k+1 ∣ u*(n+1) := dvd_mul_of_dvd_right hN u
  have eq : r*(u*x+r*y)*l = u*(n+1)+(C*l)*y := by
    rw [ht']
    calc
      _ = (r*u*x)*l+(r^2*y)*l := by simp only [Nat.mul_add,Nat.add_mul,pow_two]; ac_rfl
      _ = _ := by rw [← hc]; simp only [Nat.mul_add,Nat.add_mul,pow_two]; ac_rfl
  exact co.dvd_of_dvd_mul_right ((Nat.dvd_add_iff_right hR).mpr (eq ▸ hL))

private theorem mutualBoundOne {C k l : ℕ} (cpos : 0<C) (kp : 0<k) (lp : 0<l)
    (hk : k+1 ∣ C*l) (hl : l+1 ∣ C*k) : k≤C^2+C^3 := by
  obtain ⟨a,ha⟩ := hk
  obtain ⟨b,hb⟩ := hl
  have posa : 0<a := by
    have hp := Nat.mul_pos cpos lp
    by_contra! hz
    have : a=0 := by omega
    simp [this] at ha; omega
  have posb : 0<b := by
    have hp := Nat.mul_pos cpos kp
    by_contra! hz
    have : b=0 := by omega
    simp [this] at hb; omega
  have id1 : C^2*k=(a*b)*k+(a*b+C*b) := by grind only
  have pos := Nat.mul_pos cpos posb
  have small : a*b<C^2 := by
    by_contra! h
    have := Nat.mul_le_mul_right k h
    omega
  have le := Nat.mul_le_mul_right k (show a*b+1≤C^2 by omega)
  rw [Nat.add_mul, Nat.one_mul, id1] at le
  have bl : b≤a*b := by simpa using Nat.mul_le_mul_right b (show 1≤a by omega)
  have hbc := Nat.mul_le_mul_left C (show b≤C^2 by omega)
  have id3 : C*C^2=C^3 := by grind only
  rw [id3] at hbc
  omega

private theorem sizeFromQuotient {a b k : ℕ} (ha : 1<a) (hb : 1<b)
    (ht : a*b+1=(a+b)*k) : a≤k^2+k ∧ b≤k^2+k := by
  have gt (p q : ℕ) (hl : 1<p) (he : p*q+1=(p+q)*k) : k<p := by
    by_contra! h
    have hm := Nat.mul_le_mul_left (p+q) h
    have he' : (p+q)*p=p*p+p*q := by grind only
    have hs : p≤p*p := by simpa using Nat.mul_le_mul_left p (show 1≤p by omega)
    rw [he',← he] at hm; omega
  have ga := gt a b ha ht
  have gb := gt b a hb (by simpa [Nat.mul_comm b a,Nat.add_comm b a] using ht)
  have ia : a=k+(a-k) := by omega
  have ib : b=k+(b-k) := by omega
  have hprod : (a-k)*(b-k)+1=k^2 := by grind only
  have A : a-k≤(a-k)*(b-k) := by simpa using Nat.mul_le_mul_left (a-k) (show 1≤b-k by omega)
  have B : b-k≤(a-k)*(b-k) := by simpa using Nat.mul_le_mul_right (b-k) (show 1≤a-k by omega)
  omega

/-- A uniform finite bound for a fixed pair of exchanged blocks. For fixed u<r,
C=r²-u² and H=C²+C³, a collision forces n≤(H²+H)². -/
theorem fixedBlocksHeight {n u r x y : ℕ} (hur : u<r)
    (h1 : IsCrystalWithComponents n (u*x) (r*y))
    (h2 : IsCrystalWithComponents n (u*y) (r*x)) :
    let C := r^2-u^2
    let H := C^2+C^3
    n≤(H^2+H)^2 := by
  let C := r^2-u^2
  let H := C^2+C^3
  change n≤(H^2+H)^2
  obtain ⟨_,ha,hb,hp,k,_,hk,ht,hs⟩ := (quotientCriterion ..).mp h1
  obtain ⟨_,_,_,hp',l,_,hl,ht',hs'⟩ := (quotientCriterion ..).mp h2
  have hpow : u^2<r^2 := Nat.pow_lt_pow_left hur (by decide)
  have hc : C+u^2=r^2 := by dsimp [C]; omega
  have hcpos : 0<C := by dsimp [C]; omega
  have h1' := crossDvd hc hp ht ht' hs
  have h2' := crossDvd hc hp' ht' ht hs'
  have hkH : k≤H := mutualBoundOne hcpos (by omega) (by omega) h1' h2'
  have hpows : k^2≤H^2 := Nat.pow_le_pow_left hkH 2
  obtain ⟨sizea,sizeb⟩ := sizeFromQuotient ha hb (hp ▸ ht)
  rw [hp,pow_two (H^2+H)]
  exact Nat.mul_le_mul (by omega) (by omega)

#print axioms crossDvd
#print axioms mutualBoundOne
#print axioms sizeFromQuotient
#print axioms fixedBlocksHeight
end CrystalCampaign
