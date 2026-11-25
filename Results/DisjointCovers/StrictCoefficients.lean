import Lean

namespace DisjointCovers

/-- Divide a pair of congruent coefficients by their gcd when that gcd
divides the predecessor of the modulus. -/
private theorem normalizeSlope {m d A B : Nat} (hm : 0 < m)
    (hApos : 0 < A) (hmod : (A*d)%m = B) (hg : Nat.gcd A B ∣ m-1) :
    let g := Nat.gcd A B
    ((A/g)*d)%m = B/g := by
  dsimp only
  let g := Nat.gcd A B
  let q := (A*d)/m
  have hA := Nat.gcd_dvd_left A B
  have hB := Nat.gcd_dvd_right A B
  have hsum : B+m*q = A*d := by
    dsimp [q]
    simpa only [hmod] using Nat.mod_add_div (A*d) m
  have hgq : g ∣ q := by
    have hgmd : g ∣ m*q := by
      have hd := Nat.dvd_sub (Nat.dvd_mul_right_of_dvd hA d) hB
      rwa [← hsum, Nat.add_sub_cancel_left] at hd
    have hgd := Nat.dvd_sub hgmd (Nat.dvd_mul_right_of_dvd hg q)
    rwa [← Nat.sub_mul, show m-(m-1)=1 by omega, Nat.one_mul] at hgd
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ hApos
  have hAg : A/g*g = A := Nat.div_mul_cancel hA
  have hBg : B/g*g = B := Nat.div_mul_cancel hB
  have hqg : q/g*g = q := Nat.div_mul_cancel hgq
  have hprod : B/g + m*(q/g) = (A/g)*d := by
    apply Nat.eq_of_mul_eq_mul_right hgpos
    calc
      (B/g + m*(q/g))*g = B+m*q := by rw [Nat.add_mul, Nat.mul_assoc, hBg, hqg]
      _ = A*d := hsum
      _ = (A/g)*d*g := by rw [Nat.mul_right_comm (A/g) d g, hAg]
  rw [← hprod, Nat.add_mul_mod_self_left]
  have hb : B < m := hmod ▸ Nat.mod_lt _ hm
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hb)

/-- A residue slope strictly between 1 and the predecessor of the modulus
has a representative with both coefficients greater than 1 and coprime. -/
theorem strict_slope (m d : Nat) (hd : 2 ≤ d) (hdm : d+2 ≤ m) :
    ∃ a b : Nat, 1 < a ∧ a < m ∧ 1 < b ∧ b < m ∧
      Nat.gcd a b = 1 ∧ (a*d)%m = b := by
  let A := m-1
  let B := m-d
  let g := Nat.gcd A B
  let s := A/g
  let t := B/g
  have hm : 0 < m := by omega
  have hA : 0 < A := by dsimp [A]; omega
  have hB : 0 < B := by dsimp [B]; omega
  have hBlt : B < A := by dsimp [B,A]; omega
  have hdivideA : g ∣ A := Nat.gcd_dvd_left _ _
  have hdivideB : g ∣ B := Nat.gcd_dvd_right _ _
  have hmulA : s*g = A := Nat.div_mul_cancel hdivideA
  have hmulB : t*g = B := Nat.div_mul_cancel hdivideB
  have hst : t < s := by
    apply Nat.lt_of_not_ge
    intro he
    have hh := Nat.mul_le_mul_right g he
    omega
  have ht : 0 < t := by
    by_cases he : t = 0
    · rw [he,Nat.zero_mul] at hmulB
      omega
    · exact Nat.pos_of_ne_zero he
  have hab : (A*d)%m = B := by
    have he : A*d = B + m*(d-1) := by
      have h₁ : m*d - 1*d = A*d := (Nat.sub_mul ..).symm
      have h₂ : m*d - m = m*(d-1) := by
        simpa only [Nat.mul_one] using (Nat.mul_sub m d 1).symm
      rw [Nat.one_mul] at h₁
      have h₃ : m ≤ m*d := by
        simpa using Nat.mul_le_mul_left m (by omega : 1 ≤ d)
      dsimp [B]
      omega
    rw [he,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (by dsimp [B]; omega)]
  have hstmod : (s*d)%m = t := normalizeSlope hm hA hab hdivideA
  have hstcop : Nat.gcd s t = 1 := Nat.gcd_div_gcd_div_gcd_of_pos_left hA
  have hslt : s < m := by
    have hh := Nat.div_le_self A g
    dsimp [s,A] at *
    omega
  by_cases htone : t = 1
  · let C := m-s
    let D := m-1
    let k := Nat.gcd C D
    let a := C/k
    let b := D/k
    have hge : 2 ≤ g := by simp [htone] at hmulB; dsimp [B] at hmulB; omega
    have hhalf : 2*s ≤ A := by
      have hh := Nat.mul_le_mul_left s hge
      simpa [hmulA,Nat.mul_comm 2 s] using hh
    have hC : 0 < C := by dsimp [C]; omega
    have hD : 0 < D := by dsimp [D]; omega
    have hCD : C ≤ D := by dsimp [C,D]; omega
    have hka : k ∣ C := Nat.gcd_dvd_left _ _
    have hkb : k ∣ D := Nat.gcd_dvd_right _ _
    have hklt : k < C := by
      have hdif := Nat.dvd_sub hkb hka
      have he : D-C = s-1 := by dsimp [C,D]; omega
      have hepos : 0 < D-C := by dsimp [C,D]; omega
      have := Nat.le_of_dvd hepos hdif
      dsimp [C,A] at *
      omega
    have ha : 1 < a := by
      have haeq : a*k=C := Nat.div_mul_cancel hka
      by_cases ha' : a≤1
      · have := Nat.mul_le_mul_right k ha'
        simp only [Nat.one_mul, haeq] at this
        omega
      · omega
    have hb : 1 < b := by
      have hbeq : b*k=D := Nat.div_mul_cancel hkb
      by_cases hb' : b≤1
      · have := Nat.mul_le_mul_right k hb'
        simp only [Nat.one_mul,hbeq] at this
        omega
      · omega
    have hraw : (C*d)%m = D := by
      have hh : C*d+s*d=m*d := by
        rw [← Nat.add_mul]
        simp [C,Nat.sub_add_cancel (show s≤m by omega)]
      have hrem : ((C*d)%m + 1)%m = 0 := by
        rw [← htone, ← hstmod, ← Nat.add_mod, hh, Nat.mul_mod_right]
      have hlt := Nat.mod_lt (C*d) hm
      by_cases he : (C*d)%m+1 < m
      · rw [Nat.mod_eq_of_lt he] at hrem
        omega
      · dsimp [D]
        omega
    refine ⟨a,b,ha,?_,hb,?_,Nat.gcd_div_gcd_div_gcd_of_pos_left hC,normalizeSlope hm hC hraw hkb⟩
    · have := Nat.div_le_self C k
      dsimp [a,C] at *
      omega
    · have := Nat.div_le_self D k
      dsimp [b,D] at *
      omega
  · exact ⟨s,t,by omega,hslt,by omega,by omega,hstcop,hstmod⟩

end DisjointCovers
