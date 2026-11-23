import Fiber
open Arxiv.«1601.03081»
namespace CrystalCampaign.StageTwo

private theorem inverseIdentity {u r x y A B c : ℕ} (ix : c*x+u*A=r*B) (iy : c*y+u*B=r*A) :
    c^2*(x*y)+(u*r)*(A^2+B^2)=(r^2+u^2)*(A*B) := by
  have hx : (c:ℤ)*x+(u:ℤ)*A=(r:ℤ)*B := by exact_mod_cast ix
  have hy : (c:ℤ)*y+(u:ℤ)*B=(r:ℤ)*A := by exact_mod_cast iy
  have xx : (c:ℤ)*x=r*B-u*A := by omega
  have yy : (c:ℤ)*y=r*A-u*B := by omega
  have h : (c:ℤ)^2*(x*y)+(u*r)*(A^2+B^2)=(r^2+u^2)*(A*B) := by
    calc
      _ = ((c:ℤ)*x)*(c*y)+(u*r)*(A^2+B^2) := by grind only
      _ = _ := by rw [xx,yy]; grind only
  exact_mod_cast h

/-- Subtraction-free form of the primitive binary quadratic. -/
def Conic (u r g m A B c : ℕ) : Prop :=
  (u*r)^2*(A^2+B^2)+c^2*(m*g*A*B)=(u*r)*((r^2+u^2)*(A*B))+c^2

/-- With the two exact inverse linear equations, the conic is equivalent to the product equation. -/
theorem conic_iff_product {u r x y g m A B c : ℕ} (cp : 0<c)
    (ix : c*x+u*A=r*B) (iy : c*y+u*B=r*A) :
    Conic u r g m A B c ↔ u*r*x*y+1=m*g*A*B := by
  unfold Conic
  have ih:=inverseIdentity ix iy
  have ident : (u*r)*((r^2+u^2)*(A*B))+c^2 =
      (u*r)^2*(A^2+B^2)+c^2*(u*r*x*y+1) := by
    rw [← ih]
    simp only [Nat.mul_add,pow_two,Nat.mul_one]
    ac_rfl
  rw [ident,Nat.add_right_inj,Nat.mul_right_inj (show c^2≠0 by positivity)]
  exact eq_comm

theorem fiberConic {n u r x y k l g m A B c : ℕ} (f : Fiber n u r x y k l g m A B c) :
    Conic u r g m A B c := (conic_iff_product f.cPos f.invX f.invY).mpr
      (f.conditions.product ▸ fiberProduct f)

private theorem integralFactor {u r g m A B c : ℕ} (h : Conic u r g m A B c) :
    (A:ℤ) ∣ ((u*r:ℕ):ℤ)^2*(B:ℤ)^2-(c:ℤ)^2 := by
  let t : ℤ := (u:ℤ)*r
  unfold Conic at h
  have he : t^2*((A:ℤ)^2+B^2)+(c:ℤ)^2*(m*g*A*B)=t*((r^2+u^2)*(A*B))+c^2 := by
    dsimp [t]; exact_mod_cast h
  push_cast
  change (A:ℤ) ∣ t^2*(B:ℤ)^2-(c:ℤ)^2
  refine ⟨(t*(r^2+u^2)-(m:ℤ)*g*c^2)*B-t^2*A,?_⟩
  grind only

private theorem projectSuccessor {a b g m t c : ℤ} (hf : a ∣ t^2*b^2-c^2)
    (hd : m*b+1 ∣ g*a) : m*b+1 ∣ g*(t^2-(m*c)^2) := by
  obtain ⟨z,hz⟩:=hf
  obtain ⟨v,hv⟩:=hd
  refine ⟨v*m^2*z-g*t^2*(m*b-1),?_⟩
  calc
    _ = g*(t^2*b^2-c^2)*m^2-g*t^2*((m*b+1)*(m*b-1)) := by grind only
    _ = (g*a)*z*m^2-g*t^2*((m*b+1)*(m*b-1)) := by rw [hz]; grind only
    _ = _ := by rw [hv]; grind only

theorem conicSwap {u r g m A B c : ℕ} (h : Conic u r g m A B c) :
    Conic u r g m B A c := by
  unfold Conic at *
  convert h using 1 <;> ac_rfl

/-- The exact elimination works already for one successor, before the other is tested. -/
theorem successorElimination {u r g m A B c : ℕ} (conic : Conic u r g m A B c)
    (lt : m*c<u*r) (dvd : m*B+1 ∣ g*A) :
    m*B+1 ∣ g*((u*r)^2-(m*c)^2) := by
  have hd : (m:ℤ)*B+1 ∣ (g:ℤ)*A := by exact_mod_cast dvd
  have hf := integralFactor conic
  have h := projectSuccessor hf hd
  have hh : (m:ℤ)*B+1 ∣ (g:ℤ)*(((u:ℤ)*r)^2-((m:ℤ)*c)^2) := by simpa using h
  have le : (m*c)^2≤(u*r)^2:=Nat.pow_le_pow_left lt.le 2
  exact_mod_cast (show ((m*B+1:ℕ):ℤ) ∣ ((g*((u*r)^2-(m*c)^2):ℕ):ℤ) by
    push_cast [Nat.cast_sub le]; exact hh)

private theorem quotientLt {a b k : ℕ} (ha : 1<a) (he : a*b+1=(a+b)*k) : k<a := by
  by_contra! h
  have hm:=Nat.mul_le_mul_left (a+b) h
  have id : (a+b)*a=a*a+a*b := by grind only
  have aa : a≤a*a := by simpa using Nat.mul_le_mul_left a ha.le
  rw [id,← he] at hm; omega

theorem positiveDeterminant {n u r x y k l g m A B c : ℕ} (f : Fiber n u r x y k l g m A B c) :
    m*c<u*r := by
  have e:=(conditions_iff f.gap f.spread).mpr ⟨k,l,f.conditions⟩
  obtain ⟨up,rp,xp,_⟩:=cellProperties e
  have hk := quotientLt f.conditions.proper.1 (e.first.2.2.2.1 ▸ f.conditions.firstEq)
  have rx : (m*c)*x+u*l=r*k := by
    rw [f.lEq,f.kEq]
    calc
      _ = m*(c*x+u*A) := by rw [Nat.mul_add]; ac_rfl
      _ = _ := by rw [f.invX]; ac_rfl
  have hh:=Nat.mul_lt_mul_of_pos_left hk rp
  have hxr : r*(u*x)=(u*r)*x := by ac_rfl
  rw [hxr,← rx] at hh
  exact Nat.lt_of_mul_lt_mul_right (show (m*c)*x<(u*r)*x by omega)

theorem universalCertificate {n u r x y k l g m A B c : ℕ} (f : Fiber n u r x y k l g m A B c) :
    let M:=g*((u*r)^2-(m*c)^2)
    0<M ∧ k+1 ∣ M ∧ l+1 ∣ M := by
  have lt:=positiveDeterminant f
  have d1 : m*B+1 ∣ g*A := f.kEq ▸ f.sumA ▸ f.conditions.firstDvd
  have d2 : m*A+1 ∣ g*B := f.lEq ▸ f.sumB ▸ f.conditions.secondDvd
  have h:=fiberConic f
  exact ⟨Nat.mul_pos f.gPos (Nat.sub_pos_of_lt (Nat.pow_lt_pow_left lt (by decide))),
    f.kEq ▸ successorElimination h lt d1, f.lEq ▸ successorElimination (conicSwap h) lt d2⟩

/-- The primitive conic has no integral Vieta replacement, including negative or zero replacements. -/
theorem noIntegralVieta {n u r x y k l g m A B c : ℕ} (f : Fiber n u r x y k l g m A B c) :
    ¬∃ z : ℤ, ((u*r:ℕ):ℤ)^2*A*z+(c:ℤ)^2=((u*r:ℕ):ℤ)^2*B^2 := by
  rintro ⟨z,hz⟩
  let t:=u*r
  change (t:ℤ)^2*A*z+(c:ℤ)^2=(t:ℤ)^2*B^2 at hz
  have hd : (t:ℤ) ∣ (c:ℤ)^2 := ⟨(t:ℤ)*(B^2-(A:ℤ)*z),by grind only⟩
  have dn : t∣c^2 := by exact_mod_cast hd
  have h1:=((axialCoprime f).1.pow_right 2).eq_one_of_dvd dn
  obtain ⟨up,rp,_⟩:=cellProperties ((conditions_iff f.gap f.spread).mpr ⟨k,l,f.conditions⟩)
  have rr:=f.gap
  have le : r≤t := by simpa [t] using Nat.mul_le_mul_right r (show 1≤u by omega)
  omega

/-- Reconstruct a genuine ordered collision from an integral point in one fiber.
The two separate successor divisibilities are retained in the converse. -/
theorem reconstruct {u r x y g m A B c : ℕ} (hur : u<r) (hxy : x<y) (cp : 0<c)
    (det : g*c+u^2=r^2) (ix : c*x+u*A=r*B) (iy : c*y+u*B=r*A)
    (conic : Conic u r g m A B c) (hn : Odd (u*r*x*y))
    (proper : 1<u*x ∧ 1<r*y ∧ 1<u*y ∧ 1<r*x)
    (ok : Odd (m*B)) (ol : Odd (m*A)) (hk : 3≤m*B) (hl : 3≤m*A)
    (dk : m*B+1 ∣ g*A) (dl : m*A+1 ∣ g*B) : Exchange (u*r*x*y) u r x y := by
  have sums (X Y P Q : ℕ) (i1 : c*X+u*P=r*Q) (i2 : c*Y+u*Q=r*P) : u*X+r*Y=g*P := by
    have e1:=congrArg (fun i : ℕ => u*i) i1
    have e2:=congrArg (fun i : ℕ => r*i) i2
    have e3:=congrArg (fun i : ℕ => i*P) det
    apply Nat.eq_of_mul_eq_mul_left cp
    revert e1 e2 e3; clear * -; intro e1 e2 e3; grind only
  have s:=sums x y A B ix iy
  have t:=sums y x B A iy ix
  have hp:=(conic_iff_product cp ix iy).mp conic
  apply (conditions_iff hur hxy).mpr
  exact ⟨m*B,m*A,⟨rfl,hn,proper,ok,ol,hk,hl,by rw [s,hp]; ac_rfl,by rw [t,hp]; ac_rfl,
    s ▸ dk,t ▸ dl⟩⟩

theorem fiveCertificateValue : 12*((1*5)^2-(1*2)^2)=252 := by decide

#print axioms conic_iff_product
#print axioms fiberConic
#print axioms successorElimination
#print axioms positiveDeterminant
#print axioms universalCertificate
#print axioms noIntegralVieta
#print axioms reconstruct
#print axioms fiveCertificateValue
end CrystalCampaign.StageTwo
