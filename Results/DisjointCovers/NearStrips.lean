import Checker

namespace DisjointCovers

/-- One modulus and its canonical residues in rows zero and one. -/
structure StripClass where
  modulus : Nat
  lower : Nat
  upper : Nat
deriving DecidableEq

def StripClass.residue (c : StripClass) (upper : Bool) : Nat :=
  if upper then c.upper else c.lower

def stripHit (upper : Bool) (x : Int) (c : StripClass) : Bool :=
  decide (x % (c.modulus : Int) = (c.residue upper : Int))

def exactRow (n : Nat) (cs : List StripClass) (upper : Bool) : Prop :=
  ∀ x : Int, 0 ≤ x → x < (n : Int) → cs.countP (stripHit upper x) = 1

/-- Data for two rows. Each class has a point in each row and a second point
in at least one of them. The two row widths can temporarily differ. -/
structure Strip (lower upper : Nat) (cs : List StripClass) : Prop where
  distinct : (cs.map StripClass.modulus).Nodup
  valid : ∀ c ∈ cs, 2 ≤ c.modulus ∧ c.lower < c.modulus ∧ c.upper < c.modulus ∧
    c.lower ≠ c.upper ∧ c.lower < lower ∧ c.upper < upper ∧
    (c.lower + c.modulus < lower ∨ c.upper + c.modulus < upper)
  exactLower : exactRow lower cs false
  exactUpper : exactRow upper cs true

/-- A near row with a singleton and a hole on either side, both before the
next hit of the singleton in that direction. This rules out completing the
row to a one-dimensional cover by keeping its congruences and extending it. -/
def NearRow (n : Nat) (cs : List StripClass) (upper : Bool) : Prop :=
  ∃ c ∈ cs, ∃ l r : Int,
    (c.residue upper : Int) - c.modulus < l ∧ l < 0 ∧ (n : Int) ≤ r ∧
    r < (c.residue upper : Int) + c.modulus ∧ c.residue upper < n ∧
    cs.countP (stripHit upper l) = 0 ∧ cs.countP (stripHit upper r) = 0

private structure Stable (n : Nat) (cs : List StripClass) : Prop where
  size : 3 ≤ n
  cropped : Strip (n-1) n cs
  lowerFull : exactRow n cs false
  lowerNear : NearRow n cs false
  upperNear : NearRow n cs true

theorem near_prevents_completion {n : Nat} {cs : List StripClass} {upper : Bool}
    (hn : NearRow n cs upper)
    (hvalid : ∀ c ∈ cs, c.residue upper < c.modulus) (l r : Int) (hl : l ≤ 0)
    (hr : (n : Int) ≤ r)
    (hexact : ∀ x : Int, l ≤ x → x < r → cs.countP (stripHit upper x) = 1) :
    ¬ ∀ c ∈ cs, ∃ x y : Int, l ≤ x ∧ x < y ∧ y < r ∧
      stripHit upper x c ∧ stripHit upper y c := by
  obtain ⟨c, hc, lg, rg, hlg, hneg, hsize, hrg, ha, hleft, hright⟩ := hn
  have hL : lg < l := by
    by_cases h : l ≤ lg
    · have bad := hexact lg h (by omega)
      omega
    · omega
  have hR : r ≤ rg := by
    by_cases h : rg < r
    · have bad := hexact rg (by omega) h
      omega
    · omega
  intro h
  obtain ⟨x, y, hx, hxy, hy, hxc, hyc⟩ := h c hc
  have only (z : Int) (hz : l ≤ z) (h'z : z < r) (hh : stripHit upper z c) :
      z = (c.residue upper : Int) := by
    have he : z % (c.modulus : Int) = (c.residue upper : Int) := of_decide_eq_true hh
    have hsum := Int.emod_add_mul_ediv z (c.modulus : Int)
    rw [he] at hsum
    have hzero : z / (c.modulus : Int) = 0 := by
      have hM : 0 < (c.modulus : Int) := by have := hvalid c hc; omega
      by_cases hp : 1 ≤ z / (c.modulus : Int)
      · have hlarge := Int.mul_le_mul_of_nonneg_left hp (by omega : 0 ≤ (c.modulus : Int))
        simp only [Int.mul_one] at hlarge
        omega
      · by_cases hm : z / (c.modulus : Int) ≤ -1
        · have hsmall := Int.mul_le_mul_of_nonneg_left hm (by omega : 0 ≤ (c.modulus : Int))
          simp only [Int.mul_neg, Int.mul_one] at hsmall
          omega
        · omega
    rw [hzero, Int.mul_zero, Int.add_zero] at hsum
    exact hsum.symm
  have := only x hx (by omega) hxc
  have := only y (by omega) hy hyc
  omega

private def parity (p : Nat) (upper : Bool) : Nat := if upper then 1-p else p

private def liftClass (p : Nat) (c : StripClass) : StripClass :=
  ⟨2*c.modulus, 2*c.lower+p, 2*c.upper+(1-p)⟩

private def doubleRows (p : Nat) (cs : List StripClass) : List StripClass :=
  ⟨2,1-p,p⟩ :: cs.map (liftClass p)

private theorem lift_residue (p : Nat) (upper : Bool) (c : StripClass) :
    (liftClass p c).residue upper = 2*c.residue upper + parity p upper := by
  cases upper <;> rfl

private theorem emod_double (x m : Int) (hm : 0 < m) :
    x % (2*m) = 2*((x/2)%m)+x%2 := by
  have hx := Int.mul_ediv_add_emod x 2
  have hr := Int.emod_lt_of_pos (x/2) hm
  have hnonneg := Int.emod_nonneg (x/2) (by omega : m ≠ 0)
  have h2 : 0 ≤ x % 2 := Int.emod_nonneg x (by decide)
  have hb : 2 * ((x/2)%m) + x%2 < 2*m := by omega
  calc
    x % (2*m) = (2*(x/2)+x%2) % (2*m) := congrArg (· % (2*m)) hx.symm
    _ = ((2*(x/2))%(2*m)+x%2) % (2*m) := (Int.emod_add_emod ..).symm
    _ = _ := by rw [Int.mul_emod_mul_of_pos _ _ (by decide), Int.emod_eq_of_lt (by omega) hb]

private theorem hit_lift (p : Nat) (hp : p ≤ 1) (upper : Bool) (x : Int)
    (c : StripClass) (hm : 0 < c.modulus) :
    stripHit upper x (liftClass p c) =
      if x%2 = parity p upper then stripHit upper (x/2) c else false := by
  have he : (parity p upper : Int) < 2 := by cases upper <;> simp [parity] <;> omega
  have iff_hit :
      x % (2*(c.modulus : Int)) = 2*(c.residue upper : Int)+(parity p upper : Int) ↔
      x%2 = parity p upper ∧ (x/2) % (c.modulus : Int) = c.residue upper := by
    rw [emod_double _ _ (by omega)]
    omega
  unfold stripHit
  rw [lift_residue]
  have hm' : ((liftClass p c).modulus : Int) = 2*(c.modulus : Int) := by simp [liftClass]
  rw [hm', Int.natCast_add, Int.natCast_mul]
  change decide (x % (2*(c.modulus : Int)) =
      2*(c.residue upper : Int)+(parity p upper : Int)) = _
  by_cases h : x % 2 = parity p upper <;> simp [iff_hit, h]

private theorem doubled_count {p : Nat} (hp : p ≤ 1) {cs : List StripClass}
    (hpos : ∀ c ∈ cs, 0 < c.modulus) (upper : Bool) (x : Int) :
    (doubleRows p cs).countP (stripHit upper x) =
      if x%2 = parity p upper then cs.countP (stripHit upper (x/2)) else 1 := by
  have hfiller : stripHit upper x ⟨2,1-p,p⟩ = decide (x%2 ≠ parity p upper) := by
    unfold stripHit
    congr 1
    apply propext
    cases upper <;> simp [StripClass.residue, parity] <;> omega
  rw [doubleRows, List.countP_cons, hfiller, List.countP_map]
  by_cases he : x % 2 = parity p upper
  · have hc := List.countP_congr (l := cs) (p := stripHit upper x ∘ liftClass p)
        (q := stripHit upper (x/2)) (fun c hm => by
          simp [hit_lift p hp upper x c (hpos c hm), he])
    simp [he, hc]
  · have hz : cs.countP (stripHit upper x ∘ liftClass p) = 0 := by
      apply List.countP_eq_zero.mpr
      intro c hc
      simp [hit_lift p hp upper x c (hpos c hc), he]
    simp [he, hz]

private theorem kept_bounds {n p : Nat} (hp : p ≤ 1) (hn : 3 ≤ n)
    {cs : List StripClass} (h : Stable n cs) :
    ∀ c ∈ cs, 2 ≤ c.modulus ∧ c.lower < c.modulus ∧ c.upper < c.modulus ∧
      c.lower < n-p ∧ c.upper < n ∧
      (c.lower+c.modulus < n-p ∨ c.upper+c.modulus < n) := by
  intro c hc
  obtain ⟨hm, hL, hU, hne, hl, hu, hh⟩ := h.cropped.valid c hc
  refine ⟨hm,hL,hU,by omega,hu,?_⟩
  rcases hh with hh | hh
  · exact Or.inl (by omega)
  · exact Or.inr hh

private theorem doubled_near {n p : Nat} (hp : p ≤ 1) {cs : List StripClass}
    (hpos : ∀ c ∈ cs, 0 < c.modulus) (upper : Bool)
    (hvalid : ∀ c ∈ cs, (liftClass p c).residue upper < 2*n-p)
    (h : NearRow n cs upper) : NearRow (2*n-p) (doubleRows p cs) upper := by
  obtain ⟨c,hc,l,r,hbl,hl,hr,hbr,ha,hlhole,hrhole⟩ := h
  let d : Int := parity p upper
  have hd₀ : 0 ≤ d := by dsimp [d]; omega
  have hd₁ : d < 2 := by dsimp [d]; cases upper <;> simp [parity] <;> omega
  refine ⟨liftClass p c, List.mem_cons_of_mem _ (List.mem_map_of_mem hc),
    2*l+d, 2*r+d, ?_, ?_, ?_, ?_, hvalid c hc, ?_, ?_⟩
  · rw [lift_residue]
    simp [liftClass, d] at *
    omega
  · omega
  · omega
  · rw [lift_residue]
    simp [liftClass, d] at *
    omega
  · rw [doubled_count hp hpos]
    have he : (2*l+d)%2 = (parity p upper : Int) := by dsimp [d]; omega
    have hh : (2*l+d)/2 = l := by omega
    simp [he, hh, hlhole]
  · rw [doubled_count hp hpos]
    have he : (2*r+d)%2 = (parity p upper : Int) := by dsimp [d]; omega
    have hh : (2*r+d)/2 = r := by omega
    simp [he, hh, hrhole]

private theorem step {n p : Nat} (hp : p ≤ 1) {cs : List StripClass} (h : Stable n cs) :
    Stable (2*n-p) (doubleRows p cs) := by
  let w := 2*n-p
  have hn := h.size
  have hpos : ∀ c ∈ cs, 0 < c.modulus := fun c hc => by
    have := (h.cropped.valid c hc).1
    omega
  have hkeep := kept_bounds hp hn h
  have hlow : exactRow (n-p) cs false := by
    have hp' : p = 0 ∨ p = 1 := by omega
    rcases hp' with rfl | rfl
    · simpa using h.lowerFull
    · exact h.cropped.exactLower
  have newLower (limit : Nat) (hw : limit ≤ w) : exactRow limit (doubleRows p cs) false := by
    intro x hx hxl
    rw [doubled_count hp hpos]
    simp only [parity, Bool.false_eq_true, ite_false]
    by_cases he : x%2 = (p:Int)
    · rw [ite_eq_left he]
      exact hlow (x/2) (by omega) (by dsimp [w] at hw; omega)
    · simp [he]
  have newUpper : exactRow w (doubleRows p cs) true := by
    intro x hx hxl
    rw [doubled_count hp hpos]
    simp only [parity, ite_true]
    by_cases he : x%2 = ((1-p : Nat):Int)
    · rw [ite_eq_left he]
      exact h.cropped.exactUpper (x/2) (by omega) (by dsimp [w] at hxl; omega)
    · simp [he]
  have hstrip : Strip (w-1) w (doubleRows p cs) := by
    refine ⟨?_, ?_, newLower (w-1) (by omega), newUpper⟩
    · have hmap : (cs.map (liftClass p)).map StripClass.modulus =
          (cs.map StripClass.modulus).map (2*·) := by
        simp [List.map_map, Function.comp_def, liftClass]
      rw [doubleRows, List.map_cons, List.nodup_cons, hmap, List.Nodup, List.pairwise_map]
      refine ⟨?_, h.cropped.distinct.imp (fun hne he => hne (by omega))⟩
      intro he
      obtain ⟨m, hm, heq⟩ := List.mem_map.mp he
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hm
      have hM := (h.cropped.valid c hc).1
      dsimp at heq
      omega
    · intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · dsimp [w]
        omega
      · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
        obtain ⟨hm, hL, hU, hl, hu, hh⟩ := hkeep d hd
        dsimp [liftClass, w]
        rcases hh with hh | hh <;> omega
  refine ⟨by omega, hstrip, newLower w (by omega), ?_, ?_⟩
  · exact doubled_near hp hpos false (fun c hc => by
      have hh := (hstrip.valid _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hc))).2.2.2.2.1
      change (liftClass p c).lower < w-1 at hh
      change (liftClass p c).lower < w
      omega) h.lowerNear
  · exact doubled_near hp hpos true (fun c hc =>
      (hstrip.valid _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hc))).2.2.2.2.2.1) h.upperNear

private def checkRow (n : Nat) (cs : List StripClass) (upper : Bool) : Bool :=
  (List.range n).all (fun x => decide (cs.countP (stripHit upper (x:Int)) = 1))

private theorem row_of_check {n : Nat} {cs : List StripClass} {upper : Bool}
    (h : checkRow n cs upper = true) : exactRow n cs upper := by
  intro x hx hxn
  have ha : x.toNat < n := by omega
  have := List.all_eq_true.mp h x.toNat (List.mem_range.mpr ha)
  simpa [Int.toNat_of_nonneg hx] using this

private def checkImmediateHoles (n : Nat) (cs : List StripClass) (upper : Bool) : Bool :=
  decide (cs.countP (stripHit upper (-1)) = 0) &&
  decide (cs.countP (stripHit upper n) = 0) &&
  cs.any (fun c => decide ((c.residue upper : Int) - c.modulus < -1 ∧
    n < c.residue upper + c.modulus ∧ c.residue upper < n))

private theorem near_of_check {n : Nat} {cs : List StripClass} {upper : Bool}
    (h : checkImmediateHoles n cs upper = true) : NearRow n cs upper := by
  simp only [checkImmediateHoles, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at h
  obtain ⟨c,hc,hl,hr,ha⟩ := h.2
  exact ⟨c,hc,-1,n,hl,by decide,Int.le_refl _,by omega,ha,h.1.1,h.1.2⟩

private def checkData (n : Nat) (cs : List StripClass) : Bool :=
  decide (cs.map StripClass.modulus).Nodup &&
  cs.all (fun c => decide (2 ≤ c.modulus ∧ c.lower < c.modulus ∧ c.upper < c.modulus ∧
    c.lower ≠ c.upper ∧ c.lower < n-1 ∧ c.upper < n ∧
    (c.lower + c.modulus < n-1 ∨ c.upper + c.modulus < n)))

private def checkSeed (n : Nat) (cs : List StripClass) : Bool :=
  decide (3 ≤ n) && checkData n cs &&
  checkRow (n-1) cs false && checkRow n cs true && checkRow n cs false &&
  checkImmediateHoles n cs false && checkImmediateHoles n cs true

private theorem stable_of_check {n : Nat} {cs : List StripClass}
    (h : checkSeed n cs = true) : Stable n cs := by
  simp only [checkSeed, checkData, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hn, hd, hv⟩, hl⟩, hu⟩, hlf⟩, hln⟩, hun⟩ := h
  exact ⟨hn,⟨hd,hv,row_of_check hl,row_of_check hu⟩,row_of_check hlf,
    near_of_check hln,near_of_check hun⟩

private def seeds : List (List StripClass) := [
  [⟨5,3,1⟩, ⟨6,4,3⟩, ⟨8,6,4⟩, ⟨9,2,5⟩, ⟨10,5,7⟩, ⟨11,9,2⟩, ⟨12,0,8⟩, ⟨16,1,10⟩, ⟨18,7,0⟩],
  [⟨6,3,4⟩, ⟨8,5,6⟩, ⟨9,7,3⟩, ⟨10,1,8⟩, ⟨11,8,2⟩, ⟨12,10,5⟩, ⟨13,4,9⟩, ⟨14,0,11⟩, ⟨15,12,0⟩, ⟨16,2,7⟩, ⟨18,6,1⟩],
  [⟨7,3,4⟩, ⟨8,4,6⟩, ⟨9,6,7⟩, ⟨10,8,3⟩, ⟨11,5,8⟩, ⟨12,1,0⟩, ⟨13,11,2⟩, ⟨14,0,10⟩, ⟨15,9,5⟩, ⟨16,7,1⟩, ⟨17,2,9⟩],
  [⟨7,2,3⟩, ⟨8,5,4⟩, ⟨9,1,5⟩, ⟨10,7,6⟩, ⟨11,3,2⟩, ⟨12,6,7⟩, ⟨13,11,8⟩, ⟨14,12,1⟩, ⟨15,0,9⟩, ⟨16,4,11⟩, ⟨18,8,0⟩],
  [⟨3,0,1⟩, ⟨10,7,8⟩, ⟨11,5,3⟩, ⟨12,10,5⟩, ⟨13,1,11⟩, ⟨14,11,6⟩, ⟨15,13,0⟩, ⟨16,4,9⟩, ⟨17,2,12⟩, ⟨19,8,2⟩],
  [⟨8,4,6⟩, ⟨9,7,2⟩, ⟨10,8,5⟩, ⟨11,6,7⟩, ⟨12,1,4⟩, ⟨13,10,8⟩, ⟨14,11,3⟩, ⟨15,0,12⟩, ⟨16,5,9⟩, ⟨17,2,13⟩, ⟨18,14,1⟩, ⟨19,3,10⟩, ⟨23,9,0⟩],
  [⟨5,1,3⟩, ⟨9,4,2⟩, ⟨10,8,7⟩, ⟨12,5,4⟩, ⟨13,2,9⟩, ⟨14,12,5⟩, ⟨15,9,0⟩, ⟨16,7,14⟩, ⟨17,3,12⟩, ⟨18,10,6⟩, ⟨19,0,10⟩, ⟨20,14,1⟩],
  [⟨3,0,1⟩, ⟨9,1,2⟩, ⟨10,7,8⟩, ⟨11,5,6⟩, ⟨14,11,9⟩, ⟨15,8,0⟩, ⟨16,4,14⟩, ⟨18,14,3⟩, ⟨19,13,5⟩, ⟨20,2,12⟩],
  [⟨4,0,1⟩, ⟨9,5,2⟩, ⟨11,6,8⟩, ⟨13,9,10⟩, ⟨14,7,4⟩, ⟨15,11,0⟩, ⟨16,2,14⟩, ⟨17,13,7⟩, ⟨18,1,12⟩, ⟨19,10,3⟩, ⟨20,15,6⟩, ⟨22,3,16⟩],
  [⟨4,1,2⟩, ⟨6,0,1⟩, ⟨11,8,9⟩, ⟨12,3,5⟩, ⟨13,10,11⟩, ⟨15,7,0⟩, ⟨17,14,4⟩, ⟨18,2,12⟩, ⟨19,16,8⟩, ⟨20,11,3⟩, ⟨22,4,16⟩],
  [⟨3,0,1⟩, ⟨6,1,3⟩, ⟨12,10,8⟩, ⟨14,2,12⟩, ⟨15,8,2⟩, ⟨16,4,14⟩, ⟨17,11,6⟩, ⟨18,14,0⟩, ⟨19,17,5⟩, ⟨21,5,11⟩],
  [⟨4,0,1⟩, ⟨6,1,2⟩, ⟨12,5,7⟩, ⟨13,9,11⟩, ⟨15,11,3⟩, ⟨17,14,10⟩, ⟨18,15,4⟩, ⟨19,2,12⟩, ⟨20,3,15⟩, ⟨21,6,16⟩, ⟨22,18,6⟩, ⟨23,10,0⟩],
  [⟨4,0,1⟩, ⟨6,3,0⟩, ⟨8,2,3⟩, ⟨13,6,7⟩, ⟨14,11,8⟩, ⟨16,14,10⟩, ⟨18,5,14⟩, ⟨19,17,4⟩, ⟨21,1,16⟩, ⟨22,7,15⟩, ⟨26,13,2⟩],
  [⟨9,1,7⟩, ⟨10,6,3⟩, ⟨12,9,6⟩, ⟨13,7,9⟩, ⟨14,11,12⟩, ⟨15,12,5⟩, ⟨16,14,8⟩, ⟨17,5,2⟩, ⟨18,0,15⟩, ⟨19,15,10⟩, ⟨20,3,11⟩, ⟨21,13,0⟩, ⟨22,2,14⟩, ⟨23,8,4⟩, ⟨25,4,17⟩, ⟨27,17,1⟩],
  [⟨4,0,2⟩, ⟨8,2,3⟩, ⟨10,1,5⟩, ⟨14,9,7⟩, ⟨15,7,8⟩, ⟨16,3,12⟩, ⟨17,13,0⟩, ⟨19,15,13⟩, ⟨20,17,9⟩, ⟨21,6,16⟩, ⟨23,14,1⟩, ⟨24,5,20⟩, ⟨27,25,4⟩],
  [⟨4,0,1⟩, ⟨6,1,0⟩, ⟨8,6,3⟩, ⟨14,9,8⟩, ⟨16,5,7⟩, ⟨18,15,14⟩, ⟨19,10,16⟩, ⟨21,17,10⟩, ⟨22,18,4⟩, ⟨23,3,20⟩, ⟨25,2,15⟩, ⟨26,11,2⟩],
  [⟨3,0,1⟩, ⟨6,1,0⟩, ⟨9,2,5⟩, ⟨12,4,3⟩, ⟨15,8,11⟩, ⟨19,17,2⟩, ⟨20,14,9⟩, ⟨21,5,17⟩, ⟨22,10,20⟩, ⟨25,22,8⟩],
  [⟨4,1,2⟩, ⟨6,2,1⟩, ⟨8,3,0⟩, ⟨12,4,3⟩, ⟨14,10,9⟩, ⟨15,0,5⟩, ⟨17,6,11⟩, ⟨21,18,12⟩, ⟨22,12,17⟩, ⟨24,7,21⟩, ⟨25,22,4⟩]
]

private theorem seeds_checked : checkTable checkSeed 19 seeds = true := by decide

private theorem stable_from_nineteen (n : Nat) (hn : 19 ≤ n) :
    ∃ cs, Stable n cs := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hsmall : n < 37
    · let i := n-19
      have hi : i < seeds.length := by
        change i < 18
        omega
      have hchecked := checkTable_at seeds_checked hi
      have hindex : 19+i = n := by omega
      rw [hindex] at hchecked
      exact ⟨seeds[i], stable_of_check hchecked⟩
    · let k := (n+1)/2
      let p := (2*k)-n
      have hkn : k < n := by dsimp [k]; omega
      have hk : 19 ≤ k := by dsimp [k]; omega
      have hp : p ≤ 1 := by dsimp [p,k]; omega
      have hwidth : 2*k-p = n := by dsimp [p,k]; omega
      obtain ⟨cs, hcs⟩ := ih k hkn hk
      exact ⟨doubleRows p cs, hwidth ▸ step hp hcs⟩

theorem near_strips_from_nineteen (n : Nat) (hn : 19 ≤ n) :
    ∃ cs, Strip n n cs ∧ NearRow n cs false ∧ NearRow n cs true := by
  obtain ⟨cs,h⟩ := stable_from_nineteen n hn
  refine ⟨cs,⟨h.cropped.distinct,?_,h.lowerFull,h.cropped.exactUpper⟩,h.lowerNear,h.upperNear⟩
  intro c hc
  obtain ⟨hm,hlo,hup,hne,hl,hu,ht⟩ := h.cropped.valid c hc
  refine ⟨hm,hlo,hup,hne,by omega,hu,?_⟩
  rcases ht with ht | ht
  · exact Or.inl (by omega)
  · exact Or.inr ht

end DisjointCovers
