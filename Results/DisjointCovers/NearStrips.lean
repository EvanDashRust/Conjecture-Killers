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

private def checkHoles (n : Nat) (cs : List StripClass) (upper : Bool) (l r : Int) : Bool :=
  decide (l < 0 ∧ (n:Int) ≤ r) &&
  decide (cs.countP (stripHit upper l) = 0) &&
  decide (cs.countP (stripHit upper r) = 0) &&
  cs.any (fun c => decide ((c.residue upper : Int) - c.modulus < l ∧
    r < (c.residue upper : Int) + c.modulus ∧ c.residue upper < n))

private theorem near_of_check {n : Nat} {cs : List StripClass} {upper : Bool} {l r : Int}
    (h : checkHoles n cs upper l r = true) : NearRow n cs upper := by
  simp only [checkHoles, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at h
  obtain ⟨c,hc,hl,hr,ha⟩ := h.2
  exact ⟨c,hc,l,r,hl,h.1.1.1.1,h.1.1.1.2,hr,ha,h.1.1.2,h.1.2⟩

private def checkData (n : Nat) (cs : List StripClass) : Bool :=
  decide (cs.map StripClass.modulus).Nodup &&
  cs.all (fun c => decide (2 ≤ c.modulus ∧ c.lower < c.modulus ∧ c.upper < c.modulus ∧
    c.lower ≠ c.upper ∧ c.lower < n-1 ∧ c.upper < n ∧
    (c.lower + c.modulus < n-1 ∨ c.upper + c.modulus < n)))

private def checkStable (n : Nat) (cs : List StripClass) (l r : Int) : Bool :=
  decide (3 ≤ n) && checkData n cs &&
  checkRow (n-1) cs false && checkRow n cs true && checkRow n cs false &&
  checkHoles n cs false l r && checkHoles n cs true l r

private theorem stable_of_check {n : Nat} {cs : List StripClass} {l r : Int}
    (h : checkStable n cs l r = true) : Stable n cs := by
  simp only [checkStable, checkData, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
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

private theorem seeds_checked : checkTable (fun n cs => checkStable n cs (-1) n) 19 seeds = true := by
  decide

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

private theorem Stable.full {n : Nat} {cs : List StripClass} (h : Stable n cs) : Strip n n cs := by
  refine ⟨h.cropped.distinct,?_,h.lowerFull,h.cropped.exactUpper⟩
  intro c hc
  obtain ⟨hm,hlo,hup,hne,hl,hu,ht⟩ := h.cropped.valid c hc
  refine ⟨hm,hlo,hup,hne,by omega,hu,?_⟩
  rcases ht with ht | ht
  · exact Or.inl (by omega)
  · exact Or.inr ht


theorem near_strips_from_nineteen (n : Nat) (hn : 19 ≤ n) :
    ∃ cs, Strip n n cs ∧ NearRow n cs false ∧ NearRow n cs true := by
  obtain ⟨cs,h⟩ := stable_from_nineteen n hn
  exact ⟨cs,h.full,h.lowerNear,h.upperNear⟩

private structure SeedWithHoles where
  left : Int
  right : Int
  classes : List StripClass

private def checkCoprimeSeed (n : Nat) (s : SeedWithHoles) : Bool :=
  checkStable n s.classes s.left s.right &&
    s.classes.all (fun c => decide (c.modulus%3 ≠ 0))

private def coprimeSeeds : List SeedWithHoles := [
  ⟨-1, 37, [⟨7,4,3⟩, ⟨10,6,8⟩, ⟨11,8,5⟩, ⟨13,7,0⟩, ⟨14,1,11⟩, ⟨16,12,7⟩, ⟨17,10,15⟩, ⟨19,5,1⟩, ⟨20,3,9⟩, ⟨22,17,14⟩, ⟨23,21,12⟩, ⟨25,9,19⟩, ⟨26,14,4⟩, ⟨28,22,6⟩, ⟨29,2,22⟩, ⟨31,13,2⟩, ⟨35,0,21⟩]⟩,
  ⟨-1, 38, [⟨5,2,1⟩, ⟨10,1,2⟩, ⟨11,8,7⟩, ⟨13,3,4⟩, ⟨14,0,5⟩, ⟨16,10,8⟩, ⟨17,6,10⟩, ⟨19,15,9⟩, ⟨20,5,14⟩, ⟨22,20,15⟩, ⟨23,13,20⟩, ⟨25,18,0⟩, ⟨26,9,23⟩, ⟨29,4,13⟩, ⟨32,24,3⟩]⟩,
  ⟨-1, 39, [⟨5,0,2⟩, ⟨10,8,6⟩, ⟨13,11,5⟩, ⟨14,12,0⟩, ⟨16,13,8⟩, ⟨17,6,13⟩, ⟨19,14,4⟩, ⟨20,2,9⟩, ⟨22,9,19⟩, ⟨23,19,11⟩, ⟨25,16,10⟩, ⟨26,1,15⟩, ⟨28,4,21⟩, ⟨29,7,20⟩, ⟨31,3,25⟩, ⟨32,17,1⟩, ⟨35,21,3⟩]⟩,
  ⟨-1, 40, [⟨4,1,2⟩, ⟨8,3,1⟩, ⟨13,2,3⟩, ⟨14,6,7⟩, ⟨16,14,11⟩, ⟨17,7,15⟩, ⟨19,12,4⟩, ⟨20,18,8⟩, ⟨22,0,19⟩, ⟨23,16,13⟩, ⟨25,23,12⟩, ⟨26,10,24⟩, ⟨28,4,20⟩, ⟨31,26,0⟩, ⟨34,8,5⟩]⟩,
  ⟨-1, 41, [⟨4,0,2⟩, ⟨8,2,0⟩, ⟨10,3,5⟩, ⟨13,9,7⟩, ⟨14,1,3⟩, ⟨16,14,11⟩, ⟨19,6,4⟩, ⟨20,17,9⟩, ⟨23,21,13⟩, ⟨25,19,12⟩, ⟨26,5,21⟩, ⟨28,11,19⟩, ⟨31,7,28⟩, ⟨38,27,1⟩]⟩,
  ⟨-1, 43, [⟨4,0,1⟩, ⟨8,1,2⟩, ⟨13,5,6⟩, ⟨14,7,8⟩, ⟨16,6,14⟩, ⟨17,10,11⟩, ⟨19,11,12⟩, ⟨20,14,7⟩, ⟨22,15,16⟩, ⟨23,19,0⟩, ⟨25,23,15⟩, ⟨26,3,24⟩, ⟨32,26,3⟩, ⟨35,13,4⟩, ⟨37,2,20⟩]⟩,
  ⟨-1, 43, [⟨7,5,4⟩, ⟨10,4,6⟩, ⟨13,10,9⟩, ⟨14,2,10⟩, ⟨16,13,12⟩, ⟨17,15,14⟩, ⟨19,6,15⟩, ⟨20,7,0⟩, ⟨22,20,1⟩, ⟨23,21,7⟩, ⟨25,22,8⟩, ⟨26,11,19⟩, ⟨28,0,17⟩, ⟨29,9,21⟩, ⟨31,8,29⟩, ⟨32,3,27⟩, ⟨35,31,2⟩, ⟨37,18,5⟩, ⟨38,17,3⟩, ⟨40,1,13⟩]⟩,
  ⟨-1, 44, [⟨8,3,6⟩, ⟨11,9,4⟩, ⟨13,8,7⟩, ⟨14,10,11⟩, ⟨16,14,13⟩, ⟨17,12,0⟩, ⟨19,13,12⟩, ⟨20,5,16⟩, ⟨22,17,10⟩, ⟨25,22,3⟩, ⟨26,23,9⟩, ⟨28,0,19⟩, ⟨29,4,21⟩, ⟨31,6,18⟩, ⟨32,16,8⟩, ⟨34,7,24⟩, ⟨35,1,23⟩, ⟨37,18,5⟩, ⟨38,2,27⟩, ⟨40,26,1⟩, ⟨41,15,2⟩]⟩,
  ⟨-1, 45, [⟨5,1,3⟩, ⟨13,9,11⟩, ⟨14,10,6⟩, ⟨16,7,14⟩, ⟨17,13,15⟩, ⟨19,14,12⟩, ⟨20,8,9⟩, ⟨22,15,0⟩, ⟨23,4,19⟩, ⟨25,19,10⟩, ⟨26,20,1⟩, ⟨28,12,26⟩, ⟨29,3,25⟩, ⟨31,17,5⟩, ⟨32,2,17⟩, ⟨34,18,7⟩, ⟨35,29,4⟩, ⟨37,5,16⟩, ⟨38,25,2⟩, ⟨43,0,21⟩]⟩,
  ⟨-1, 46, [⟨8,2,0⟩, ⟨10,3,7⟩, ⟨13,11,9⟩, ⟨14,7,11⟩, ⟨16,6,13⟩, ⟨17,15,14⟩, ⟨19,17,15⟩, ⟨20,9,3⟩, ⟨22,5,20⟩, ⟨23,8,5⟩, ⟨25,20,19⟩, ⟨26,14,10⟩, ⟨28,0,26⟩, ⟨29,25,1⟩, ⟨31,19,2⟩, ⟨32,12,18⟩, ⟨34,16,4⟩, ⟨35,30,6⟩, ⟨37,4,12⟩, ⟨38,1,21⟩]⟩,
  ⟨-1, 47, [⟨4,0,1⟩, ⟨8,1,0⟩, ⟨14,7,6⟩, ⟨16,2,3⟩, ⟨17,5,10⟩, ⟨19,10,4⟩, ⟨20,6,11⟩, ⟨22,15,14⟩, ⟨23,19,7⟩, ⟨25,13,18⟩, ⟨26,23,12⟩, ⟨28,3,22⟩, ⟨29,14,26⟩, ⟨31,27,15⟩, ⟨34,11,28⟩, ⟨37,30,2⟩]⟩,
  ⟨-2, 49, [⟨4,3,0⟩, ⟨8,2,5⟩, ⟨13,12,9⟩, ⟨16,4,7⟩, ⟨17,16,14⟩, ⟨20,17,6⟩, ⟨22,8,11⟩, ⟨23,5,15⟩, ⟨26,6,1⟩, ⟨28,13,25⟩, ⟨29,22,18⟩, ⟨31,14,17⟩, ⟨32,21,10⟩, ⟨37,9,30⟩, ⟨38,24,3⟩, ⟨40,0,34⟩, ⟨41,29,2⟩, ⟨43,1,19⟩]⟩,
  ⟨-1, 49, [⟨5,3,0⟩, ⟨10,2,3⟩, ⟨13,1,11⟩, ⟨14,11,4⟩, ⟨16,4,12⟩, ⟨19,15,17⟩, ⟨20,17,1⟩, ⟨22,9,7⟩, ⟨23,7,8⟩, ⟨26,19,16⟩, ⟨28,16,22⟩, ⟨29,6,26⟩, ⟨31,10,27⟩, ⟨32,21,6⟩, ⟨34,29,14⟩, ⟨37,24,2⟩, ⟨38,26,9⟩, ⟨41,5,19⟩, ⟨47,0,34⟩]⟩,
  ⟨-1, 50, [⟨4,1,0⟩, ⟨8,4,5⟩, ⟨16,6,3⟩, ⟨19,8,11⟩, ⟨20,15,14⟩, ⟨22,10,17⟩, ⟨23,16,15⟩, ⟨25,23,1⟩, ⟨26,14,7⟩, ⟨28,24,18⟩, ⟨29,2,27⟩, ⟨31,26,10⟩, ⟨32,11,22⟩, ⟨34,0,31⟩, ⟨35,7,23⟩, ⟨37,19,6⟩, ⟨38,30,9⟩, ⟨40,18,2⟩, ⟨44,3,25⟩]⟩,
  ⟨-1, 51, [⟨4,0,1⟩, ⟨8,1,4⟩, ⟨16,14,10⟩, ⟨17,5,6⟩, ⟨19,15,16⟩, ⟨20,3,18⟩, ⟨22,13,8⟩, ⟨23,19,11⟩, ⟨25,6,14⟩, ⟨26,21,24⟩, ⟨28,10,3⟩, ⟨29,27,19⟩, ⟨31,26,15⟩, ⟨32,18,0⟩, ⟨35,2,22⟩, ⟨38,7,27⟩, ⟨40,29,7⟩, ⟨41,11,2⟩]⟩,
  ⟨-1, 52, [⟨7,4,5⟩, ⟨11,5,6⟩, ⟨14,12,4⟩, ⟨17,7,10⟩, ⟨19,15,16⟩, ⟨20,13,14⟩, ⟨22,14,15⟩, ⟨23,19,8⟩, ⟨25,10,11⟩, ⟨26,17,22⟩, ⟨28,9,25⟩, ⟨29,22,20⟩, ⟨31,0,29⟩, ⟨32,28,13⟩, ⟨34,20,7⟩, ⟨35,29,3⟩, ⟨37,8,24⟩, ⟨38,6,23⟩, ⟨40,30,2⟩, ⟨43,21,0⟩, ⟨44,3,9⟩, ⟨46,2,21⟩, ⟨49,1,30⟩, ⟨50,23,1⟩]⟩,
  ⟨-2, 54, [⟨4,0,1⟩, ⟨8,2,0⟩, ⟨16,11,3⟩, ⟨17,13,10⟩, ⟨19,3,4⟩, ⟨20,15,6⟩, ⟨22,17,14⟩, ⟨23,14,11⟩, ⟨25,6,22⟩, ⟨26,19,12⟩, ⟨28,23,15⟩, ⟨31,7,30⟩, ⟨32,1,28⟩, ⟨34,21,18⟩, ⟨37,29,2⟩, ⟨40,9,20⟩, ⟨41,5,31⟩, ⟨43,25,7⟩]⟩,
  ⟨-1, 54, [⟨4,0,1⟩, ⟨8,5,3⟩, ⟨16,2,12⟩, ⟨17,9,14⟩, ⟨19,3,4⟩, ⟨20,15,18⟩, ⟨23,19,16⟩, ⟨25,6,22⟩, ⟨26,7,6⟩, ⟨28,11,8⟩, ⟨29,17,26⟩, ⟨31,27,15⟩, ⟨32,23,20⟩, ⟨34,30,0⟩, ⟨35,14,24⟩, ⟨37,10,30⟩, ⟨38,25,2⟩, ⟨43,38,7⟩, ⟨50,1,10⟩]⟩,
  ⟨-2, 57, [⟨5,1,4⟩, ⟨10,5,1⟩, ⟨13,4,7⟩, ⟨14,10,8⟩, ⟨16,7,0⟩, ⟨17,3,13⟩, ⟨20,8,3⟩, ⟨23,9,12⟩, ⟨25,22,17⟩, ⟨28,27,10⟩, ⟨29,13,26⟩, ⟨31,2,28⟩, ⟨32,18,27⟩, ⟨34,19,25⟩, ⟨35,34,5⟩, ⟨37,12,18⟩, ⟨38,29,15⟩, ⟨43,40,2⟩, ⟨44,0,37⟩, ⟨46,14,6⟩]⟩,
  ⟨-1, 56, [⟨8,2,4⟩, ⟨11,3,5⟩, ⟨13,7,8⟩, ⟨14,1,11⟩, ⟨16,12,3⟩, ⟨17,4,14⟩, ⟨19,13,7⟩, ⟨20,17,10⟩, ⟨22,8,2⟩, ⟨25,23,15⟩, ⟨26,19,17⟩, ⟨28,11,9⟩, ⟨29,6,13⟩, ⟨31,22,29⟩, ⟨32,9,0⟩, ⟨35,24,6⟩, ⟨37,31,18⟩, ⟨38,16,22⟩, ⟨40,0,33⟩, ⟨44,5,23⟩, ⟨53,27,1⟩]⟩,
  ⟨-1, 57, [⟨5,1,3⟩, ⟨10,0,5⟩, ⟨13,9,11⟩, ⟨16,13,14⟩, ⟨17,8,10⟩, ⟨20,18,2⟩, ⟨22,15,19⟩, ⟨25,19,1⟩, ⟨26,7,21⟩, ⟨29,23,7⟩, ⟨31,12,29⟩, ⟨32,17,0⟩, ⟨34,24,20⟩, ⟨35,32,4⟩, ⟨37,2,34⟩, ⟨40,34,9⟩, ⟨41,14,31⟩, ⟨43,4,17⟩, ⟨44,27,12⟩, ⟨46,28,6⟩, ⟨49,5,40⟩, ⟨50,3,16⟩]⟩,
  ⟨-1, 58, [⟨4,0,1⟩, ⟨8,1,0⟩, ⟨16,2,3⟩, ⟨17,13,10⟩, ⟨19,7,4⟩, ⟨20,3,6⟩, ⟨23,14,15⟩, ⟨25,10,11⟩, ⟨28,11,22⟩, ⟨29,22,18⟩, ⟨31,15,28⟩, ⟨32,21,7⟩, ⟨34,29,20⟩, ⟨35,19,30⟩, ⟨37,5,31⟩, ⟨38,31,14⟩, ⟨41,27,2⟩, ⟨43,38,12⟩, ⟨49,6,34⟩]⟩,
  ⟨-1, 59, [⟨8,5,4⟩, ⟨11,8,5⟩, ⟨14,4,11⟩, ⟨16,12,8⟩, ⟨17,9,13⟩, ⟨19,16,10⟩, ⟨20,11,6⟩, ⟨22,20,1⟩, ⟨23,2,18⟩, ⟨25,22,17⟩, ⟨26,14,9⟩, ⟨28,6,22⟩, ⟨29,7,14⟩, ⟨31,27,0⟩, ⟨32,23,19⟩, ⟨38,1,33⟩, ⟨40,17,32⟩, ⟨41,15,37⟩, ⟨43,33,15⟩, ⟨46,3,21⟩, ⟨47,24,7⟩, ⟨50,0,34⟩, ⟨52,38,3⟩, ⟨55,10,2⟩]⟩,
  ⟨-1, 60, [⟨4,2,1⟩, ⟨8,1,2⟩, ⟨16,0,8⟩, ⟨17,11,14⟩, ⟨19,5,16⟩, ⟨20,7,3⟩, ⟨22,15,0⟩, ⟨23,21,15⟩, ⟨26,3,20⟩, ⟨28,12,19⟩, ⟨29,23,7⟩, ⟨31,8,28⟩, ⟨34,19,32⟩, ⟨35,31,4⟩, ⟨38,13,27⟩, ⟨40,36,11⟩, ⟨43,20,12⟩, ⟨46,35,6⟩, ⟨52,4,30⟩]⟩,
  ⟨-1, 61, [⟨4,0,2⟩, ⟨8,1,4⟩, ⟨16,2,1⟩, ⟨19,7,13⟩, ⟨20,11,5⟩, ⟨22,15,19⟩, ⟨25,21,23⟩, ⟨26,13,21⟩, ⟨28,19,15⟩, ⟨29,14,11⟩, ⟨31,23,0⟩, ⟨32,30,7⟩, ⟨35,29,24⟩, ⟨37,5,29⟩, ⟨41,27,16⟩, ⟨43,10,27⟩, ⟨44,38,9⟩, ⟨47,22,8⟩, ⟨49,6,37⟩, ⟨53,35,3⟩, ⟨55,3,35⟩]⟩,
  ⟨-1, 62, [⟨4,0,1⟩, ⟨10,5,0⟩, ⟨16,6,3⟩, ⟨17,13,14⟩, ⟨20,3,6⟩, ⟨22,19,12⟩, ⟨25,17,2⟩, ⟨26,11,18⟩, ⟨28,18,11⟩, ⟨31,27,28⟩, ⟨32,29,15⟩, ⟨34,31,24⟩, ⟨35,33,7⟩, ⟨37,2,32⟩, ⟨38,21,36⟩, ⟨40,9,23⟩, ⟨41,10,38⟩, ⟨43,14,22⟩, ⟨46,7,43⟩, ⟨47,26,8⟩, ⟨49,1,16⟩, ⟨50,34,4⟩]⟩,
  ⟨-1, 63, [⟨4,0,1⟩, ⟨8,2,4⟩, ⟨16,1,8⟩, ⟨17,13,14⟩, ⟨20,11,15⟩, ⟨25,14,18⟩, ⟨26,19,16⟩, ⟨28,25,6⟩, ⟨31,23,27⟩, ⟨32,27,19⟩, ⟨34,9,30⟩, ⟨35,6,32⟩, ⟨38,29,0⟩, ⟨40,22,7⟩, ⟨41,5,23⟩, ⟨43,21,11⟩, ⟨44,37,2⟩, ⟨46,15,22⟩, ⟨47,38,3⟩, ⟨49,35,10⟩, ⟨50,7,26⟩, ⟨52,3,39⟩]⟩,
  ⟨-1, 64, [⟨4,1,2⟩, ⟨8,2,1⟩, ⟨16,3,4⟩, ⟨19,8,13⟩, ⟨20,0,3⟩, ⟨23,16,21⟩, ⟨25,6,15⟩, ⟨26,22,19⟩, ⟨28,15,0⟩, ⟨29,7,8⟩, ⟨31,23,16⟩, ⟨34,32,27⟩, ⟨35,28,24⟩, ⟨37,30,11⟩, ⟨38,14,29⟩, ⟨40,4,35⟩, ⟨43,38,12⟩, ⟨44,11,39⟩, ⟨46,24,7⟩, ⟨47,12,31⟩, ⟨55,47,5⟩]⟩,
  ⟨-1, 65, [⟨11,9,2⟩, ⟨13,6,4⟩, ⟨16,8,7⟩, ⟨17,12,15⟩, ⟨19,11,10⟩, ⟨20,14,11⟩, ⟨22,15,16⟩, ⟨25,16,8⟩, ⟨26,22,19⟩, ⟨28,23,26⟩, ⟨29,10,21⟩, ⟨31,21,22⟩, ⟨32,25,20⟩, ⟨34,2,0⟩, ⟨35,33,9⟩, ⟨37,35,5⟩, ⟨38,28,25⟩, ⟨40,7,37⟩, ⟨41,3,18⟩, ⟨43,0,40⟩, ⟨44,17,27⟩, ⟨46,38,1⟩, ⟨47,13,28⟩, ⟨49,1,36⟩, ⟨50,5,41⟩, ⟨52,18,12⟩, ⟨55,27,6⟩, ⟨58,4,14⟩, ⟨59,26,3⟩]⟩,
  ⟨-1, 66, [⟨10,8,7⟩, ⟨11,2,1⟩, ⟨14,12,11⟩, ⟨20,16,18⟩, ⟨22,7,19⟩, ⟨23,19,6⟩, ⟨25,22,21⟩, ⟨26,17,24⟩, ⟨28,11,14⟩, ⟨29,21,26⟩, ⟨31,10,13⟩, ⟨32,5,16⟩, ⟨34,30,20⟩, ⟨35,32,8⟩, ⟨37,34,22⟩, ⟨38,23,31⟩, ⟨40,20,33⟩, ⟨41,14,30⟩, ⟨43,9,35⟩, ⟨44,27,5⟩, ⟨46,3,40⟩, ⟨49,31,2⟩, ⟨50,44,10⟩, ⟨52,25,9⟩, ⟨53,0,28⟩, ⟨55,4,32⟩, ⟨56,6,36⟩, ⟨59,33,3⟩, ⟨61,45,4⟩, ⟨62,1,15⟩, ⟨64,15,0⟩]⟩,
  ⟨-1, 67, [⟨10,8,5⟩, ⟨11,9,8⟩, ⟨14,12,6⟩, ⟨16,7,11⟩, ⟨19,14,13⟩, ⟨20,17,9⟩, ⟨22,3,17⟩, ⟨23,4,1⟩, ⟨25,16,21⟩, ⟨26,19,14⟩, ⟨28,21,26⟩, ⟨31,13,7⟩, ⟨32,11,28⟩, ⟨34,22,2⟩, ⟨35,1,33⟩, ⟨37,34,0⟩, ⟨38,35,4⟩, ⟨40,29,18⟩, ⟨41,24,31⟩, ⟨46,15,23⟩, ⟨47,30,10⟩, ⟨49,2,44⟩, ⟨50,46,3⟩, ⟨52,32,12⟩, ⟨53,10,50⟩, ⟨55,5,16⟩, ⟨56,6,22⟩, ⟨59,0,56⟩]⟩,
  ⟨-1, 68, [⟨4,1,2⟩, ⟨8,0,1⟩, ⟨20,3,7⟩, ⟨22,14,15⟩, ⟨25,10,23⟩, ⟨26,20,19⟩, ⟨28,11,24⟩, ⟨29,22,11⟩, ⟨31,7,13⟩, ⟨32,18,29⟩, ⟨34,28,21⟩, ⟨35,12,0⟩, ⟨37,15,32⟩, ⟨38,34,5⟩, ⟨40,19,31⟩, ⟨41,31,12⟩, ⟨43,26,20⟩, ⟨44,30,16⟩, ⟨47,44,4⟩, ⟨49,6,36⟩, ⟨50,4,28⟩, ⟨53,42,3⟩, ⟨56,27,8⟩, ⟨64,2,39⟩]⟩,
  ⟨-1, 69, [⟨5,3,1⟩, ⟨10,6,3⟩, ⟨16,9,12⟩, ⟨17,10,8⟩, ⟨20,12,17⟩, ⟨25,5,22⟩, ⟨26,21,24⟩, ⟨29,22,20⟩, ⟨31,14,27⟩, ⟨34,15,5⟩, ⟨35,7,32⟩, ⟨37,34,15⟩, ⟨38,24,10⟩, ⟨40,20,35⟩, ⟨41,35,14⟩, ⟨43,40,2⟩, ⟨44,39,18⟩, ⟨46,4,34⟩, ⟨47,17,40⟩, ⟨50,37,4⟩, ⟨52,2,30⟩, ⟨55,29,9⟩, ⟨56,11,38⟩, ⟨59,0,19⟩, ⟨61,31,7⟩, ⟨64,1,29⟩, ⟨65,19,0⟩]⟩,
  ⟨-1, 70, [⟨4,1,0⟩, ⟨8,2,1⟩, ⟨16,12,13⟩, ⟨20,15,6⟩, ⟨22,8,15⟩, ⟨25,14,5⟩, ⟨26,20,21⟩, ⟨28,3,11⟩, ⟨29,22,14⟩, ⟨31,23,27⟩, ⟨32,24,22⟩, ⟨34,4,19⟩, ⟨35,32,7⟩, ⟨37,11,34⟩, ⟨40,7,23⟩, ⟨41,27,38⟩, ⟨43,0,35⟩, ⟨44,19,18⟩, ⟨47,40,3⟩, ⟨49,36,2⟩, ⟨56,6,31⟩, ⟨59,16,10⟩]⟩,
  ⟨-1, 71, [⟨4,1,2⟩, ⟨14,8,9⟩, ⟨16,11,8⟩, ⟨19,16,17⟩, ⟨22,12,19⟩, ⟨25,23,7⟩, ⟨26,18,21⟩, ⟨28,24,16⟩, ⟨31,15,12⟩, ⟨32,10,13⟩, ⟨38,20,35⟩, ⟨40,32,20⟩, ⟨41,31,11⟩, ⟨43,30,25⟩, ⟨44,19,29⟩, ⟨46,14,33⟩, ⟨47,0,31⟩, ⟨49,28,0⟩, ⟨52,38,15⟩, ⟨53,2,27⟩, ⟨55,26,4⟩, ⟨56,6,48⟩, ⟨58,40,3⟩, ⟨59,51,5⟩, ⟨61,7,53⟩, ⟨62,4,39⟩, ⟨64,3,28⟩, ⟨68,39,1⟩]⟩,
  ⟨-1, 72, [⟨4,1,2⟩, ⟨8,4,1⟩, ⟨16,14,12⟩, ⟨20,18,7⟩, ⟨22,10,15⟩, ⟨25,23,11⟩, ⟨28,22,20⟩, ⟨29,26,16⟩, ⟨31,16,21⟩, ⟨32,11,24⟩, ⟨34,6,29⟩, ⟨35,24,4⟩, ⟨37,34,32⟩, ⟨40,35,31⟩, ⟨41,39,23⟩, ⟨43,8,35⟩, ⟨46,27,5⟩, ⟨47,19,40⟩, ⟨52,31,3⟩, ⟨53,3,43⟩, ⟨55,15,19⟩, ⟨56,7,53⟩, ⟨62,2,13⟩, ⟨67,0,8⟩, ⟨68,42,0⟩]⟩
]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem coprimeSeeds_checked : checkTable checkCoprimeSeed 37 coprimeSeeds = true := by
  decide

private theorem coprime_stable (n : Nat) (hn : 37 ≤ n) :
    ∃ cs, Stable n cs ∧ ∀ c ∈ cs, c.modulus%3 ≠ 0 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hs : n < 73
    · let i := n-37
      have hi : i < coprimeSeeds.length := by change i < 36; omega
      have hc := checkTable_at coprimeSeeds_checked hi
      rw [show 37+i=n by omega] at hc
      simp only [checkCoprimeSeed, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc
      exact ⟨coprimeSeeds[i].classes,stable_of_check hc.1,hc.2⟩
    · let k := (n+1)/2
      let p := 2*k-n
      obtain ⟨cs,hc,hcop⟩ := ih k (by dsimp [k]; omega) (by dsimp [k]; omega)
      have hp : p ≤ 1 := by dsimp [p,k]; omega
      have he : 2*k-p=n := by dsimp [p,k]; omega
      refine ⟨doubleRows p cs,he ▸ step hp hc,?_⟩
      intro c hm
      rcases List.mem_cons.mp hm with rfl | hm
      · change 2%3 ≠ 0
        decide
      · obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hm
        have := hcop d hd
        change (2*d.modulus)%3 ≠ 0
        omega

/-- There are near strips whose moduli avoid multiples of 3 at every width
at least 37. The stricter construction interleaves these with a second strip. -/
theorem coprime_near_strips (n : Nat) (hn : 37 ≤ n) :
    ∃ cs, Strip n n cs ∧ NearRow n cs false ∧ NearRow n cs true ∧
      ∀ c ∈ cs, c.modulus%3 ≠ 0 := by
  obtain ⟨cs,hc,hcop⟩ := coprime_stable n hn
  exact ⟨cs,hc.full,hc.lowerNear,hc.upperNear,hcop⟩

private def along (p : Nat) (c : StripClass) : StripClass :=
  ⟨2*c.modulus,2*c.lower+p,2*c.upper+p⟩

/-- Each modulus of the first strip is placed on even columns of both rows.
The second strip is placed on odd columns of both rows. -/
def interleave (cs ds : List StripClass) : List StripClass :=
  cs.map (along 0) ++ ds.map (along 1)

private theorem along_count {cs : List StripClass} {p : Nat} (hp : p ≤ 1)
    (hpos : ∀ c ∈ cs, 0 < c.modulus) (upper : Bool) (x : Int) :
    (cs.map (along p)).countP (stripHit upper x) =
      if x%2 = (p:Int) then cs.countP (stripHit upper (x/2)) else 0 := by
  have heq (c : StripClass) (hm : 0 < c.modulus) :
      (stripHit upper x ∘ along p) c =
        if x%2 = (p:Int) then stripHit upper (x/2) c else false := by
    have hres : (along p c).residue upper = 2*c.residue upper+p := by cases upper <;> rfl
    have hiff :
        x%(2*(c.modulus:Int))=2*(c.residue upper:Int)+(p:Int) ↔
        x%2=(p:Int) ∧ (x/2)%(c.modulus:Int)=(c.residue upper:Int) := by
      rw [emod_double _ _ (by omega)]
      omega
    change (stripHit upper x (along p c)) = _
    unfold stripHit
    rw [hres,Int.natCast_add,Int.natCast_mul]
    change decide (x%(2*(c.modulus:Int))=2*(c.residue upper:Int)+(p:Int)) = _
    by_cases he : x%2=(p:Int) <;> simp [hiff,he]
  rw [List.countP_map]
  by_cases h : x%2=(p:Int)
  · rw [ite_eq_left h]
    apply List.countP_congr
    intro c hc
    rw [heq c (hpos c hc),ite_eq_left h]
  · rw [ite_eq_right h]
    apply List.countP_eq_zero.mpr
    intro c hc
    rw [heq c (hpos c hc),ite_eq_right h]
    decide

private theorem interleave_count {cs ds : List StripClass}
    (hcpos : ∀ c ∈ cs, 0 < c.modulus) (hdpos : ∀ c ∈ ds, 0 < c.modulus)
    (upper : Bool) (x : Int) :
    (interleave cs ds).countP (stripHit upper x) =
      if x%2=0 then cs.countP (stripHit upper (x/2)) else ds.countP (stripHit upper (x/2)) := by
  unfold interleave
  rw [List.countP_append,along_count (by decide : 0≤1) hcpos,
    along_count (by decide : 1≤1) hdpos]
  have he : x%2=0 ∨ x%2=1 := by omega
  rcases he with he | he <;> simp [he]

private theorem along_moduli (p : Nat) (cs : List StripClass) :
    (cs.map (along p)).map StripClass.modulus = (cs.map StripClass.modulus).map (2*·) := by
  simp [List.map_map, Function.comp_def, along]

private theorem along_valid {n k p : Nat} {cs : List StripClass} (hp : p ≤ 1)
    (hc : Strip k k cs)
    (hbound : ∀ x < k, 2*x+p < n) :
    ∀ c ∈ cs.map (along p), 2 ≤ c.modulus ∧ c.lower < c.modulus ∧
      c.upper < c.modulus ∧ c.lower ≠ c.upper ∧ c.lower < n ∧ c.upper < n ∧
      (c.lower+c.modulus < n ∨ c.upper+c.modulus < n) := by
  intro c hmem
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hmem
  obtain ⟨hm,hl,hu,hne,hk₀,hk₁,ht⟩ := hc.valid d hd
  have hl' := hbound d.lower hk₀
  have hu' := hbound d.upper hk₁
  refine ⟨by change 2 ≤ 2*d.modulus; omega, ?_, ?_, ?_, hl', hu', ?_⟩
  · change 2*d.lower+p < 2*d.modulus
    omega
  · change 2*d.upper+p < 2*d.modulus
    omega
  · change 2*d.lower+p ≠ 2*d.upper+p
    omega
  · rcases ht with ht | ht
    · have hb := hbound (d.lower+d.modulus) ht
      left
      change 2*d.lower+p+2*d.modulus < n
      omega
    · have hb := hbound (d.upper+d.modulus) ht
      right
      change 2*d.upper+p+2*d.modulus < n
      omega

/-- The two parity lifts preserve the near witnesses in the even columns.
The output moduli are even and each class has equal parity in both rows. -/
theorem interleave_near {n : Nat} {cs ds : List StripClass}
    (hc : Strip ((n+1)/2) ((n+1)/2) cs) (hd : Strip (n/2) (n/2) ds)
    (hsep : ∀ c ∈ cs, ∀ d ∈ ds, c.modulus ≠ d.modulus)
    (hl : NearRow ((n+1)/2) cs false) (hu : NearRow ((n+1)/2) cs true) :
    ∃ es, Strip n n es ∧ NearRow n es false ∧ NearRow n es true ∧
      ∀ c ∈ es, c.modulus%2=0 ∧ c.lower%2=c.upper%2 := by
  have hcpos : ∀ c ∈ cs, 0 < c.modulus := fun c hm => by have := (hc.valid c hm).1; omega
  have hdpos : ∀ c ∈ ds, 0 < c.modulus := fun c hm => by have := (hd.valid c hm).1; omega
  have heven : ∀ x < (n+1)/2, 2*x+0<n := by intro x hx; omega
  have hodd : ∀ x < n/2, 2*x+1<n := by intro x hx; omega
  have hexact (upper : Bool) : exactRow n (interleave cs ds) upper := by
    intro x hx hn
    rw [interleave_count hcpos hdpos]
    by_cases he : x%2=0
    · rw [ite_eq_left he]
      have hlim : x/2 < ((n+1)/2 : Nat) := by omega
      cases upper
      · exact hc.exactLower (x/2) (by omega) hlim
      · exact hc.exactUpper (x/2) (by omega) hlim
    · rw [ite_eq_right he]
      have hlim : x/2 < (n/2 : Nat) := by omega
      cases upper
      · exact hd.exactLower (x/2) (by omega) hlim
      · exact hd.exactUpper (x/2) (by omega) hlim
  have hnear (upper : Bool) (h : NearRow ((n+1)/2) cs upper) :
      NearRow n (interleave cs ds) upper := by
    obtain ⟨c,hc',l,r,hl₀,hl₁,hr₀,hr₁,ha,holeL,holeR⟩ := h
    have hm : along 0 c ∈ interleave cs ds :=
      List.mem_append_left _ (List.mem_map_of_mem hc')
    have hres : (along 0 c).residue upper = 2*c.residue upper := by
      cases upper <;> simp [along,StripClass.residue]
    have hmod : (along 0 c).modulus = 2*c.modulus := rfl
    refine ⟨along 0 c,hm,2*l,2*r,?_,by omega,by omega,?_,?_,?_,?_⟩
    · rw [hres,hmod]
      omega
    · rw [hres,hmod]
      omega
    · rw [hres]
      omega
    · rw [interleave_count hcpos hdpos]
      have hdiv : (2*l)/2=l := by omega
      simp [hdiv,holeL]
    · rw [interleave_count hcpos hdpos]
      have hdiv : (2*r)/2=r := by omega
      simp [hdiv,holeR]
  refine ⟨interleave cs ds,⟨?_,?_,hexact false,hexact true⟩,hnear false hl,hnear true hu,?_⟩
  · rw [interleave,List.map_append,List.nodup_append,along_moduli,along_moduli]
    refine ⟨?_,?_,?_⟩
    · rw [List.Nodup,List.pairwise_map]
      exact hc.distinct.imp (fun hne he => hne (by omega))
    · rw [List.Nodup,List.pairwise_map]
      exact hd.distinct.imp (fun hne he => hne (by omega))
    · intro x hx y hy hxy
      obtain ⟨m,hm,rfl⟩ := List.mem_map.mp hx
      obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hy
      obtain ⟨c,hcm,rfl⟩ := List.mem_map.mp hm
      obtain ⟨d,hdm,rfl⟩ := List.mem_map.mp hk
      exact hsep c hcm d hdm (by omega)
  · intro c hm
    rcases List.mem_append.mp hm with he | he
    · exact along_valid (by decide) hc heven c he
    · exact along_valid (by decide) hd hodd c he
  · intro c hm
    rcases List.mem_append.mp hm with he | he
    · obtain ⟨d,hdm,rfl⟩ := List.mem_map.mp he
      dsimp [along]
      omega
    · obtain ⟨d,hdm,rfl⟩ := List.mem_map.mp he
      dsimp [along]
      omega

end DisjointCovers
