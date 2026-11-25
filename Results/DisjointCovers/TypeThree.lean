import NearStrips
import ShiftCounterexample

namespace DisjointCovers

/-- The modulus occupying a point of the strip. -/
def stripLabel (cs : List StripClass) (upper : Bool) (x : Nat) : Nat :=
  ((cs.find? (stripHit upper (x:Int))).map StripClass.modulus).getD 0

private theorem find_covering_class {n x : Nat} {cs : List StripClass} {upper : Bool}
    (h : exactRow n cs upper) (hx : x < n) :
    ∃ c ∈ cs, stripHit upper (x:Int) c ∧ stripLabel cs upper x = c.modulus := by
  have hn := h (x:Int) (by omega) (by omega)
  have hpos : 0 < cs.countP (stripHit upper (x:Int)) := by omega
  have hf := List.find?_isSome.mpr (List.countP_pos_iff.mp hpos)
  cases he : cs.find? (stripHit upper (x:Int)) with
  | none => simp [he] at hf
  | some c =>
    exact ⟨c, List.mem_of_find?_eq_some he, List.find?_some he, by simp [stripLabel,he]⟩

private theorem same_modulus_same_class {cs : List StripClass} {a b : StripClass}
    (hd : (cs.map StripClass.modulus).Nodup) (ha : a ∈ cs) (hb : b ∈ cs)
    (he : a.modulus = b.modulus) : a = b := by
  induction cs with
  | nil => simp at ha
  | cons c cs ih =>
    rw [List.map_cons,List.nodup_cons] at hd
    rcases List.mem_cons.mp ha with rfl | hat
    · rcases List.mem_cons.mp hb with rfl | hbt
      · rfl
      · exact False.elim (hd.1 (List.mem_map.mpr ⟨b,hbt,he.symm⟩))
    · rcases List.mem_cons.mp hb with rfl | hbt
      · exact False.elim (hd.1 (List.mem_map.mpr ⟨a,hat,he⟩))
      · exact ih hd.2 hat hbt

private theorem only_one_hit {p : StripClass → Bool} {cs : List StripClass} {a b : StripClass}
    (h : cs.countP p = 1) (ha : a ∈ cs) (hb : b ∈ cs) (hpa : p a) (hpb : p b) :
    a = b := by
  by_cases he : a = b
  · exact he
  · have hnodup : ([a,b] : List StripClass).Nodup := by simp [List.nodup_cons,he]
    have hsub : [a,b] ⊆ cs.filter p := by
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact List.mem_filter.mpr ⟨ha,hpa⟩
      · have hc' : c = b := by simpa using hc
        subst c
        exact List.mem_filter.mpr ⟨hb,hpb⟩
    have htwo := hnodup.length_le_of_subset hsub
    simp [← List.countP_eq_length_filter,h] at htwo

private theorem label_iff {n x : Nat} {cs : List StripClass} {upper : Bool}
    (he : exactRow n cs upper) (hd : (cs.map StripClass.modulus).Nodup)
    (hx : x<n) {c : StripClass} (hc : c∈cs) :
    stripLabel cs upper x = c.modulus ↔ x % c.modulus = c.residue upper := by
  obtain ⟨d,hdm,hdh,hdl⟩ := find_covering_class he hx
  have nat_hit (e : StripClass) :
      stripHit upper (x:Int) e ↔ x%e.modulus = e.residue upper := by
    simp only [stripHit, decide_eq_true_eq, Int.ofNat_mod_ofNat, Int.natCast_inj]
  constructor
  · intro h
    have hh := same_modulus_same_class hd hdm hc (hdl.symm.trans h)
    subst d
    exact (nat_hit _).mp hdh
  · intro hh
    have hcd := only_one_hit (he (x:Int) (by omega) (by omega)) hc hdm ((nat_hit _).mpr hh) hdh
    rwa [hcd]

theorem Strip.realizes {n : Nat} {cs : List StripClass} (h : Strip n n cs) (hn : 2 ≤ n) :
    TwoRowIRDCS n (stripLabel cs false) (stripLabel cs true) := by
  refine ⟨hn, ?_⟩
  intro m hm
  change 0 < ((List.range n).countP (fun x => decide (stripLabel cs false x = m))) +
      ((List.range n).countP (fun x => decide (stripLabel cs true x = m))) at hm
  have occurs : ∃ x < n, stripLabel cs false x = m ∨ stripLabel cs true x = m := by
    by_cases hp : 0 < (List.range n).countP (fun x => decide (stripLabel cs false x = m))
    · obtain ⟨x,hx,he⟩ := List.countP_pos_iff.mp hp
      exact ⟨x,List.mem_range.mp hx,Or.inl (of_decide_eq_true he)⟩
    · have hq : 0 < (List.range n).countP (fun x => decide (stripLabel cs true x = m)) := by omega
      obtain ⟨x,hx,he⟩ := List.countP_pos_iff.mp hq
      exact ⟨x,List.mem_range.mp hx,Or.inr (of_decide_eq_true he)⟩
  obtain ⟨x,hx,hxlabel⟩ := occurs
  have c_exists : ∃ c ∈ cs, c.modulus = m := by
    rcases hxlabel with hxlabel | hxlabel
    · obtain ⟨c,hc,_,he⟩ := find_covering_class h.exactLower hx
      exact ⟨c,hc,he.symm.trans hxlabel⟩
    · obtain ⟨c,hc,_,he⟩ := find_covering_class h.exactUpper hx
      exact ⟨c,hc,he.symm.trans hxlabel⟩
  obtain ⟨c,hc,rfl⟩ := c_exists
  obtain ⟨hm,hl,hu,hne,hln,hun,htwo⟩ := h.valid c hc
  let b := if c.upper < c.lower then c.lower-c.upper else c.modulus+c.lower-c.upper
  have hb₀ : 0 < b := by dsimp [b]; split <;> omega
  have hb₁ : b < c.modulus := by dsimp [b]; split <;> omega
  have hab : (c.upper+b)%c.modulus = c.lower := by
    have ho : c.upper+b = c.lower ∨ c.upper+b = c.lower+c.modulus := by
      dsimp [b]
      split <;> omega
    rcases ho with he | he
    · rw [he,Nat.mod_eq_of_lt hl]
    · rw [he,Nat.add_mod_right,Nat.mod_eq_of_lt hl]
  have hmod (y : Nat) : (y+b)%c.modulus = c.lower ↔ y%c.modulus = c.upper := by
    constructor
    · intro hey
      have he := Nat.add_mod_eq_add_mod_right (c.modulus-b) (hey.trans hab.symm)
      simpa only [Nat.add_assoc, show b+(c.modulus-b)=c.modulus by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt hu] using he
    · intro hey
      exact (Nat.add_mod_eq_add_mod_right b (hey.trans (Nat.mod_eq_of_lt hu).symm)).trans hab
  have lo (x : Nat) (hx : x<n) :
      stripLabel cs false x = c.modulus ↔ x % c.modulus = c.lower :=
    label_iff h.exactLower h.distinct hx hc
  have up (x : Nat) (hx : x<n) :
      stripLabel cs true x = c.modulus ↔ x % c.modulus = c.upper :=
    label_iff h.exactUpper h.distinct hx hc
  refine ⟨1,b,c.lower,by decide,by omega,hb₀,hb₁,by simp,?_,?_⟩
  · intro x hx
    simp only [Nat.one_mul, Nat.mod_eq_of_lt hl]
    exact ⟨lo x hx,(up x hx).trans (hmod x).symm⟩
  · rcases htwo with htwo | htwo
    · left
      refine ⟨⟨c.lower,hln⟩,⟨c.lower+c.modulus,htwo⟩,⟨c.upper,hun⟩,?_,?_,?_,?_⟩
      · intro he
        have := congrArg Fin.val he
        dsimp at this
        omega
      · exact (lo _ hln).mpr (Nat.mod_eq_of_lt hl)
      · exact (lo _ htwo).mpr (by rw [Nat.add_mod_right,Nat.mod_eq_of_lt hl])
      · exact (up _ hun).mpr (Nat.mod_eq_of_lt hu)
    · right
      refine ⟨⟨c.upper,hun⟩,⟨c.upper+c.modulus,htwo⟩,⟨c.lower,hln⟩,?_,?_,?_,?_⟩
      · intro he
        have := congrArg Fin.val he
        dsimp at this
        omega
      · exact (up _ hun).mpr (Nat.mod_eq_of_lt hu)
      · exact (up _ htwo).mpr (by rw [Nat.add_mod_right,Nat.mod_eq_of_lt hu])
      · exact (lo _ hln).mpr (Nat.mod_eq_of_lt hl)

/-- Affirmative answer to Emanuel's §7.4.1 eventual Type 3 question. Both rows
can be near IRDCS at every width at least 19. -/
theorem emanuel_type_three_from_nineteen (n : Nat) (hn : 19 ≤ n) :
    ∃ cs, Strip n n cs ∧ TwoRowIRDCS n (stripLabel cs false) (stripLabel cs true) ∧
      NearRow n cs false ∧ NearRow n cs true := by
  obtain ⟨cs, hs, hl, hu⟩ := near_strips_from_nineteen n hn
  exact ⟨cs,hs,hs.realizes (by omega),hl,hu⟩

#print axioms emanuel_type_three_from_nineteen
#print axioms near_prevents_completion

end DisjointCovers
