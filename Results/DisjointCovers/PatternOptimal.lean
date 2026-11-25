import PatternCertificates

namespace DisjointCovers

private def points (n : Nat) : List Nat := (List.range n).map (·+1)

private theorem mem_points {n x : Nat} : x ∈ points n ↔ 1 ≤ x ∧ x ≤ n := by
  simp only [points, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨y, hy, rfl⟩
    omega
  · intro h
    exact ⟨x-1, by omega, by omega⟩

private theorem two_hits {p : α → Bool} {a b : α} {xs : List α}
    (ha : a ∈ xs) (hb : b ∈ xs) (hab : a ≠ b) (hpa : p a) (hpb : p b) :
    2 ≤ xs.countP p := by
  induction xs with
  | nil => simp at ha
  | cons c xs ih =>
    rcases List.mem_cons.mp ha with rfl | hat
    · have hbt := (List.mem_cons.mp hb).resolve_left (Ne.symm hab)
      have hpos := List.countP_pos_iff.mpr ⟨b, hbt, hpb⟩
      rw [List.countP_cons_of_pos hpa]
      omega
    · rcases List.mem_cons.mp hb with rfl | hbt
      · have hpos := List.countP_pos_iff.mpr ⟨a, hat, hpa⟩
        rw [List.countP_cons_of_pos hpb]
        omega
      · have htail := ih hat hbt
        rw [List.countP_cons]
        omega

private theorem moduli_distinct {cs : List Class} {a b : Class}
    (hd : (cs.map Prod.fst).Nodup) (ha : a ∈ cs) (hb : b ∈ cs) (hne : a ≠ b) :
    a.1 ≠ b.1 := by
  induction cs with
  | nil => simp at ha
  | cons c cs ih =>
    rw [List.map_cons, List.nodup_cons] at hd
    rcases List.mem_cons.mp ha with rfl | hat
    · have hbt := (List.mem_cons.mp hb).resolve_left (Ne.symm hne)
      intro he
      exact hd.1 (List.mem_map.mpr ⟨b, hbt, he.symm⟩)
    · rcases List.mem_cons.mp hb with rfl | hbt
      · intro he
        exact hd.1 (List.mem_map.mpr ⟨a, hat, he⟩)
      · exact ih hd.2 hat hbt

private def compatible (n : Nat) (a b : Class) : Bool :=
  decide (a.1 ≠ b.1) && (points n).all (fun x => !(hit x a && hit x b))

private theorem compatible_of_cover {n : Nat} {cs : List Class} (hc : IntervalCover 2 n cs)
    {a b : Class} (ha : a ∈ cs) (hb : b ∈ cs) (hne : a ≠ b) :
    compatible n a b = true := by
  simp only [compatible, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨moduli_distinct hc.1 ha hb hne, ?_⟩
  intro x hx
  obtain ⟨hx₁, hx₂⟩ := mem_points.mp hx
  cases he : hit x a <;> cases hf : hit x b <;> try rfl
  have htwo := two_hits ha hb hne he hf
  have hone := hc.2.2 x hx₁ hx₂
  omega

private def candidates (n : Nat) : List Class :=
  (List.range (n+1)).flatMap fun m =>
    ((List.range m).map fun a => (m,a)).filter fun c =>
      decide (2 ≤ c.1 ∧ 2 ≤ (points n).countP fun x => hit x c)

private theorem mem_candidates {n : Nat} {cs : List Class} (hc : IntervalCover 2 n cs)
    {c : Class} (hm : c ∈ cs) : c ∈ candidates n := by
  obtain ⟨hmin, hnorm, x, y, hx, hxy, hy, hxc, hyc⟩ := hc.2.1 c hm
  have hdiv := Nat.sub_mod_eq_zero_of_mod_eq (hyc.trans hxc.symm)
  have hbound : c.1 ≤ n := by
    by_cases hn : c.1 ≤ n
    · exact hn
    · have hgap : y-x < c.1 := by omega
      rw [Nat.mod_eq_of_lt hgap] at hdiv
      omega
  have htwo : 2 ≤ (points n).countP (fun j => hit j c) :=
    two_hits (mem_points.mpr ⟨hx, by omega⟩) (mem_points.mpr ⟨by omega, hy⟩)
      (by omega) (by simp [hit, hxc]) (by simp [hit, hyc])
  exact List.mem_flatMap.mpr ⟨c.1, List.mem_range.mpr (by omega),
    List.mem_filter.mpr ⟨List.mem_map.mpr ⟨c.2, List.mem_range.mpr hnorm, by cases c; rfl⟩,
      decide_eq_true ⟨hmin, htwo⟩⟩⟩

/-- Try all compatible extensions at the first uncovered point. -/
private def search (n : Nat) (pool : List Class) : List Nat → List Class → Bool
  | [], _ => true
  | x :: xs, chosen =>
    if chosen.any (hit x) then
      search n pool xs chosen
    else
      pool.any fun c =>
        hit x c && chosen.all (compatible n c) && search n pool xs (c :: chosen)

private theorem search_complete {n : Nat} {cs : List Class} (hc : IntervalCover 2 n cs)
    {xs : List Nat} (hxs : ∀ x ∈ xs, x ∈ points n) {chosen : List Class}
    (hchosen : ∀ c ∈ chosen, c ∈ cs) :
    search n (candidates n) xs chosen = true := by
  induction xs generalizing chosen with
  | nil => rfl
  | cons x xs ih =>
    have htail : ∀ y ∈ xs, y ∈ points n := fun y hy => hxs y (List.mem_cons_of_mem x hy)
    rw [search]
    split
    · exact ih htail hchosen
    · rename_i hn
      obtain ⟨hx₁, hx₂⟩ := mem_points.mp (hxs x (List.mem_cons_self ..))
      have hpos : 0 < cs.countP (hit x) := by rw [hc.2.2 x hx₁ hx₂]; decide
      obtain ⟨c, hc₁, hc₂⟩ := List.countP_pos_iff.mp hpos
      have hnew : c ∉ chosen := fun hm => hn (List.any_eq_true.mpr ⟨c, hm, hc₂⟩)
      refine List.any_eq_true.mpr ⟨c, mem_candidates hc hc₁, ?_⟩
      simp only [Bool.and_eq_true]
      refine ⟨⟨hc₂, List.all_eq_true.mpr (fun d hd => ?_)⟩, ?_⟩
      · exact compatible_of_cover hc hc₁ (hchosen d hd) (fun e => hnew (e ▸ hd))
      · exact ih htail (fun d hd => (List.mem_cons.mp hd).elim (fun e => e ▸ hc₁) (hchosen d))

private def anchors (r : Nat) : List Class :=
  [(9,r%9), (6,(r+1)%6), (3,(r+2)%3)]

private theorem anchors_mem {cs : List Class} {x : Nat} (h : PatternAt cs x) :
    ∀ c ∈ anchors (x%18), c ∈ cs := by
  have h9 : x%18%9 = x%9 := by omega
  have h6 : (x%18+1)%6 = (x+1)%6 := by omega
  have h3 : (x%18+2)%3 = (x+2)%3 := by omega
  simp only [anchors, h9, h6, h3, List.mem_cons, List.not_mem_nil, or_false]
  intro c hm
  rcases hm with rfl | rfl | rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem checked_no_24 :
    (List.range 18).all (fun r => !(search 24 (candidates 24) (points 24) (anchors r))) = true := by
  decide

/-- Length 24 is excluded, so 25 is the least threshold. -/
theorem no_nine_six_three_at_24 : ¬ ∃ cs, NineSixThree 24 cs := by
  rintro ⟨cs, _, hc, x, _, _, hp⟩
  have hre : x % 18 ∈ List.range 18 := List.mem_range.mpr (by omega)
  have fail := List.all_eq_true.mp checked_no_24 (x % 18) hre
  have pass := search_complete hc (xs := points 24) (fun _ h => h) (anchors_mem hp)
  simp [pass] at fail

/-- Emanuel's eventual-existence question, with its optimal threshold. -/
theorem optimal_nine_six_three_threshold :
    (∀ n, 25 ≤ n → ∃ cs, NineSixThree n cs) ∧
      (∀ b, (∀ n, b ≤ n → ∃ cs, NineSixThree n cs) → 25 ≤ b) := by
  refine ⟨nine_six_three_from_25, ?_⟩
  intro b hb
  by_cases h : 25 ≤ b
  · exact h
  · exact False.elim (no_nine_six_three_at_24 (hb 24 (by omega)))

#print axioms no_nine_six_three_at_24
#print axioms optimal_nine_six_three_threshold

end DisjointCovers
