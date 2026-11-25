import Tables

namespace DisjointCovers

/-- A cover avoiding multiples of 3 exists for every length at least 44. -/
theorem coprime_covers (n : Nat) (hn : 44 ≤ n) :
    ∃ cs, Cover n cs ∧ CoprimeToThree cs := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hsmall : n < 88
    · exact coprime_base n hn hsmall
    · let k := (n+1)/2
      obtain ⟨cs, hc, hcop⟩ := ih k (by dsimp [k]; omega) (by dsimp [k]; omega)
      refine ⟨(2,1) :: lift 2 0 cs, double hc ?_ (by dsimp [k]; omega) (by omega),
        double_coprime hcop⟩
      dsimp [k]
      omega

private theorem triple_bound {n r₀ r₁ r₂ : Nat} {cs ds : List Class}
    (hn : 132 ≤ n) (hc : Cover ((n+1)/3) cs) (hd : Cover ((n+1)/3) ds) :
    ∀ c ∈ (3,r₀) :: (lift 3 r₁ cs ++ lift 3 r₂ ds), c.1+2 ≤ n := by
  intro c hm
  rcases List.mem_cons.mp hm with rfl | hm
  · change 5 ≤ n
    omega
  · rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨d, hdmem, rfl⟩ := List.mem_map.mp hm
      have ht := (hc.valid d hdmem).2.2
      change 3*d.1+2 ≤ n
      omega
    · obtain ⟨d, hdmem, rfl⟩ := List.mem_map.mp hm
      have ht := (hd.valid d hdmem).2.2
      change 3*d.1+2 ≤ n
      omega

/-- Two residues modulo 3 have the common fibre size (n+1)/3. -/
private theorem assemble {n : Nat} {cs ds : List Class} (hn : 132 ≤ n)
    (hc : Cover ((n+1)/3) cs) (hd : Cover ((n+1)/3) ds)
    (hsep : Separate cs ds) : ∃ es, Cover n es ∧ MultiplesOfThree es ∧ HasModulus es 3 ∧
      (∀ c ∈ es, c.1+2 ≤ n) := by
  by_cases he : n % 3 = 1
  · refine ⟨(3,0) :: (lift 3 1 cs ++ lift 3 2 ds), ?_, triple_multiples, by simp [HasModulus], triple_bound hn hc hd⟩
    exact triple hc hd hsep (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by omega) (fun y => by omega) (fun y => by omega)
  · refine ⟨(3,2) :: (lift 3 0 cs ++ lift 3 1 ds), ?_, triple_multiples, by simp [HasModulus], triple_bound hn hc hd⟩
    exact triple hc hd hsep (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by omega) (fun y => by omega) (fun y => by omega)

/-- The tripling construction uses modulus 3, and no modulus greater than n-2. -/
theorem multiple_covers_bounded (n : Nat) (hn : 132 ≤ n) :
    ∃ cs, Cover n cs ∧ MultiplesOfThree cs ∧ HasModulus cs 3 ∧
      (∀ c ∈ cs, c.1+2 ≤ n) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    let k := (n+1)/3
    have hk : 44 ≤ k := by dsimp [k]; omega
    by_cases hsmall : k < 132
    · obtain ⟨cs, ds, hc, hd, hsep⟩ := paired_base k hk hsmall
      exact assemble hn hc hd hsep
    · obtain ⟨cs, hc, hcop⟩ := coprime_covers k hk
      obtain ⟨ds, hd, hmul, _, _⟩ := ih k (by dsimp [k]; omega) (by omega)
      exact assemble hn hc hd (separate_of_three hcop hmul)

/-- For every n at least 132, there is a cover using modulus 3 and only multiples of 3. -/
theorem multiple_covers_with_three (n : Nat) (hn : 132 ≤ n) :
    ∃ cs, Cover n cs ∧ MultiplesOfThree cs ∧ HasModulus cs 3 := by
  obtain ⟨cs,hc,hm,hthree,_⟩ := multiple_covers_bounded n hn
  exact ⟨cs,hc,hm,hthree⟩

/-- For every n at least 132, the cover can use only multiples of 3. -/
theorem multiple_covers (n : Nat) (hn : 132 ≤ n) :
    ∃ cs, Cover n cs ∧ MultiplesOfThree cs := by
  obtain ⟨cs, hc, hmul, _⟩ := multiple_covers_with_three n hn
  exact ⟨cs, hc, hmul⟩

theorem covers_from_seventeen (n : Nat) (hn : 17 ≤ n) :
    ∃ cs, Cover n cs ∧ (∀ c ∈ cs, 3 ≤ c.1) := by
  by_cases hsmall : n < 132
  · exact small_base n hn hsmall
  · obtain ⟨cs, hc, hm⟩ := multiple_covers n (by omega)
    refine ⟨cs, hc, ?_⟩
    intro c hmem
    have := (hc.valid c hmem).1
    have := hm c hmem
    omega

/-- Distinct moduli above the given lower bound, exactly one class per point
of [1,n], and at least two points per class. -/
def IntervalCover (minModulus n : Nat) (cs : List Class) : Prop :=
  (cs.map Prod.fst).Nodup ∧
  (∀ c ∈ cs, minModulus ≤ c.1 ∧ c.2 < c.1 ∧
    ∃ x y : Nat, 1 ≤ x ∧ x < y ∧ y ≤ n ∧ x % c.1 = c.2 ∧ y % c.1 = c.2) ∧
  (∀ x : Nat, 1 ≤ x → x ≤ n → cs.countP (hit x) = 1)

/-- Myerson's question excludes modulus 2. -/
abbrev MyersonCover := IntervalCover 3

/-- Translate a residue class forward by one integer. -/
def shift (c : Class) : Class := (c.1, (c.2+1) % c.1)

private theorem hit_shift (c : Class) (x : Nat) (hr : c.2 < c.1) :
    hit (x+1) (shift c) = hit x c := by
  unfold shift hit
  congr 1
  apply propext
  change (x+1) % c.1 = (c.2+1) % c.1 ↔ x % c.1 = c.2
  constructor
  · intro he
    have hm : 1 + (c.1-1) = c.1 := by omega
    have hh := Nat.add_mod_eq_add_mod_right (c.1-1) he
    rw [Nat.add_assoc, Nat.add_assoc, hm, Nat.add_mod_right, Nat.add_mod_right,
      Nat.mod_eq_of_lt hr] at hh
    exact hh
  · intro he
    exact Nat.add_mod_eq_add_mod_right 1 (he.trans (Nat.mod_eq_of_lt hr).symm)

/-- Translate a cover on [0,n) to the published convention on [1,n]. -/
theorem to_interval_cover {minModulus n : Nat} {cs : List Class} (hc : Cover n cs)
    (hm : ∀ c ∈ cs, minModulus ≤ c.1) : IntervalCover minModulus n (cs.map shift) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [List.map_map, Function.comp_def, shift] using hc.distinct
  · intro d hd
    obtain ⟨c, hmem, rfl⟩ := List.mem_map.mp hd
    obtain ⟨hmin, hcanon, hbound⟩ := hc.valid c hmem
    change minModulus ≤ c.1 ∧ (c.2 + 1) % c.1 < c.1 ∧ _
    refine ⟨hm c hmem, Nat.mod_lt _ (by omega), c.2+1, c.2+c.1+1,
      by omega, by omega, by omega, rfl, ?_⟩
    change (c.2+c.1+1) % c.1 = (c.2+1) % c.1
    rw [Nat.add_right_comm, Nat.add_mod_right]
  · intro x hpos htop
    let y := x-1
    have hxy : x = y+1 := by dsimp [y]; omega
    have hy : y < n := by omega
    rw [hxy, List.countP_map]
    have agree (c : Class) (hmem : c ∈ cs) : (hit (y+1) ∘ shift) c ↔ hit y c := by
      change hit (y+1) (shift c) ↔ hit y c
      rw [hit_shift c y (hc.valid c hmem).2.1]
    rw [List.countP_congr agree]
    exact hc.partition y hy

/-- Affirmative answer to Gerry Myerson's second question on MathOverflow. -/
theorem myerson_second_question (n : Nat) (hn : 17 ≤ n) :
    ∃ cs, MyersonCover n cs := by
  obtain ⟨cs, hc, hm⟩ := covers_from_seventeen n hn
  exact ⟨cs.map shift, to_interval_cover hc hm⟩

#print axioms myerson_second_question
#print axioms multiple_covers

end DisjointCovers
