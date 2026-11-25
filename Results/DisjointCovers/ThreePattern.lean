import Proof

namespace DisjointCovers

/-- The three points beginning at x are assigned moduli 9, 6, and 3 in order. -/
abbrev PatternAt (cs : List Class) (x : Nat) : Prop :=
  (9, x % 9) ∈ cs ∧ (6, (x+1) % 6) ∈ cs ∧ (3, (x+2) % 3) ∈ cs

/-- Lyman, Morris, and Toomey's Definition 6 on the interval [1,n]. -/
def NineSixThree (n : Nat) (cs : List Class) : Prop :=
  18 ≤ n ∧ IntervalCover 2 n cs ∧ ∃ x, 1 ≤ x ∧ x+2 ≤ n ∧ PatternAt cs x

theorem shift_pattern {n x : Nat} {cs : List Class} (hn : 18 ≤ n)
    (hc : Cover n cs)
    (hx : x+2 < n) (hp : PatternAt cs x) : NineSixThree n (cs.map shift) := by
  refine ⟨hn, to_interval_cover hc (fun c hm => (hc.valid c hm).1),
    x+1, by omega, by omega, ?_⟩
  rcases hp with ⟨h₉, h₆, h₃⟩
  refine ⟨List.mem_map.mpr ⟨(9,x%9), h₉, ?_⟩,
    List.mem_map.mpr ⟨(6,(x+1)%6), h₆, ?_⟩,
    List.mem_map.mpr ⟨(3,(x+2)%3), h₃, ?_⟩⟩
  · simp [shift]
  · simp [shift, Nat.add_assoc]
  · simp [shift, Nat.add_assoc]

private theorem with_two (n : Nat) (hn : 88 ≤ n) :
    ∃ cs, Cover n cs ∧ CoprimeToThree cs ∧ (2,1) ∈ cs := by
  let k := (n+1)/2
  obtain ⟨cs, hc, hcop⟩ := coprime_covers k (by dsimp [k]; omega)
  refine ⟨(2,1) :: lift 2 0 cs, double hc ?_ (by dsimp [k]; omega) (by omega),
    double_coprime hcop, List.mem_cons_self ..⟩
  dsimp [k]
  omega

private theorem triple_pattern {n k a r₀ r₁ r₂ : Nat} {cs ds : List Class}
    (hn : 20 ≤ n) (hc : Cover k cs) (hd : Cover k ds) (hs : Separate cs ds)
    (h₂ : (2,1) ∈ cs) (h₃ : (3,a) ∈ ds)
    (hr₂ : r₂ ≤ 1) (hr₁ : r₁ = r₂+1) (hr₀ : r₀ = (r₂+2)%3)
    (hb₁ : ∀ y, y < k ↔ 3*y+r₁ < n) (hb₂ : ∀ y, y < k ↔ 3*y+r₂ < n) :
    ∃ es, Cover n es ∧ MultiplesOfThree es ∧ ∃ x, x+2 < n ∧ PatternAt es x := by
  let es := (3,r₀) :: (lift 3 r₁ cs ++ lift 3 r₂ ds)
  refine ⟨es, triple hc hd hs (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) hb₁ hb₂, triple_multiples, ?_⟩
  have ha := (hd.valid (3,a) h₃).2.1
  change a < 3 at ha
  let x := if a % 2 = 1 then 3*a+r₂ else 3*a+r₂+9
  have h9 : x % 9 = 3*a+r₂ := by dsimp [x]; split <;> omega
  have h6 : (x+1) % 6 = 3+r₁ := by dsimp [x]; split <;> omega
  have h3 : (x+2) % 3 = r₀ := by dsimp [x]; split <;> omega
  refine ⟨x, ?_, ?_⟩
  · dsimp [x]
    split <;> omega
  · change (9,x%9) ∈ es ∧ (6,(x+1)%6) ∈ es ∧ (3,(x+2)%3) ∈ es
    rw [h9, h6, h3]
    exact ⟨List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map.mpr
        ⟨(3,a), h₃, rfl⟩)),
      List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map.mpr ⟨(2,1), h₂, rfl⟩)),
      List.mem_cons_self ..⟩

/-- The construction for the unbounded range. -/
theorem nine_six_three_from_395 (n : Nat) (hn : 395 ≤ n) : ∃ cs, NineSixThree n cs := by
  let k := (n+1)/3
  have hk : 132 ≤ k := by dsimp [k]; omega
  obtain ⟨cs, hc, hcop, h₂⟩ := with_two k (by omega)
  obtain ⟨ds, hd, hmul, h₃⟩ := multiple_covers_with_three k hk
  obtain ⟨⟨m,a⟩, ha, hm⟩ := List.mem_map.mp h₃
  change m = 3 at hm
  subst m
  have hs := separate_of_three hcop hmul
  have build : ∃ es, Cover n es ∧ MultiplesOfThree es ∧ ∃ x, x+2 < n ∧ PatternAt es x := by
    by_cases h : n % 3 = 1
    · exact triple_pattern (r₀ := 0) (r₁ := 2) (r₂ := 1) (by omega) hc hd hs h₂ ha
        (by decide) (by decide) (by decide)
        (fun y => by dsimp [k]; omega) (fun y => by dsimp [k]; omega)
    · exact triple_pattern (r₀ := 2) (r₁ := 1) (r₂ := 0) (by omega) hc hd hs h₂ ha
        (by decide) (by decide) (by decide)
        (fun y => by dsimp [k]; omega) (fun y => by dsimp [k]; omega)
  obtain ⟨es, he, _, x, hx, hp⟩ := build
  exact ⟨es.map shift, shift_pattern (by omega) he hx hp⟩

end DisjointCovers
