import Lean

namespace DisjointCovers

/-- A pair (modulus, canonical residue). The interval is [0,n).
Adding one to every point and residue gives the formulation on [1,n]. -/
abbrev Class := Nat × Nat

def hit (x : Nat) (c : Class) : Bool :=
  decide (x % c.1 = c.2)

/-- Normalized classes that partition the interval, with two or more hits per class.
The first two possible hits of (m,a) are a and a + m. -/
structure Cover (n : Nat) (cs : List Class) : Prop where
  distinct : (cs.map Prod.fst).Nodup
  valid : ∀ c ∈ cs, 2 ≤ c.1 ∧ c.2 < c.1 ∧ c.2 + c.1 < n
  partition : ∀ x, x < n → cs.countP (hit x) = 1

def HasModulus (cs : List Class) (m : Nat) : Prop := m ∈ cs.map Prod.fst

def Separate (cs ds : List Class) : Prop :=
  ∀ m, HasModulus cs m → ¬ HasModulus ds m

def CoprimeToThree (cs : List Class) : Prop :=
  ∀ c ∈ cs, c.1 % 3 ≠ 0

def MultiplesOfThree (cs : List Class) : Prop :=
  ∀ c ∈ cs, c.1 % 3 = 0

/-- Pull a cover back along the map x ↦ s*x + r. -/
def lift (s r : Nat) (cs : List Class) : List Class :=
  cs.map fun c => (s * c.1, s * c.2 + r)

private theorem count_lift {s r x : Nat} {cs : List Class}
    (hs : s = 2 ∨ s = 3) (hr : r < s) :
    (lift s r cs).countP (hit x) =
      if x%s = r then cs.countP (hit (x/s)) else 0 := by
  have hiff (c : Class) :
      x % (s*c.1) = s*c.2+r ↔ x%s = r ∧ (x/s)%c.1 = c.2 := by
    rw [Nat.mod_mul]
    rcases hs with h₂ | h₃ <;> subst s <;> omega
  simp only [lift, List.countP_map]
  by_cases he : x%s = r
  · have hf : (hit x ∘ fun c : Class => (s*c.1, s*c.2+r)) = hit (x/s) := by
      funext c
      simp [hit, hiff, he]
    simp [he, hf]
  · rw [ite_eq_right he, List.countP_eq_zero]
    intro c _
    simp [hit, hiff, he]

private theorem lift_moduli (s r : Nat) (cs : List Class) :
    (lift s r cs).map Prod.fst = (cs.map Prod.fst).map (s * ·) := by
  simp [lift, List.map_map, Function.comp_def]

private theorem lift_nodup {s r n : Nat} {cs : List Class}
    (hs : 0 < s) (h : Cover n cs) : ((lift s r cs).map Prod.fst).Nodup := by
  rw [lift_moduli, List.Nodup, List.pairwise_map]
  exact h.distinct.imp (fun hne heq => hne (Nat.eq_of_mul_eq_mul_left hs heq))

private theorem lift_valid {s r n k : Nat} {cs : List Class}
    (hs : s = 2 ∨ s = 3) (hr : r < s) (h : Cover k cs) (bound : ∀ y < k, s*y+r < n) :
    ∀ c ∈ lift s r cs, 2 ≤ c.1 ∧ c.2 < c.1 ∧ c.2 + c.1 < n := by
  intro c hc
  obtain ⟨⟨m,a⟩, hm, rfl⟩ := List.mem_map.mp hc
  obtain ⟨hm₂, hlt, hhit⟩ := h.valid (m,a) hm
  have hb := bound (a + m) hhit
  dsimp at *
  rcases hs with hs | hs <;> subst s <;> omega

theorem double {n k : Nat} {cs : List Class}
    (h : Cover k cs) (hn : n = 2*k ∨ n = 2*k-1) (hk : 2 ≤ k) (hn' : 3 < n) :
    Cover n ((2,1) :: lift 2 0 cs) := by
  constructor
  · rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, lift_nodup (by decide) h⟩
    intro he
    rw [lift_moduli] at he
    obtain ⟨_, hm, hmul⟩ := List.mem_map.mp he
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hm
    have := (h.valid c hc).1
    dsimp at *
    omega
  · intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨by decide, by decide, hn'⟩
    · exact lift_valid (Or.inl rfl) (by decide) h (fun y hy => by omega) c hc
  · intro x hx
    rw [List.countP_cons, count_lift (Or.inl rfl) (by decide)]
    have he : x % 2 = 0 ∨ x % 2 = 1 := by omega
    obtain hzero | hone := he
    · have hy : x / 2 < k := by omega
      simp [hit, hzero, h.partition _ hy]
    · simp [hit, hone]

theorem double_coprime {cs : List Class} (h : CoprimeToThree cs) :
    CoprimeToThree ((2,1) :: lift 2 0 cs) := by
  intro c hc
  rcases List.mem_cons.mp hc with rfl | hc
  · decide
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    have hh := h d hd
    dsimp at *
    omega

/-- Two residue classes of equal size can be covered independently. The third
residue class is a single congruence. The bounds specify the two interval fibres. -/
theorem triple {n k r₀ r₁ r₂ : Nat} {cs ds : List Class}
    (hc : Cover k cs) (hd : Cover k ds) (hsep : Separate cs ds)
    (hr₀ : r₀ < 3) (hr₁ : r₁ < 3) (hr₂ : r₂ < 3)
    (h01 : r₀ ≠ r₁) (h02 : r₀ ≠ r₂) (h12 : r₁ ≠ r₂) (hsize : r₀ + 3 < n)
    (hb₁ : ∀ y, y < k ↔ 3*y+r₁ < n) (hb₂ : ∀ y, y < k ↔ 3*y+r₂ < n) :
    Cover n ((3,r₀) :: (lift 3 r₁ cs ++ lift 3 r₂ ds)) := by
  constructor
  · rw [List.map_cons, List.nodup_cons, List.map_append, List.nodup_append]
    refine ⟨?_, lift_nodup (by decide) hc, lift_nodup (by decide) hd, ?_⟩
    · rw [List.mem_append, lift_moduli, lift_moduli]
      have noThree {ls : List Class} (h : Cover k ls) :
          3 ∉ (ls.map Prod.fst).map (3 * ·) := by
        intro hx
        obtain ⟨_, hm, he⟩ := List.mem_map.mp hx
        obtain ⟨c, hcl, rfl⟩ := List.mem_map.mp hm
        have := (h.valid c hcl).1
        dsimp at *
        omega
      exact fun h => h.elim (noThree hc) (noThree hd)
    · intro m hmc m' hmd heq
      subst m'
      rw [lift_moduli] at hmc hmd
      obtain ⟨a, ha, he⟩ := List.mem_map.mp hmc
      obtain ⟨b, hb, he'⟩ := List.mem_map.mp hmd
      have hab : a = b := by omega
      exact hsep a ha (hab ▸ hb)
  · intro c hmem
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact ⟨by omega, hr₀, hsize⟩
    · rcases List.mem_append.mp hmem with hmem | hmem
      · exact lift_valid (Or.inr rfl) hr₁ hc (fun y hy => (hb₁ y).mp hy) c hmem
      · exact lift_valid (Or.inr rfl) hr₂ hd (fun y hy => (hb₂ y).mp hy) c hmem
  · intro x hx
    rw [List.countP_cons, List.countP_append, count_lift (Or.inr rfl) hr₁,
      count_lift (Or.inr rfl) hr₂]
    have hmod : x % 3 = r₀ ∨ x % 3 = r₁ ∨ x % 3 = r₂ := by omega
    rcases hmod with he | he | he
    · simp [hit, he, h01, h02]
    · have hy : x/3 < k := (hb₁ _).mpr (by omega)
      simp [hit, he, Ne.symm h01, h12, hc.partition _ hy]
    · have hy : x/3 < k := (hb₂ _).mpr (by omega)
      simp [hit, he, Ne.symm h02, Ne.symm h12, hd.partition _ hy]

theorem triple_multiples {r₀ r₁ r₂ : Nat} {cs ds : List Class} :
    MultiplesOfThree ((3,r₀) :: (lift 3 r₁ cs ++ lift 3 r₂ ds)) := by
  intro c hmem
  rcases List.mem_cons.mp hmem with rfl | hmem
  · change 3 % 3 = 0
    decide
  · rcases List.mem_append.mp hmem with hmem | hmem
    · obtain ⟨d, _, rfl⟩ := List.mem_map.mp hmem
      simp
    · obtain ⟨d, _, rfl⟩ := List.mem_map.mp hmem
      simp

theorem separate_of_three {cs ds : List Class}
    (hc : CoprimeToThree cs) (hd : MultiplesOfThree ds) : Separate cs ds := by
  intro m hm hdm
  obtain ⟨c, hcm, rfl⟩ := List.mem_map.mp hm
  obtain ⟨d, hdm, he⟩ := List.mem_map.mp hdm
  exact hc c hcm (he ▸ hd d hdm)

end DisjointCovers
