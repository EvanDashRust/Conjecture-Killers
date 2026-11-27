import Mathlib.Tactic

namespace Selfridge.SharedHole

/-- Replacing any pattern already inside the retained union preserves all covered words. -/
theorem redundant_replacement {α : Type*} (kept old new : Set α) (ho : old ⊆ kept) :
    kept ∪ old ⊆ kept ∪ new := by
  intro x hx
  rcases hx with hx | hx
  · exact Or.inl hx
  · exact Or.inl (ho hx)

/-- A phase menu with at least two survivors permits a single forbidden value. -/
theorem avoid_one_phase {α : Type*} [DecidableEq α] (live : Finset α) (x : α)
    (h : 2 ≤ live.card) : ∃ y ∈ live, y ≠ x := by
  by_contra! bad
  have hsub : live ⊆ {x} := fun a ha => by simpa using bad a ha
  have := Finset.card_le_card hsub
  simp at this
  omega

/-- Exact algebra for the pair contribution in the both-present case. -/
theorem pair_charge (u v z t a b : ℚ)
    (hh : a + b ≤ 1 + z) :
    a + b - 2*t ≤ (u-t) + (v-t) - min (min (u-t) (v-t)) (u+v-1-z) := by
  have h := min_le_right (min (u-t) (v-t)) (u+v-1-z)
  linarith

/-- If every root receives at least one label and non-singletons need at least two,
    the singleton count follows. -/
theorem singleton_roots (roots singles labels : ℕ) (h : singles ≤ roots)
    (count : singles + 2*(roots-singles) ≤ labels) :
    2*roots-labels ≤ singles := by omega

/-- Holes among horizontal and vertical lines need one individually placed rectangle per cell. -/
theorem grid_budget (a b c : ℕ) (ha : a < 7) (hb : b < 11)
    (hc : (7-a)*(11-b) ≤ c) : 17 ≤ a+b+c := by
  have h : (7-a)*(11-b) = 17 - a - b + (6-a)*(10-b) := by
    interval_cases a <;> interval_cases b <;> decide
  omega

#print axioms grid_budget
#print axioms redundant_replacement
#print axioms avoid_one_phase
#print axioms pair_charge
#print axioms singleton_roots

end Selfridge.SharedHole
