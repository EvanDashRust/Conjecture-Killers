/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Finset.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Algebra.Ring.Int.Parity

/-!
# Unique Crystal Components

*Reference:* [arxiv/1601.03081](https://arxiv.org/abs/1601.03081)
**The Biharmonic mean**
by *Marco Abrate, Stefano Barbero, Umberto Cerruti, Nadir Murru*
-/

@[expose] public section

namespace Arxiv.«1601.03081»

/--
An odd number $n$ is called a crystal if $n = ab$, with $a, b > 1$
and $B(a, b) ∈ ℕ$, where $B(a, b) := ((a + b)^2 + (a b + 1)^2) / (2 (a + 1) (b + 1))$.
-/
def IsCrystalWithComponents (n a b : ℕ) : Prop :=
  Odd n ∧ 1 < a ∧ 1 < b ∧ n = a * b ∧ 2 * (a + 1) * (b + 1) ∣ (a + b)^2 + (a * b + 1)^2

theorem isCrystalWithComponents_35_5_7 : IsCrystalWithComponents 35 5 7 := by
  norm_num [IsCrystalWithComponents]
  exact ⟨17, rfl⟩

/-- The $B \iff P$ divisibility equivalence from Proposition 1. Oddness of $a$ suffices. -/
theorem biharmonic_dvd_iff_product (a b : ℕ) (ha : Odd a) :
    2 * (a + 1) * (b + 1) ∣ (a + b)^2 + (a * b + 1)^2 ↔
      (a + 1) * (b + 1) ∣ (a + b) * (a * b + 1) := by
  obtain ⟨k, hk⟩ := ha
  have hden : 2 * (a + 1) * (b + 1) ∣ ((a + 1) * (b + 1))^2 := by
    refine ⟨(k + 1) * (b + 1), ?_⟩
    rw [hk]
    grind
  have hid : (a + b)^2 + (a * b + 1)^2 + 2 * ((a + b) * (a * b + 1)) =
      ((a + 1) * (b + 1))^2 := by grind
  have hd : 2 * (a + 1) * (b + 1) ∣
      (a + b)^2 + (a * b + 1)^2 + 2 * ((a + b) * (a * b + 1)) := hid ▸ hden
  calc
    _ ↔ 2 * (a + 1) * (b + 1) ∣ 2 * ((a + b) * (a * b + 1)) :=
      ⟨fun h => (Nat.dvd_add_iff_right h).mpr hd,
        fun h => (Nat.dvd_add_iff_left h).mpr hd⟩
    _ ↔ _ := by rw [Nat.mul_assoc, Nat.mul_dvd_mul_iff_left (by decide : 0 < 2)]

/-- The $P \iff Q$ divisibility equivalence from Proposition 1. -/
theorem product_dvd_iff_sum_sq (a b : ℕ) :
    (a + 1) * (b + 1) ∣ (a + b) * (a * b + 1) ↔
      (a + 1) * (b + 1) ∣ (a + b)^2 := by
  have hd : (a + 1) * (b + 1) ∣ (a + b)^2 + (a + b) * (a * b + 1) := by
    have hid : (a + b)^2 + (a + b) * (a * b + 1) =
        (a + b) * ((a + 1) * (b + 1)) := by grind
    rw [hid]
    exact dvd_mul_left _ _
  exact ⟨fun h => (Nat.dvd_add_iff_left h).mpr hd,
    fun h => (Nat.dvd_add_iff_right h).mpr hd⟩

/-- The $P \iff F$ divisibility equivalence from Proposition 1. -/
theorem product_dvd_iff_mul_sq (a b : ℕ) :
    (a + 1) * (b + 1) ∣ (a + b) * (a * b + 1) ↔
      (a + 1) * (b + 1) ∣ (a * b + 1)^2 := by
  have hd : (a + 1) * (b + 1) ∣ (a * b + 1)^2 + (a + b) * (a * b + 1) := by
    have hid : (a * b + 1)^2 + (a + b) * (a * b + 1) =
        (a * b + 1) * ((a + 1) * (b + 1)) := by grind
    rw [hid]
    exact dvd_mul_left _ _
  exact ⟨fun h => (Nat.dvd_add_iff_left h).mpr hd,
    fun h => (Nat.dvd_add_iff_right h).mpr hd⟩

/-- Crystal components satisfy the equivalent $P$ divisibility condition of Proposition 1. -/
theorem isCrystalWithComponents_iff_product_dvd (n a b : ℕ) :
    IsCrystalWithComponents n a b ↔
      Odd n ∧ 1 < a ∧ 1 < b ∧ n = a * b ∧
        (a + 1) * (b + 1) ∣ (a + b) * (a * b + 1) := by
  unfold IsCrystalWithComponents
  refine and_congr_right fun hn => and_congr_right fun _ => and_congr_right fun _ => ?_
  refine and_congr_right fun hab => ?_
  exact biharmonic_dvd_iff_product a b (Nat.Odd.of_mul_left (hab ▸ hn))

/-- Crystal components satisfy the equivalent $Q$ divisibility condition of Proposition 1. -/
theorem isCrystalWithComponents_iff_sum_sq_dvd (n a b : ℕ) :
    IsCrystalWithComponents n a b ↔
      Odd n ∧ 1 < a ∧ 1 < b ∧ n = a * b ∧ (a + 1) * (b + 1) ∣ (a + b)^2 := by
  rw [isCrystalWithComponents_iff_product_dvd, product_dvd_iff_sum_sq]

/-- Crystal components satisfy the equivalent $F$ divisibility condition of Proposition 1. -/
theorem isCrystalWithComponents_iff_mul_sq_dvd (n a b : ℕ) :
    IsCrystalWithComponents n a b ↔
      Odd n ∧ 1 < a ∧ 1 < b ∧ n = a * b ∧ (a + 1) * (b + 1) ∣ (a * b + 1)^2 := by
  rw [isCrystalWithComponents_iff_product_dvd, product_dvd_iff_mul_sq]

end Arxiv.«1601.03081»
