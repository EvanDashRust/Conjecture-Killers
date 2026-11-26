import Mathlib.Tactic

namespace Selfridge
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 1200000
set_option maxRecDepth 24000

/-- Local normalization of the two 3-power classes and the 3-coordinate
of the mixed class. The hypotheses exclude absorption into the class mod 3. -/
theorem third_prime_orbit_three :
    ∀ (a₃ : Fin 3) (a₉ : Fin 9) (a₁₅ : Fin 3),
      a₉.val % 3 ≠ a₃.val → a₁₅ ≠ a₃ →
      ∃ (u : Fin 3) (v : Fin 9), u.val ≠ 0 ∧
        (u.val * a₃.val + v.val) % 3 = 0 ∧
        (u.val * a₁₅.val + v.val) % 3 = 1 ∧
        ((u.val * a₉.val + v.val) % 9 = 1 ∨
         (u.val * a₉.val + v.val) % 9 = 2) := by decide +kernel

/-- Local normalization at 5. -/
theorem third_prime_orbit_five :
    ∀ (a₅ a₁₅ : Fin 5), a₁₅ ≠ a₅ →
      ∃ (u v : Fin 5), u.val ≠ 0 ∧
        (u.val * a₅.val + v.val) % 5 = 0 ∧
        (u.val * a₁₅.val + v.val) % 5 = 1 := by decide +kernel

/-- Glue the unit residues mod 9 and mod 5, preserving invertibility. -/
theorem third_prime_orbit_unit_glue :
    ∀ (u₉ : Fin 9) (u₅ : Fin 5), u₉.val % 3 ≠ 0 → u₅.val ≠ 0 →
      ∃ u : Fin 45, u.val.Coprime 45 ∧ u.val % 9 = u₉.val ∧
        u.val % 5 = u₅.val := by decide +kernel

/-- Glue both translations on the small head. -/
theorem third_prime_orbit_translation_glue :
    ∀ (v₉ : Fin 9) (v₅ : Fin 5),
      ∃ v : Fin 45, v.val % 9 = v₉.val ∧ v.val % 5 = v₅.val := by decide +kernel

#print axioms third_prime_orbit_three
#print axioms third_prime_orbit_five
#print axioms third_prime_orbit_unit_glue
#print axioms third_prime_orbit_translation_glue

end Selfridge
