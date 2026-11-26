import Mathlib.Tactic

namespace Selfridge.Head

/-- In the intersecting orbit, the overlaps in the two remaining 3-roots imply 11/40. -/
theorem intersecting_orbit (X Y : ℝ) (h₁ : 1/9 ≤ X) (h₂ : X+Y ≤ 1/6) :
    11/40 ≤ (2/3-X-Y)*(3/4)-1/8+X/5+Y/20 := by
  linarith

/-- Two disjoint towers in each coordinate leave the limiting head mass 1/4. -/
theorem nonintersecting_orbit (s t : ℝ) (hs : s ≤ 1/2) (ht : t ≤ 1/4) :
    1/4 ≤ (1-s)*(1-t)-s*t := by
  linarith only [show (1-s)*(1-t)-s*t = 1-s-t by ring, hs, ht]

#print axioms intersecting_orbit
#print axioms nonintersecting_orbit
end Selfridge.Head
