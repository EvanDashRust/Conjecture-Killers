import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! A counterexample to Kališnik and Lešnik, Conjecture 6.3, arXiv:2603.04271v2. -/

namespace SkewMagnitude

open Filter Asymptotics Matrix
open scoped Topology

noncomputable def corners (d r : ℝ) : Fin 4 → ℝ := ![-r, r, d - r, d + r]

theorem corners_strictMono (d r : ℝ) (hr : 0 < r) (hd : 2 * r < d) :
    StrictMono (corners d r) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num [Fin.lt_def] at hij
  all_goals simp [corners]; linarith

noncomputable def similarity (d r : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j => Real.exp (-|corners d r i - corners d r j|)

private def chainMatrix (a b : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, a, a*b, a*b*a; a, 1, b, b*a; a*b, b, 1, a; a*b*a, b*a, a, 1]

private theorem det_chainMatrix (a b : ℝ) :
    (chainMatrix a b).det = (1 - a^2)^2 * (1 - b^2) := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, chainMatrix, Matrix.det_fin_three, Fin.succAbove]
  ring

/-- The four endpoints are those of two disjoint intervals of radius r
centered at 0 and d. The similarity determinant factors along their gaps. -/
theorem det_two_intervals (d r : ℝ) (hr : 0 < r) (hd : 2 * r < d) :
    (similarity d r).det = (1 - Real.exp (-(4*r)))^2 * (1 - Real.exp (-(2*(d-2*r)))) := by
  let a := Real.exp (-(2*r))
  let b := Real.exp (-(d-2*r))
  have hM : similarity d r = chainMatrix a b := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [similarity, corners, chainMatrix, a, b]
    all_goals
      first | rw [abs_of_nonneg (by linarith)] | rw [abs_of_nonpos (by linarith)]
      try simp only [← Real.exp_add]
      congr 1; ring
  have ha : a^2 = Real.exp (-(4*r)) := by
    dsimp only [a]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hb : b^2 = Real.exp (-(2*(d-2*r))) := by
    dsimp only [b]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hM, det_chainMatrix, ha, hb]

theorem normalized_limit (d : ℝ) (hd : 0 < d) :
    Tendsto (fun r => (similarity d r).det / r^2) (𝓝[>] 0)
      (𝓝 (16 * (1 - Real.exp (-(2*d))))) := by
  have hne : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r := self_mem_nhdsWithin
  have hlt : ∀ᶠ r : ℝ in 𝓝[>] 0, r < d / 2 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (gt_mem_nhds (by linarith))
  have hdifferential : HasDerivAt (fun r : ℝ => 1 - Real.exp (-(4*r))) 4 0 := by
    have h := (hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub
      (((hasDerivAt_id (0 : ℝ)).const_mul (-4 : ℝ)).exp)
    norm_num at h
    exact h
  have hquot : Tendsto (fun r : ℝ => (1 - Real.exp (-(4*r)))/r) (𝓝[>] 0) (𝓝 4) := by
    have h := (hasDerivAt_iff_tendsto_slope_zero.mp hdifferential)
    have hf : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] 0 :=
      nhdsWithin_mono _ (fun x hx => ne_of_gt hx)
    simpa [slope, div_eq_mul_inv, mul_comm] using h.mono_left hf
  have hfactor : Tendsto (fun r : ℝ => 1 - Real.exp (-(2*(d-2*r)))) (𝓝[>] 0)
      (𝓝 (1 - Real.exp (-(2*d)))) := by
    have hcont : Continuous (fun r : ℝ => 1 - Real.exp (-(2*(d-2*r)))) := by fun_prop
    have h' := hcont.continuousAt (x := (0 : ℝ))
    simpa only [ContinuousWithinAt, mul_zero, sub_zero] using h'.continuousWithinAt (s := Set.Ioi (0 : ℝ))
  have ht := (hquot.pow 2).mul hfactor
  norm_num at ht
  apply ht.congr'
  filter_upwards [hne, hlt] with r hr hr'
  rw [det_two_intervals d r hr (by linarith)]
  rw [div_pow]
  ring

/-- Conjecture 6.3 fails for every pair of distinct centers on the real line.
For these two intervals the conjecture's k is 2. -/
theorem conjecture63_false (d : ℝ) (hd : 0 < d) :
    ¬ (fun r => (similarity d r).det - 16*r^2) =O[𝓝[>] 0] (fun r => r^3) := by
  intro h
  have hsmall : (fun r : ℝ => r^3) =o[𝓝[>] 0] (fun r => r^2) :=
    (isLittleO_pow_pow (𝕜 := ℝ) (by decide : 2 < 3)).mono nhdsWithin_le_nhds
  have hzero := (h.trans_isLittleO hsmall).tendsto_div_nhds_zero
  have hn : Tendsto (fun r => ((similarity d r).det - 16*r^2) / r^2) (𝓝[>] 0)
      (𝓝 (16 * (1 - Real.exp (-(2*d))) - 16)) := by
    have ht := (normalized_limit d hd).sub tendsto_const_nhds (b := (16 : ℝ))
    apply ht.congr'
    filter_upwards [show ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r from self_mem_nhdsWithin] with r hr
    field_simp
  have he := tendsto_nhds_unique hn hzero
  have hpos := Real.exp_pos (-(2*d))
  linarith

#print axioms corners_strictMono
#print axioms det_two_intervals
#print axioms normalized_limit
#print axioms conjecture63_false

end SkewMagnitude
