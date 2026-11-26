import Mathlib.Tactic
import Mathlib.Data.Fintype.BigOperators

open scoped BigOperators

namespace Selfridge

variable {S I : Type} [Fintype S] [DecidableEq S]
abbrev Weights (I : Type) := I → ℝ

private def selected (s : S) : List (S × Weights I) → Weights I
  | [] => 0
  | (t, v) :: rest => selected s rest + if s = t then v else 0

private def total : List (S × Weights I) → Weights I
  | [] => 0
  | (_, v) :: rest => total rest + v

omit [Fintype S] in
private theorem selected_le_total (s : S) (l : List (S × Weights I))
    (nonneg : ∀ c ∈ l, 0 ≤ c.2) : selected s l ≤ total l := by
  induction l with
  | nil => simp [selected, total]
  | cons c rest ih =>
    have hrest := ih (fun i hi => nonneg i (List.mem_cons_of_mem c hi))
    have hc := nonneg c (by simp)
    simp only [selected, total]
    split <;> gcongr

/-- Aligning all target values maximizes this upper bound for an increasing
function with increasing differences. The coordinate need not be uniform. -/
theorem align_coordinate (w : S → ℝ) (w_nonneg : ∀ s, 0 ≤ w s)
    (w_mass : ∑ s, w s = 1) (cap : ℝ) (w_cap : ∀ s, w s ≤ cap)
    (F : Weights I → ℝ) (F_mono : Monotone F)
    (F_diff : ∀ ⦃x y c : Weights I⦄, x ≤ y → 0 ≤ c →
      F (x + c) - F x ≤ F (y + c) - F y)
    (base : Weights I) (l : List (S × Weights I)) (nonneg : ∀ c ∈ l, 0 ≤ c.2) :
    ∑ s, w s * F (base + selected s l) ≤
      F base + cap * (F (base + total l) - F base) := by
  induction l with
  | nil => simp [selected, total, ← Finset.sum_mul, w_mass]
  | cons c rest ih =>
    have hc := nonneg c (by simp)
    have hh : ∀ i ∈ rest, 0 ≤ i.2 := fun i hi => nonneg i (List.mem_cons_of_mem c hi)
    let inc := F (base + total rest + c.2) - F (base + total rest)
    have hinc : 0 ≤ inc := sub_nonneg.mpr (F_mono (le_add_of_nonneg_right hc))
    have step (s : S) :
        w s * F (base + selected s (c :: rest)) ≤
          w s * F (base + selected s rest) + if s = c.1 then w s * inc else 0 := by
      by_cases he : s = c.1
      · subst s
        simp only [selected, ite_true, ← add_assoc]
        have hs : base + selected c.1 rest ≤ base + total rest :=
          add_le_add_right (selected_le_total c.1 rest hh) base
        have df := F_diff hs hc
        have hd := mul_le_mul_of_nonneg_left df (w_nonneg c.1)
        dsimp [inc]
        linarith only [hd]
      · simp [selected, he]
    calc
      _ ≤ ∑ s, (w s * F (base + selected s rest) + if s = c.1 then w s * inc else 0) :=
        Finset.sum_le_sum (fun s _ => step s)
      _ = (∑ s, w s * F (base + selected s rest)) + w c.1 * inc := by
        rw [Finset.sum_add_distrib]
        simp
      _ ≤ (F base + cap * (F (base + total rest) - F base)) + cap * inc :=
        add_le_add (ih hh) (mul_le_mul_of_nonneg_right (w_cap c.1) hinc)
      _ = _ := by simp only [total, ← add_assoc, inc]; ring

#print axioms align_coordinate
end Selfridge
