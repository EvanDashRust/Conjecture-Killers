# Original verification transcript

This is the preserved successful Lean verification record from November 18, 2026. Publication of this repository is **not** a claim that Lean was rerun during upload. The original project archive is linked from the [research record](https://chatgpt.com/space/page_ba79e98e3cb08191b9cdba48365531e1).

```text
+ lean --version
Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)
+ lake --version
Lake version 5.0.0-src+5045d00 (Lean version 4.34.1)
+ lake exe cache get Mathlib.Combinatorics.Enumerative.Stirling Mathlib.Tactic.Ring Mathlib.Algebra.Order.BigOperators.Group.Finset
Current branch: HEAD
Using cache from origin: (some leanprover-community/mathlib4)
No files to download
Already decompressed 892 file(s)
+ git -C .lake/packages/mathlib rev-parse HEAD
d13f23b723b8a846827a245b89c10fc7d3f11612
++ git -C .lake/packages/mathlib rev-parse HEAD
+ test d13f23b723b8a846827a245b89c10fc7d3f11612 = d13f23b723b8a846827a245b89c10fc7d3f11612
+ lake build
ℹ [897/903] Built GySecond.Ratio (1.1s)
info: GySecond/Ratio.lean:40:0: 'GySecond.prefix_ratio_rec' depends on axioms: [propext, Quot.sound]
✔ [898/903] Built GySecond.Basic (1.5s)
✔ [899/903] Built GySecond.Encoding (1.2s)
✔ [900/903] Built GySecond.Monotone (1.5s)
ℹ [901/903] Built GySecond.Result (1.5s)
info: GySecond/Result.lean:31:0: theorem GySecond.gy_second_kind : ∀ (n p j : ℕ),
  1 ≤ j →
    j ≤ p →
      p ≤ n →
        p.stirlingSecond j * n.stirlingSecond p * (n - 1).stirlingSecond (j - 1) ≤
          (p - 1).stirlingSecond (j - 1) * (n - 1).stirlingSecond (p - 1) * n.stirlingSecond j :=
fun n p j hj hjp hpn =>
  GySecond.of_interior (fun x x_1 x_2 h₁ h₂ h₃ => GySecond.interior_product h₁ h₂ h₃) n p j hj hjp hpn
info: GySecond/Result.lean:32:0: 'GySecond.gy_second_kind' depends on axioms: [propext, Quot.sound]
✔ [902/903] Built GySecond (1.4s)
Build completed successfully (903 jobs).
+ lake env lean Audit.lean
theorem GySecond.gy_second_kind : ∀ (n p j : ℕ),
  1 ≤ j →
    j ≤ p →
      p ≤ n →
        p.stirlingSecond j * n.stirlingSecond p * (n - 1).stirlingSecond (j - 1) ≤
          (p - 1).stirlingSecond (j - 1) * (n - 1).stirlingSecond (p - 1) * n.stirlingSecond j :=
fun n p j hj hjp hpn =>
  GySecond.of_interior (fun x x_1 x_2 h₁ h₂ h₃ => GySecond.interior_product h₁ h₂ h₃) n p j hj hjp hpn
'GySecond.gy_second_kind' depends on axioms: [propext, Quot.sound]
'GySecond.eq_at_p_eq_j' depends on axioms: [propext]
'GySecond.eq_at_p_eq_n' depends on axioms: [propext]
'GySecond.eq_at_j_eq_one' depends on axioms: [propext, Quot.sound]
'GySecond.stirling_pos' depends on axioms: [propext, Quot.sound]
'GySecond.gy_monotone' depends on axioms: [propext, Quot.sound]
```
