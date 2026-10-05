import GaussianTilt.MomentMapSchauderHolderInterpolation

/-!
# Honest absorption of an initial Hölder bound

An arbitrary admissible bound is not its least possible seminorm. Iterating
a strict improvement and passing to the geometric limit removes the initial
bound without making that unjustified identification.
-/
noncomputable section
open Set Filter
open scoped Topology
namespace GaussianTilt.MomentMapSchauder

/-- Iterated improvement absorbs an arbitrary initial Hölder constant.
The conclusion no longer contains the initial constant. -/
theorem holder_bound_of_half_improvement {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F] {f : E → F} {S : Set E}
    {α Q B : ℝ} (hQ : 0 ≤ Q) (hB : 0 ≤ B)
    (hinitial : ∀ x ∈ S, ∀ y ∈ S, ‖f x - f y‖ ≤ Q * ‖x - y‖ ^ α)
    (himprove : ∀ q : ℝ, 0 ≤ q →
      (∀ x ∈ S, ∀ y ∈ S, ‖f x - f y‖ ≤ q * ‖x - y‖ ^ α) →
      ∀ x ∈ S, ∀ y ∈ S, ‖f x - f y‖ ≤ (q / 2 + B) * ‖x - y‖ ^ α) :
    ∀ x ∈ S, ∀ y ∈ S, ‖f x - f y‖ ≤ (2 * B) * ‖x - y‖ ^ α := by
  let q : ℕ → ℝ := fun k => (1 / 2 : ℝ) ^ k * Q + 2 * B
  have hq : ∀ k, 0 ≤ q k := by intro k; dsimp [q]; positivity
  have hseq : ∀ k : ℕ, ∀ x ∈ S, ∀ y ∈ S,
      ‖f x - f y‖ ≤ q k * ‖x - y‖ ^ α := by
    intro k
    induction k with
    | zero =>
      intro x hx y hy
      apply (hinitial x hx y hy).trans
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (norm_nonneg _) _)
      dsimp [q]
      nlinarith
    | succ k ih =>
      have he : q k / 2 + B = q (k + 1) := by
        dsimp [q]
        rw [pow_succ]
        ring
      simpa only [he] using himprove (q k) (hq k) ih
  intro x hx y hy
  have ht : Tendsto (fun k : ℕ => q k * ‖x - y‖ ^ α) atTop (𝓝 ((2 * B) * ‖x - y‖ ^ α)) := by
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    simpa only [q, zero_mul, zero_add] using ((hp.mul_const Q).add_const (2 * B)).mul_const (‖x - y‖ ^ α)
  exact ge_of_tendsto' ht (fun k => hseq k x hx y hy)

end GaussianTilt.MomentMapSchauder
