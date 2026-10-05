import GaussianTilt.MomentMapSchauderInterpolation
import GaussianTilt.MomentMapCampanatoJets

/-!
# Hessian interpolation from actual Taylor approximation

The actual second Fréchet derivative is converted by the real Riesz isometry
to the derivative of the gradient. Taylor remainder and quadratic coefficient
extraction then yield the interior interpolation bound needed for freezing.
-/
noncomputable section
open Set InnerProductSpace
open scoped ContDiff BigOperators Gradient
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapRegularity

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The Hessian as an operator on the Euclidean tangent space. -/
def frechetHessian (u : E → ℝ) (x : E) : E →L[ℝ] E :=
  continuousLinearMapOfBilin (fderiv ℝ (fderiv ℝ u) x)

@[simp] lemma inner_frechetHessian (u : E → ℝ) (x v w : E) :
    inner ℝ (frechetHessian u x v) w = fderiv ℝ (fderiv ℝ u) x v w :=
  continuousLinearMapOfBilin_apply _ v w

lemma norm_frechetHessian (u : E → ℝ) (x : E) :
    ‖frechetHessian u x‖ = ‖fderiv ℝ (fderiv ℝ u) x‖ := by
  have he (v : E) : ‖frechetHessian u x v‖ = ‖fderiv ℝ (fderiv ℝ u) x v‖ :=
    (toDual ℝ E).symm.norm_map _
  apply le_antisymm
  · apply (frechetHessian u x).opNorm_le_bound (norm_nonneg (fderiv ℝ (fderiv ℝ u) x))
    intro v
    rw [he]
    exact (fderiv ℝ (fderiv ℝ u) x).le_opNorm v
  · apply (fderiv ℝ (fderiv ℝ u) x).opNorm_le_bound (norm_nonneg (frechetHessian u x))
    intro v
    rw [← he]
    exact (frechetHessian u x).le_opNorm v

/-- The Riesz form of the genuine second derivative is the actual derivative
of the gradient, not an independent chosen matrix. -/
lemma hasFDerivAt_gradient_frechetHessian {u : E → ℝ} (hu : ContDiff ℝ 2 u) (x : E) :
    HasFDerivAt (gradient u) (frechetHessian u x) x := by
  have hDu := ((hu.fderiv_right (m := 1) (by norm_num)).differentiable le_rfl x).hasFDerivAt
  exact ((toDual ℝ E).symm.hasFDerivAt.comp x hDu)

lemma frechetHessian_symmetric {u : E → ℝ} (hu : ContDiff ℝ 2 u) (x v w : E) :
    inner ℝ (frechetHessian u x v) w = inner ℝ v (frechetHessian u x w) := by
  calc
    _ = fderiv ℝ (fderiv ℝ u) x v w := inner_frechetHessian u x v w
    _ = fderiv ℝ (fderiv ℝ u) x w v := (hu.contDiffAt.isSymmSndFDerivAt (by norm_num)) v w
    _ = inner ℝ (frechetHessian u x w) v := (inner_frechetHessian u x w v).symm
    _ = _ := real_inner_comm _ _

lemma inner_gradient_eq_fderiv (u : E → ℝ) (x v : E) :
    inner ℝ (gradient u x) v = fderiv ℝ u x v := toDual_symm_apply

end Hilbert

/-- Interior Hessian interpolation with explicit constants. The small term
is the actual Hessian Hölder modulus times `r^α`; the remaining term depends
only on the function supremum and `r⁻²`. -/
theorem hessian_interpolation_on_closedBall {n : ℕ} {u : E n → ℝ}
    (hu : ContDiff ℝ 2 u) {x : E n} {r U C α : ℝ}
    (hr : 0 < r) (hU : 0 ≤ U) (hC : 0 ≤ C) (hα : 0 ≤ α)
    (hu_bound : ∀ y ∈ Metric.closedBall x r, |u y| ≤ U)
    (hH : ∀ y ∈ Metric.closedBall x r, ∀ z ∈ Metric.closedBall x r,
      ‖fderiv ℝ (fderiv ℝ u) y - fderiv ℝ (fderiv ℝ u) z‖ ≤ C * ‖y - z‖ ^ α) :
    ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ 4 * U / r ^ 2 + 2 * C * r ^ α := by
  let err : ℝ := U + (C / 2) * r ^ α * r ^ 2
  have herr : 0 ≤ err := by dsimp [err]; positivity
  have hjet : ∀ v : E n, ‖v‖ ≤ r →
      |quadraticJet (u x) (gradient u x) 0 (frechetHessian u x) v| ≤ err := by
    intro v hv
    have hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • v ∈ Metric.closedBall x r := by
      intro t ht
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans hv
    have ht := taylor_second_remainder_holder_on hu hC hα hH
      (by simpa using hr.le : x ∈ Metric.closedBall x r) hseg
    have he : u (x + v) - quadraticJet (u x) (gradient u x) 0 (frechetHessian u x) v =
        u (x + v) - u x - fderiv ℝ u x v -
          (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ u) x v v := by
      simp only [quadraticJet, sub_zero, inner_gradient_eq_fderiv, inner_frechetHessian]
      ring
    rw [← he] at ht
    have hvpow : ‖v‖ ^ α ≤ r ^ α := Real.rpow_le_rpow (norm_nonneg _) hv hα
    have hvsq : ‖v‖ ^ 2 ≤ r ^ 2 := sq_le_sq₀ (norm_nonneg _) hr.le |>.mpr hv
    have herror : |u (x + v) - quadraticJet (u x) (gradient u x) 0 (frechetHessian u x) v| ≤
        (C / 2) * r ^ α * r ^ 2 := by
      apply ht.trans
      exact mul_le_mul (mul_le_mul_of_nonneg_left hvpow (by positivity)) hvsq
        (sq_nonneg _) (by positivity)
    have huv := hu_bound (x + v) (by simpa using hseg 1 ⟨by norm_num, le_rfl⟩)
    calc
      _ = |u (x + v) - (u (x + v) - quadraticJet (u x) (gradient u x) 0 (frechetHessian u x) v)| := by
        congr 1
        ring
      _ ≤ |u (x + v)| + |u (x + v) - quadraticJet (u x) (gradient u x) 0 (frechetHessian u x) v| := abs_sub _ _
      _ ≤ err := add_le_add huv herror
  have hb := quadraticJet_hessian_norm_bound (u x) (gradient u x) (frechetHessian u x)
    (frechetHessian_symmetric hu x) hr herr hjet
  rw [norm_frechetHessian] at hb
  apply hb.trans
  dsimp [err]
  have hr2 : r ^ 2 ≠ 0 := pow_ne_zero _ hr.ne'
  apply le_of_eq
  field_simp
  ring

end GaussianTilt.MomentMapSchauder
