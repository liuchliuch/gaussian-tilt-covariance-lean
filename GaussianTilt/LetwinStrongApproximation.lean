import GaussianTilt.LetwinRegularApproximation
import GaussianTilt.MomentMapStrongApproximationWhitening

/-! # Variance limits for genuinely strongly convex regular targets

The vanishing positive quadratic tilt strengthens the approximating target,
without changing the limiting law or the scope of the original theorem.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology Matrix.Norms.L2Operator

namespace GaussianTilt.Whitening
variable {n : ℕ}

theorem variance_whitened_strongTruncation_tendsto
    (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : Reference.Space n ↦ ‖x‖ ^ 4) μ)
    (hi : Reference.isotropic μ) (B : Matrix (Fin n) (Fin n) ℝ) :
    Tendsto (fun k ↦ variance (fun x : Reference.Space n ↦ matrixQuadratic B (coordinates x))
      (law (MomentMapApproximation.strongTruncation μ k))) atTop
      (𝓝 (variance (fun x : Reference.Space n ↦ matrixQuadratic B (coordinates x)) μ)) := by
  have hc : Continuous (fun x : Reference.Space n ↦ matrixQuadratic B (coordinates x)) := by
    unfold matrixQuadratic Matrix.mulVec dotProduct coordinates
    fun_prop
  have h₁ := MomentMapApproximation.integral_whitened_strongTruncation_tendsto μ hμ hi
    hc (norm_nonneg B) (quadratic_fourth_growth B)
  have h₂ := MomentMapApproximation.integral_whitened_strongTruncation_tendsto μ hμ hi
    (hc.pow 2) (sq_nonneg ‖B‖) (quadratic_square_fourth_growth B)
  rw [variance_eq_sub (quadratic_memLp_of_fourth hμ B)]
  apply (h₂.sub (h₁.pow 2)).congr'
  exact Eventually.of_forall (fun k ↦ (variance_eq_sub (Paouris.compact_memLp_continuous
    (law (MomentMapApproximation.strongTruncation μ k))
    (law_compactlySupported (MomentMapApproximation.strongTruncation_compactlySupported μ k)) hc 2)).symm)

end GaussianTilt.Whitening
