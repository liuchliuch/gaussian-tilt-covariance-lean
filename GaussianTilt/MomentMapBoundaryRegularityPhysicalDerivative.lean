import GaussianTilt.MomentMapBoundaryRegularityFiniteCover
import GaussianTilt.MomentMapBoundaryRegularityChartPullbackAlgebra

/-! # Physical operator-norm bounds from actual raw-coordinate derivatives -/
noncomputable section
set_option maxHeartbeats 2000000
open Set Filter
open scoped Topology ContDiff BigOperators
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

/-- The inverse-radius bounds on the literal raw partial derivatives imply
the physical Fréchet-derivative bound used by the global gluing theorem. -/
theorem scaled_physical_fderiv_norm_bound {f : CoordinateSpace n → ℝ} {x : E n}
    (hf : DifferentiableAt ℝ f (coordinateEquiv n x)) {r K : ℝ}
    (hr : 0 ≤ r) (hK : 0 ≤ K)
    (hpartial : ∀ i, r*|coordinateDerivative i f (coordinateEquiv n x)| ≤ K) :
    r*‖fderiv ℝ (f ∘ coordinateEquiv n) x‖ ≤ (n:ℝ)*K := by
  have hb : ‖r • fderiv ℝ (f ∘ coordinateEquiv n) x‖ ≤ (n:ℝ)*K := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    rw [ContinuousLinearMap.smul_apply,norm_smul,Real.norm_of_nonneg hr]
    rw [fderiv_comp x hf (coordinateEquiv n).differentiableAt,(coordinateEquiv n).fderiv]
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe]
    rw [fderiv_apply_eq_sum_coordinates,Real.norm_eq_abs]
    calc
      _ ≤ r*(∑ i, |coordinateEquiv n v i*coordinateDerivative i f (coordinateEquiv n x)|) :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hr
      _ = ∑ i, |coordinateEquiv n v i| *(r*|coordinateDerivative i f (coordinateEquiv n x)|) := by
        simp only [Finset.mul_sum,abs_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ ∑ _i : Fin n, ‖v‖*K := by
        apply Finset.sum_le_sum
        intro i _
        have hvi : |coordinateEquiv n v i| ≤ ‖v‖ := by
          simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v i
        exact mul_le_mul hvi (hpartial i) (by positivity) (norm_nonneg _)
      _ = _ := by simp; ring
  simpa only [norm_smul,Real.norm_of_nonneg hr] using hb

end GaussianTilt.MomentMapRegularity
