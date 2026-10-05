import GaussianTilt.MomentMapHolderSegments

/-! Actual segment integration is continuous even in the uniform norm. -/
noncomputable section
open Set MeasureTheory
open scoped Topology BoundedContinuousFunction
namespace GaussianTilt.HolderSpace
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma continuous_segmentValueIntegrand {S : Set E} (hS : Convex ℝ S)
    (D : (S →ᵇ (E →L[ℝ] F))) (x y : S) :
    Continuous (fun t : ℝ => D (segmentPoint hS x y t) ((y : E) - x)) :=
  ((D).continuous.comp (continuous_segmentPoint hS x y)).clm_apply continuous_const

def segmentValueIntegralLinear {S : Set E} (hS : Convex ℝ S) (x y : S) :
    (S →ᵇ (E →L[ℝ] F)) →ₗ[ℝ] F where
  toFun D := ∫ t in (0 : ℝ)..1, D (segmentPoint hS x y t) ((y : E) - x)
  map_add' D G := by
    simp only [map_add, BoundedContinuousFunction.add_apply, ContinuousLinearMap.add_apply]
    exact intervalIntegral.integral_add
      ((continuous_segmentValueIntegrand hS D x y).intervalIntegrable 0 1)
      ((continuous_segmentValueIntegrand hS G x y).intervalIntegrable 0 1)
  map_smul' c D := by
    simp only [map_smul, BoundedContinuousFunction.smul_apply, ContinuousLinearMap.smul_apply,
      RingHom.id_apply]
    exact intervalIntegral.integral_smul c _

lemma segmentValueIntegralLinear_norm_bound {S : Set E} (hS : Convex ℝ S) (x y : S)
    (D : (S →ᵇ (E →L[ℝ] F))) :
    ‖segmentValueIntegralLinear hS x y D‖ ≤ ‖(y : E) - x‖ * ‖D‖ := by
  have hbound : ∀ t ∈ uIoc (0 : ℝ) 1,
      ‖D (segmentPoint hS x y t) ((y : E) - x)‖ ≤ ‖D‖ * ‖(y : E) - x‖ := by
    intro t _
    exact ((D (segmentPoint hS x y t)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (D.norm_coe_le_norm _) (norm_nonneg _))
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  change ‖∫ t in (0 : ℝ)..1, D (segmentPoint hS x y t) ((y : E) - x)‖ ≤ _
  simpa only [sub_zero, abs_one, mul_one, one_mul, mul_comm] using hi

/-- Integration along the actual segment is a bounded linear map, so the
FTC compatibility identities define closed linear conditions. -/
def segmentValueIntegral {S : Set E} (hS : Convex ℝ S) (x y : S) :
    (S →ᵇ (E →L[ℝ] F)) →L[ℝ] F :=
  LinearMap.mkContinuous (𝕜 := ℝ) (E := (S →ᵇ (E →L[ℝ] F))) (F := F)
    (segmentValueIntegralLinear (F := F) hS x y) ‖(y : E) - x‖
    (segmentValueIntegralLinear_norm_bound (F := F) hS x y)

@[simp] lemma segmentValueIntegral_apply {S : Set E} (hS : Convex ℝ S) (x y : S)
    (D : (S →ᵇ (E →L[ℝ] F))) :
    segmentValueIntegral hS x y D =
      ∫ t in (0 : ℝ)..1, D (segmentPoint hS x y t) ((y : E) - x) := rfl


@[simp] lemma segmentValueIntegral_value {S : Set E} (hS : Convex ℝ S) (α : ℝ) (x y : S)
    (D : Space S (E →L[ℝ] F) α) :
    segmentValueIntegral hS x y (value S (E →L[ℝ] F) α D) = segmentIntegral hS α x y D := rfl

end GaussianTilt.HolderSpace
