import GaussianTilt.MomentMapHolderLinear

/-! # Actual bounded segment-integration maps on Hölder fields -/
noncomputable section
open Set MeasureTheory
open scoped Topology BoundedContinuousFunction
namespace GaussianTilt.HolderSpace
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def clampUnit (t : ℝ) : ℝ := max 0 (min 1 t)

lemma clampUnit_mem (t : ℝ) : clampUnit t ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

lemma clampUnit_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : clampUnit t = t := by
  simp only [clampUnit, min_eq_right ht.2, max_eq_right ht.1]

def segmentPoint {S : Set E} (hS : Convex ℝ S) (x y : S) (t : ℝ) : S :=
  ⟨(1 - clampUnit t) • (x : E) + clampUnit t • (y : E),
    hS x.2 y.2 (sub_nonneg.mpr (clampUnit_mem t).2) (clampUnit_mem t).1 (sub_add_cancel _ _)⟩

lemma continuous_segmentPoint {S : Set E} (hS : Convex ℝ S) (x y : S) :
    Continuous (segmentPoint hS x y) := by
  apply Continuous.subtype_mk
  unfold clampUnit
  fun_prop

lemma segmentPoint_eq {S : Set E} (hS : Convex ℝ S) (x y : S) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    (segmentPoint hS x y t : E) = (x : E) + t • ((y : E) - x) := by
  simp only [segmentPoint, clampUnit_eq ht]
  module

lemma continuous_segmentIntegrand {S : Set E} (hS : Convex ℝ S) (α : ℝ)
    (D : Space S (E →L[ℝ] F) α) (x y : S) :
    Continuous (fun t : ℝ => value S (E →L[ℝ] F) α D (segmentPoint hS x y t) ((y : E) - x)) :=
  ((value S (E →L[ℝ] F) α D).continuous.comp (continuous_segmentPoint hS x y)).clm_apply continuous_const

def segmentIntegralLinear {S : Set E} (hS : Convex ℝ S) (α : ℝ) (x y : S) :
    Space S (E →L[ℝ] F) α →ₗ[ℝ] F where
  toFun D := ∫ t in (0 : ℝ)..1, value S (E →L[ℝ] F) α D (segmentPoint hS x y t) ((y : E) - x)
  map_add' D G := by
    simp only [map_add, BoundedContinuousFunction.add_apply, ContinuousLinearMap.add_apply]
    exact intervalIntegral.integral_add
      ((continuous_segmentIntegrand hS α D x y).intervalIntegrable 0 1)
      ((continuous_segmentIntegrand hS α G x y).intervalIntegrable 0 1)
  map_smul' c D := by
    simp only [map_smul, BoundedContinuousFunction.smul_apply, ContinuousLinearMap.smul_apply,
      RingHom.id_apply]
    exact intervalIntegral.integral_smul c _

lemma segmentIntegralLinear_norm_bound {S : Set E} (hS : Convex ℝ S) (α : ℝ) (x y : S)
    (D : Space S (E →L[ℝ] F) α) :
    ‖segmentIntegralLinear hS α x y D‖ ≤ ‖(y : E) - x‖ * ‖D‖ := by
  have hbound : ∀ t ∈ uIoc (0 : ℝ) 1,
      ‖value S (E →L[ℝ] F) α D (segmentPoint hS x y t) ((y : E) - x)‖ ≤ ‖D‖ * ‖(y : E) - x‖ := by
    intro t _
    exact ((value S (E →L[ℝ] F) α D (segmentPoint hS x y t)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (norm_value_apply_le S (E →L[ℝ] F) α D _) (norm_nonneg _))
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  change ‖∫ t in (0 : ℝ)..1, value S (E →L[ℝ] F) α D (segmentPoint hS x y t) ((y : E) - x)‖ ≤ _
  simpa only [sub_zero, abs_one, mul_one, one_mul, mul_comm] using hi

/-- Integration along the actual segment is a bounded linear map, so the
FTC compatibility identities define closed linear conditions. -/
def segmentIntegral {S : Set E} (hS : Convex ℝ S) (α : ℝ) (x y : S) :
    Space S (E →L[ℝ] F) α →L[ℝ] F :=
  (segmentIntegralLinear hS α x y).mkContinuous ‖(y : E) - x‖
    (segmentIntegralLinear_norm_bound hS α x y)

@[simp] lemma segmentIntegral_apply {S : Set E} (hS : Convex ℝ S) (α : ℝ) (x y : S)
    (D : Space S (E →L[ℝ] F) α) :
    segmentIntegral hS α x y D =
      ∫ t in (0 : ℝ)..1, value S (E →L[ℝ] F) α D (segmentPoint hS x y t) ((y : E) - x) := rfl

end GaussianTilt.HolderSpace
