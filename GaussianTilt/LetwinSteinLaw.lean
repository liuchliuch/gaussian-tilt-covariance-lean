import GaussianTilt.LetwinSteinBounds
import GaussianTilt.NegativeSobolevDuality

/-! # Stein test bounds for the genuine transported probability law -/
noncomputable section
open MeasureTheory Matrix Set
open scoped BigOperators ContDiff ENNReal
namespace GaussianTilt.Letwin

def linearMomentMeasure {n : ℕ} (φ : CoordinateSpace n → ℝ)
    (T : Matrix (Fin n) (Fin n) ℝ) : Measure (CoordinateSpace n) :=
  (potentialMeasure φ).map (fun x => T *ᵥ coordinateGradient φ x)

lemma continuous_linearMomentMap {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (T : Matrix (Fin n) (Fin n) ℝ) :
    Continuous (fun x => T *ᵥ coordinateGradient φ x) :=
  (coordinateMatrixMap T).continuous.comp (continuous_coordinateGradient hφ)

lemma linearMomentMeasure_probability {n : ℕ} {φ : CoordinateSpace n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)] (hφ : ContDiff ℝ 1 φ)
    (T : Matrix (Fin n) (Fin n) ℝ) : IsProbabilityMeasure (linearMomentMeasure φ T) :=
  Measure.isProbabilityMeasure_map (continuous_linearMomentMap hφ T).measurable.aemeasurable

lemma integral_linearMomentMeasure {n : ℕ} {φ g : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (T : Matrix (Fin n) (Fin n) ℝ) (hg : Continuous g) :
    (∫ z, g z ∂linearMomentMeasure φ T) =
      ∫ x, g (T *ᵥ coordinateGradient φ x) ∂potentialMeasure φ :=
  integral_map (continuous_linearMomentMap hφ T).measurable.aemeasurable hg.aestronglyMeasurable

/-- The genuine dual norm constant supplied by the coupling Hessian. -/
def steinDualConstant {n : ℕ} (φ : CoordinateSpace n → ℝ)
    (T : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) : ℝ :=
  Real.sqrt (∫ x, ∑ j, (((T * coordinateHessian φ x * Tᵀ)ᵀ *ᵥ v) j)^2 ∂potentialMeasure φ)

lemma steinDualConstant_nonneg {n : ℕ} (φ : CoordinateSpace n → ℝ)
    (T : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) : 0 ≤ steinDualConstant φ T v :=
  Real.sqrt_nonneg _

lemma steinDualConstant_sq {n : ℕ} (φ : CoordinateSpace n → ℝ)
    (T : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    steinDualConstant φ T v ^ 2 =
      ∫ x, ∑ j, (((T * coordinateHessian φ x * Tᵀ)ᵀ *ᵥ v) j)^2 ∂potentialMeasure φ :=
  Real.sq_sqrt (integral_nonneg fun x => Finset.sum_nonneg fun _ _ => sq_nonneg _)

set_option maxHeartbeats 800000 in
/-- Actual H⁻¹ test bound for every linear functional of the linearly
transported moment law. The constant is a concrete Hessian-square integral. -/
theorem linearMomentMeasure_compactNegativeSobolevBound {n : ℕ} {φ : CoordinateSpace n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ ∞ φ)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (hgrad : ∀ x, coordinateGradient φ x ∈ K)
    (S : ℝ) (hHb : ∀ x i j, |coordinateHessian φ x i j| ≤ S)
    (T : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    CompactNegativeSobolevBound (linearMomentMeasure φ T) (fun z => v ⬝ᵥ z)
      (steinDualConstant φ T v) := by
  intro g hg _hgc hge
  have hφ1 := contDiff_infty.mp hφ 1
  have hD := moment_map_stein_dual_sq hφ (contDiff_infty.mp hg 1) hK hgrad S hHb T v
  have hE : (∫ x, ∑ j, (coordinateDerivative j g (T *ᵥ coordinateGradient φ x))^2
      ∂potentialMeasure φ) ≤ 1 := by
    rw [integral_linearMomentMeasure hφ1 T (continuous_gradientSquare hg)] at hge
    exact hge
  have hC0 : 0 ≤ ∫ x, ∑ j, (((T * coordinateHessian φ x * Tᵀ)ᵀ *ᵥ v) j)^2
      ∂potentialMeasure φ :=
    integral_nonneg fun x => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hSq := hD.trans (mul_le_mul_of_nonneg_left hE hC0)
  rw [mul_one] at hSq
  rw [integral_linearMomentMeasure hφ1 T (by
    apply Continuous.mul _ hg.continuous
    simp only [dotProduct]
    fun_prop)]
  exact Real.abs_le_sqrt hSq

lemma memLp_linearMomentMeasure {n : ℕ} {φ g : CoordinateSpace n → ℝ}
    [IsFiniteMeasure (potentialMeasure φ)] (hφ : ContDiff ℝ 1 φ)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (hgrad : ∀ x, coordinateGradient φ x ∈ K)
    (T : Matrix (Fin n) (Fin n) ℝ) (hg : Continuous g) (p : ℝ≥0∞) :
    MemLp g p (linearMomentMeasure φ T) := by
  apply (memLp_map_measure_iff hg.aestronglyMeasurable
    (continuous_linearMomentMap hφ T).measurable.aemeasurable).mpr
  exact memLp_comp_gradient hφ hK hgrad (hg.comp (coordinateMatrixMap T).continuous) p

set_option maxHeartbeats 800000 in
/-- Every linear functional of the actual image law is centered, by score
integration. Centering is not an extra hypothesis on the moment potential. -/
lemma integral_linearMomentMeasure_linear_eq_zero {n : ℕ} {φ : CoordinateSpace n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)] (hφ : ContDiff ℝ ∞ φ)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (hgrad : ∀ x, coordinateGradient φ x ∈ K)
    (T : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    (∫ z, v ⬝ᵥ z ∂linearMomentMeasure φ T) = 0 := by
  have hφ1 := contDiff_infty.mp hφ 1
  have hgi (i : Fin n) : Integrable (fun x => coordinateGradient φ x i) (potentialMeasure φ) :=
    integrable_comp_gradient (g := fun z : CoordinateSpace n => z i) hφ1 hK hgrad (continuous_apply i)
  rw [integral_linearMomentMeasure (g := fun z => v ⬝ᵥ z) hφ1 T
    (by simp only [dotProduct]; fun_prop)]
  have heq : (fun x => v ⬝ᵥ (T *ᵥ coordinateGradient φ x)) =
      (fun x => (Tᵀ *ᵥ v) ⬝ᵥ coordinateGradient φ x) := by
    funext x
    rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
  rw [heq, integral_dotProduct (F := coordinateGradient φ) hgi]
  have hm : (fun i => ∫ x, coordinateGradient φ x i ∂potentialMeasure φ) = 0 := by
    funext i
    exact integral_coordinateGradient_eq_zero i (hφ.differentiable (by simp)) (hgi i)
  rw [hm, dotProduct_zero]

end GaussianTilt.Letwin
