import GaussianTilt.LetwinStein
import GaussianTilt.LetwinCauchySchwarz

/-! # Actual L² dual bounds from the moment-map Stein coupling -/
noncomputable section
open MeasureTheory Matrix Set
open scoped BigOperators ContDiff ENNReal
namespace GaussianTilt.Letwin

lemma integral_dotProduct {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} {F : Ω → ι → ℝ} (hF : ∀ i, Integrable (fun x => F x i) μ)
    (v : ι → ℝ) :
    (∫ x, v ⬝ᵥ F x ∂μ) = v ⬝ᵥ (fun i => ∫ x, F x i ∂μ) := by
  simp only [dotProduct]
  rw [integral_finset_sum _ (fun i _ => (hF i).const_mul (v i))]
  simp only [integral_const_mul]

lemma memLp_comp_gradient {n : ℕ} {φ : CoordinateSpace n → ℝ}
    [IsFiniteMeasure (potentialMeasure φ)] (hφ : ContDiff ℝ 1 φ)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (hgrad : ∀ x, coordinateGradient φ x ∈ K)
    {g : CoordinateSpace n → ℝ} (hg : Continuous g) (p : ℝ≥0∞) :
    MemLp (fun x => g (coordinateGradient φ x)) p (potentialMeasure φ) := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  exact MemLp.of_bound (hg.comp (continuous_coordinateGradient hφ)).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => hC _ (hgrad x))

lemma memLp_continuous_hessian_function {n : ℕ} {φ : CoordinateSpace n → ℝ}
    [IsFiniteMeasure (potentialMeasure φ)] (hφ : ContDiff ℝ ∞ φ)
    (S : ℝ) (hHb : ∀ x i j, |coordinateHessian φ x i j| ≤ S)
    {F : Matrix (Fin n) (Fin n) ℝ → ℝ} (hF : Continuous F) (p : ℝ≥0∞) :
    MemLp (fun x => F (coordinateHessian φ x)) p (potentialMeasure φ) := by
  have hHm : Continuous (coordinateHessian φ) := continuous_pi fun i =>
    continuous_pi fun j => (smooth_coordinateHessian hφ i j).continuous
  obtain ⟨C, hC⟩ := bounded_continuous_matrix_function S hHb F hF
  exact MemLp.of_bound (hF.comp hHm).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hC x)

set_option maxHeartbeats 800000 in
/-- The scalar Stein identity for any linear functional on any linear image
of the moment law. Everything is evaluated on the original coupling. -/
theorem moment_map_stein_linear_functional {n : ℕ} {φ g : CoordinateSpace n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ ∞ φ) (hg : ContDiff ℝ 1 g)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (hgrad : ∀ x, coordinateGradient φ x ∈ K)
    (S : ℝ) (hHb : ∀ x i j, |coordinateHessian φ x i j| ≤ S)
    (T : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    (∫ x, (v ⬝ᵥ (T *ᵥ coordinateGradient φ x)) * g (T *ᵥ coordinateGradient φ x)
      ∂potentialMeasure φ) =
    ∫ x, ((T * coordinateHessian φ x * Tᵀ)ᵀ *ᵥ v) ⬝ᵥ
      coordinateGradient g (T *ᵥ coordinateGradient φ x) ∂potentialMeasure φ := by
  let Z := fun x => T *ᵥ coordinateGradient φ x
  let τ := fun x => T * coordinateHessian φ x * Tᵀ
  have hφ1 := contDiff_infty.mp hφ 1
  have hZi (i : Fin n) : MemLp (fun x => Z x i) 2 (potentialMeasure φ) := by
    exact memLp_comp_gradient hφ1 hK hgrad
      ((continuous_apply i).comp (coordinateMatrixMap T).continuous) 2
  have hgi : MemLp (fun x => g (Z x)) 2 (potentialMeasure φ) :=
    memLp_comp_gradient hφ1 hK hgrad (hg.continuous.comp (coordinateMatrixMap T).continuous) 2
  have hτ (i j : Fin n) : MemLp (fun x => τ x i j) 2 (potentialMeasure φ) := by
    apply memLp_continuous_hessian_function hφ S hHb (p := 2)
      (F := fun M => (T * M * Tᵀ) i j)
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    fun_prop
  have hD (j : Fin n) : MemLp (fun x => coordinateGradient g (Z x) j) 2 (potentialMeasure φ) := by
    exact memLp_comp_gradient hφ1 hK hgrad
      (((contDiff_coordinateDerivative hg (m := 0) (by norm_num) j).continuous).comp
        (coordinateMatrixMap T).continuous) 2
  have hFi (i : Fin n) := (hZi i).integrable_mul hgi
  have hGi (i : Fin n) : Integrable (fun x => (τ x *ᵥ coordinateGradient g (Z x)) i)
      (potentialMeasure φ) := by
    simp only [Matrix.mulVec, dotProduct]
    exact integrable_finset_sum _ (fun j _ => (hτ i j).integrable_mul (hD j))
  calc
    _ = ∫ x, v ⬝ᵥ (fun i => Z x i * g (Z x)) ∂potentialMeasure φ := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [dotProduct, Finset.sum_mul, mul_assoc, Z]
    _ = v ⬝ᵥ (fun i => ∫ x, Z x i * g (Z x) ∂potentialMeasure φ) := integral_dotProduct hFi v
    _ = v ⬝ᵥ (fun i => ∫ x, (τ x *ᵥ coordinateGradient g (Z x)) i ∂potentialMeasure φ) := by
      congr 1
      funext i
      exact moment_map_stein_linear_image hφ hg hK hgrad S hHb T i
    _ = ∫ x, v ⬝ᵥ (τ x *ᵥ coordinateGradient g (Z x)) ∂potentialMeasure φ :=
      (integral_dotProduct hGi v).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with x
      exact (Matrix.dotProduct_mulVec _ _ _).trans (by rw [Matrix.mulVec_transpose])

set_option maxHeartbeats 800000 in
/-- Squared L² test-duality estimate for the actual linearly transported
moment map. This is the analytic Cauchy–Schwarz step in Letwin lemma 2.9. -/
theorem moment_map_stein_dual_sq {n : ℕ} {φ g : CoordinateSpace n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ ∞ φ) (hg : ContDiff ℝ 1 g)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (hgrad : ∀ x, coordinateGradient φ x ∈ K)
    (S : ℝ) (hHb : ∀ x i j, |coordinateHessian φ x i j| ≤ S)
    (T : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    (∫ x, (v ⬝ᵥ (T *ᵥ coordinateGradient φ x)) * g (T *ᵥ coordinateGradient φ x)
      ∂potentialMeasure φ)^2 ≤
    (∫ x, ∑ j, (((T * coordinateHessian φ x * Tᵀ)ᵀ *ᵥ v) j)^2 ∂potentialMeasure φ) *
    (∫ x, ∑ j, (coordinateDerivative j g (T *ᵥ coordinateGradient φ x))^2 ∂potentialMeasure φ) := by
  rw [moment_map_stein_linear_functional hφ hg hK hgrad S hHb T v]
  apply integral_sum_mul_sq_le
  · intro j
    apply memLp_continuous_hessian_function hφ S hHb (p := 2)
      (F := fun M => ((T * M * Tᵀ)ᵀ *ᵥ v) j)
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct]
    fun_prop
  · intro j
    exact memLp_comp_gradient (contDiff_infty.mp hφ 1) hK hgrad
      (((contDiff_coordinateDerivative hg (m := 0) (by norm_num) j).continuous).comp
        (coordinateMatrixMap T).continuous) 2

end GaussianTilt.Letwin
