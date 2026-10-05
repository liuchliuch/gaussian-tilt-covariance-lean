import GaussianTilt.LetwinGaussianMoments
import GaussianTilt.LetwinGaussianLaw

/-! # Actual probability, centering and L² hypotheses for smoothed quadratics -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix Set
open scoped BigOperators ContDiff ENNReal
namespace GaussianTilt.Letwin

lemma noisyMomentMeasure_probability {n : ℕ} {φ : CoordinateSpace n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)] (hφ : ContDiff ℝ 1 φ)
    (T : Matrix (Fin n) (Fin n) ℝ) (r : ℝ) : IsProbabilityMeasure (noisyMomentMeasure φ T r) :=
  Measure.isProbabilityMeasure_map (continuous_noisyMomentMap hφ T r).measurable.aemeasurable

lemma noisyMomentMeasure_zero {n : ℕ} {φ : CoordinateSpace n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)] (hφ : ContDiff ℝ 1 φ)
    (T : Matrix (Fin n) (Fin n) ℝ) : noisyMomentMeasure φ T 0=linearMomentMeasure φ T := by
  rw [noisyMomentMeasure_eq_perturb hφ T 0]
  simp only [zero_smul, add_zero, Measure.map_fst_prod, measure_univ, one_smul]

lemma coordinateGaussian_coordinate_mean_zero {n : ℕ} (i : Fin n) :
    (∫ x : CoordinateSpace n, x i ∂coordinateGaussian n)=0 := by
  have h := coordinateGaussian_stein_identity (g := fun _ : CoordinateSpace n => (1 : ℝ))
    contDiff_const 1 0 (by intro x; norm_num) (by intro x j; simp [coordinateDerivative]) i
  simpa [coordinateDerivative] using h

lemma integral_coordinateGaussian_linear_eq_zero {n : ℕ} (v : Fin n → ℝ) :
    (∫ x, v ⬝ᵥ x ∂coordinateGaussian n)=0 := by
  change (∫ x, v ⬝ᵥ id x ∂coordinateGaussian n)=0
  rw [integral_dotProduct (F := id) coordinateGaussian_coordinate_integrable v]
  simp only [id_eq, coordinateGaussian_coordinate_mean_zero, dotProduct, mul_zero, Finset.sum_const_zero]

lemma integral_noisyMomentMeasure_linear_eq_zero {n : ℕ} {φ : CoordinateSpace n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)] (hφ : ContDiff ℝ ∞ φ)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (hgrad : ∀ x, coordinateGradient φ x∈K)
    (T : Matrix (Fin n) (Fin n) ℝ) (r : ℝ) (v : Fin n → ℝ) :
    (∫ z, v ⬝ᵥ z ∂noisyMomentMeasure φ T r)=0 := by
  have hφ1 := contDiff_infty.mp hφ 1
  have hcont : Continuous (fun z : CoordinateSpace n => v ⬝ᵥ z) := by
    simp only [dotProduct]; fun_prop
  have hXi : Integrable (fun x => v ⬝ᵥ (T*ᵥcoordinateGradient φ x)) (potentialMeasure φ) :=
    integrable_comp_gradient (g := fun x => v ⬝ᵥ (T*ᵥx)) hφ1 hK hgrad
      (hcont.comp (coordinateMatrixMap T).continuous)
  have hYi : Integrable (fun y : CoordinateSpace n => r*(v ⬝ᵥ y)) (coordinateGaussian n) :=
    (integrable_finset_sum _ (fun i _ => (coordinateGaussian_coordinate_integrable i).const_mul (v i))).const_mul r
  rw [noisyMomentMeasure, integral_map (continuous_noisyMomentMap hφ1 T r).measurable.aemeasurable
    hcont.aestronglyMeasurable]
  simp only [noisyMomentMap, dotProduct_add, dotProduct_smul, smul_eq_mul]
  rw [integral_add (hXi.comp_fst (coordinateGaussian n)) (hYi.comp_snd (potentialMeasure φ)),
    integral_fun_fst (fun x => v ⬝ᵥ (T*ᵥcoordinateGradient φ x)),
    integral_fun_snd (fun y : CoordinateSpace n => r*(v ⬝ᵥ y)),
    measureReal_univ_eq_one, one_smul, integral_const_mul,
    integral_coordinateGaussian_linear_eq_zero, mul_zero, smul_zero, add_zero]
  rw [← integral_linearMomentMeasure (g := fun z => v ⬝ᵥ z) hφ1 T hcont]
  exact integral_linearMomentMeasure_linear_eq_zero hφ hK hgrad T v

lemma noisyCoupling_combined_products_memLp {n : ℕ} {φ : CoordinateSpace n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)] (hφ : ContDiff ℝ 1 φ)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (hgrad : ∀ x, coordinateGradient φ x∈K)
    (T : Matrix (Fin n) (Fin n) ℝ) (a b : Fin n ⊕ Fin n) :
    MemLp (fun p : CoordinateSpace n × CoordinateSpace n =>
      Sum.elim (T*ᵥcoordinateGradient φ p.1) p.2 a * Sum.elim (T*ᵥcoordinateGradient φ p.1) p.2 b)
      2 ((potentialMeasure φ).prod (coordinateGaussian n)) := by
  have hXi (i : Fin n) : MemLp (fun x => (T*ᵥcoordinateGradient φ x) i) 2 (potentialMeasure φ) :=
    memLp_comp_gradient (g := fun x => (T*ᵥx) i) hφ hK hgrad
      ((continuous_apply i).comp (coordinateMatrixMap T).continuous) 2
  cases a with
  | inl i => cases b with
    | inl j =>
      exact (memLp_comp_gradient (g := fun x => (T*ᵥx) i*(T*ᵥx) j) hφ hK hgrad
        (((continuous_apply i).comp (coordinateMatrixMap T).continuous).mul
          ((continuous_apply j).comp (coordinateMatrixMap T).continuous)) 2).comp_fst _
    | inr j => exact memLp_independent_product (hXi i) (coordinateGaussian_coordinate_memLp j)
  | inr i => cases b with
    | inl j => simpa only [mul_comm] using memLp_independent_product (hXi j) (coordinateGaussian_coordinate_memLp i)
    | inr j => exact (coordinateGaussian_products_memLp i j).comp_snd _

lemma quadratic_noisyMomentMeasure_memLp {n : ℕ} {φ : CoordinateSpace n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)] (hφ : ContDiff ℝ 1 φ)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (hgrad : ∀ x, coordinateGradient φ x∈K)
    (T B : Matrix (Fin n) (Fin n) ℝ) (r : ℝ) :
    MemLp (matrixQuadratic B) 2 (noisyMomentMeasure φ T r) := by
  apply (memLp_map_measure_iff (contDiff_matrixQuadratic B).continuous.aestronglyMeasurable
    (continuous_noisyMomentMap hφ T r).measurable.aemeasurable).mpr
  have h := Whitening.quadratic_memLp_of_products (noisyCoupling_combined_products_memLp hφ hK hgrad T)
    (Matrix.fromBlocks B (r • B) (r • B) (r^2 • B))
  simpa only [matrixQuadratic_add_scaled_fromBlocks] using h

lemma quadratic_gradient_noisyMomentMeasure_memLp {n : ℕ} {φ : CoordinateSpace n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)] (hφ : ContDiff ℝ 1 φ)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (hgrad : ∀ x, coordinateGradient φ x∈K)
    (T B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) (r : ℝ) (i : Fin n) :
    MemLp (coordinateDerivative i (matrixQuadratic B)) 2 (noisyMomentMeasure φ T r) := by
  apply (memLp_map_measure_iff (smooth_coordinateDerivative (contDiff_matrixQuadratic B) i).continuous.aestronglyMeasurable
    (continuous_noisyMomentMap hφ T r).measurable.aemeasurable).mpr
  simp only [Function.comp_def, coordinateDerivative_matrixQuadratic B hB, Matrix.mulVec,
    dotProduct, Finset.mul_sum, ← mul_assoc]
  exact memLp_finset_sum _ (fun j _ => (memLp_noisyMomentMap hφ hK hgrad T r j).const_mul (2*B i j))

lemma integral_quadratic_gradient_noisyMomentMeasure {n : ℕ} {φ : CoordinateSpace n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)] (hφ : ContDiff ℝ ∞ φ)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (hgrad : ∀ x, coordinateGradient φ x∈K)
    (T B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) (r : ℝ) (i : Fin n) :
    (∫ z, coordinateDerivative i (matrixQuadratic B) z ∂noisyMomentMeasure φ T r)=0 := by
  have heq : coordinateDerivative i (matrixQuadratic B) = (fun z => (fun j => 2*B i j) ⬝ᵥ z) := by
    funext z
    rw [coordinateDerivative_matrixQuadratic B hB]
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  rw [heq]
  exact integral_noisyMomentMeasure_linear_eq_zero hφ hK hgrad T r _

end GaussianTilt.Letwin
