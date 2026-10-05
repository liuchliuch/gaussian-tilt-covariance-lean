import GaussianTilt.LetwinSteinLaw
import GaussianTilt.LetwinSign

/-! # The sharp regular quadratic duality budget -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix Set
open scoped BigOperators ContDiff ENNReal
namespace GaussianTilt.Letwin

lemma transpose_mulVec_scaled_row {ι : Type*} [Fintype ι]
    (U A : Matrix ι ι ℝ) (c : ℝ) (i j : ι) :
    (Aᵀ *ᵥ (fun k => c * U i k)) j = c * (U * A) i j := by
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.mul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

set_option maxHeartbeats 800000 in
/-- The sum of the actual squared dual constants is exactly the integrated
Hilbert–Schmidt square of the transformed Stein matrix. -/
lemma sum_steinDualConstant_sq {n : ℕ} {φ : CoordinateSpace n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)] (hφ : ContDiff ℝ ∞ φ)
    (S : ℝ) (hHb : ∀ x i j, |coordinateHessian φ x i j| ≤ S)
    (T U : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) :
    (∑ i, steinDualConstant φ T (fun j => c * U i j)^2) =
      c^2 * ∫ x, hsSquare (U * (T * coordinateHessian φ x * Tᵀ)) ∂potentialMeasure φ := by
  simp only [steinDualConstant_sq, transpose_mulVec_scaled_row, mul_pow]
  have hFi (i : Fin n) : Integrable
      (fun x => ∑ j, c^2 * (U * (T * coordinateHessian φ x * Tᵀ)) i j ^ 2)
      (potentialMeasure φ) := by
    exact (memLp_continuous_hessian_function hφ S hHb
      (F := fun M => ∑ j, c^2 * (U * (T * M * Tᵀ)) i j ^ 2)
      (by simp only [Matrix.mul_apply, Matrix.transpose_apply]; fun_prop) 1).integrable le_rfl
  rw [← integral_finset_sum _ (fun i _ => hFi i), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  simp only [hsSquare, Finset.mul_sum]

/-- Orthogonal rows consume exactly the same energy as the original Stein
matrix; this is the trace cancellation that prevents a condition number. -/
lemma sum_steinDualConstant_sq_orthogonal {n : ℕ} {φ : CoordinateSpace n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)] (hφ : ContDiff ℝ ∞ φ)
    (S : ℝ) (hHb : ∀ x i j, |coordinateHessian φ x i j| ≤ S)
    (T U : Matrix (Fin n) (Fin n) ℝ) (hU : Uᵀ * U = 1) (c : ℝ) :
    (∑ i, steinDualConstant φ T (fun j => c * U i j)^2) =
      c^2 * ∫ x, hsSquare (T * coordinateHessian φ x * Tᵀ) ∂potentialMeasure φ := by
  rw [sum_steinDualConstant_sq hφ S hHb]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  exact hsSquare_mul_orthogonal _ _ hU

set_option maxHeartbeats 800000 in
/-- The complete sharp budget for the quadratic gradient in sign/root
coordinates. It uses the genuine regular trace theorem, not a variance premise. -/
theorem regular_quadratic_dual_budget {n : ℕ} {φ V : CoordinateSpace n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ ∞ φ) (hc : ConvexOn ℝ univ φ)
    (hH : ∀ x, (coordinateHessian φ x).PosDef)
    {K U : Set (CoordinateSpace n)} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hgrad : ∀ x, coordinateGradient φ x ∈ K)
    (hV : ContDiffOn ℝ 2 V U) (hVc : ConvexOn ℝ U V)
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x + V (coordinateGradient φ x))
    (S : ℝ) (hHb : ∀ x i j, |coordinateHessian φ x i j| ≤ S)
    (hiso : covarianceMatrix (potentialMeasure φ) (coordinateGradient φ) = 1)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsHermitian) :
    (∑ i, steinDualConstant φ (spectralMagnitudeRoot hB) (fun j => 2 * spectralSign hB i j)^2) ≤
      8 * Matrix.trace (B^2) := by
  have hsign : (spectralSign hB)ᵀ * spectralSign hB = 1 := by
    rw [(spectralSign_isSymm hB).eq, spectralSign_mul_self]
  rw [sum_steinDualConstant_sq_orthogonal hφ S hHb _ _ hsign]
  have heq : (fun x => hsSquare (spectralMagnitudeRoot hB * coordinateHessian φ x *
      (spectralMagnitudeRoot hB)ᵀ)) =
      (fun x => Matrix.trace (spectralAbsolute hB * coordinateHessian φ x *
        spectralAbsolute hB * coordinateHessian φ x)) := by
    funext x
    rw [(spectralMagnitudeRoot_isSymm hB).eq,
      hsSquare_conjugate_eq_trace _ _ (spectralMagnitudeRoot_isSymm hB)
        (coordinateHessian_isSymm (contDiff_infty.mp hφ 2) x), spectralMagnitudeRoot_mul_self]
  rw [heq]
  have hbound := regular_mongeAmpere_trace_bound_posSemidef hφ hc hH hK hU hKU hgrad hV hVc hMA
    S hHb hiso (spectralAbsolute hB) (spectralAbsolute_posSemidef hB)
  rw [spectralAbsolute_trace_square] at hbound
  nlinarith

lemma contDiff_matrixQuadratic {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) :
    ContDiff ℝ ∞ (matrixQuadratic B) := by
  unfold matrixQuadratic Matrix.mulVec dotProduct
  fun_prop

lemma coordinateDerivative_apply {n : ℕ} (i j : Fin n) (x : CoordinateSpace n) :
    coordinateDerivative i (fun y : CoordinateSpace n => y j) x = if i = j then 1 else 0 := by
  unfold coordinateDerivative
  rw [(hasFDerivAt_apply j x).fderiv]
  simp [Pi.single_apply, eq_comm]

lemma coordinateDerivative_matrixQuadratic {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : B.IsSymm) (i : Fin n) (x : CoordinateSpace n) :
    coordinateDerivative i (matrixQuadratic B) x = 2 * (B *ᵥ x) i := by
  have hmul (a b : Fin n) : Differentiable ℝ (fun y : CoordinateSpace n => B a b * y a * y b) := by
    fun_prop
  have heq : matrixQuadratic B = (fun y : CoordinateSpace n => ∑ a, ∑ b, B a b * y a * y b) := by
    funext y
    simp only [matrixQuadratic, Matrix.mulVec, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  have happ (a : Fin n) : Differentiable ℝ (fun y : CoordinateSpace n => y a) :=
    fun y => (hasFDerivAt_apply a y).differentiableAt
  have hd (a b : Fin n) :
      coordinateDerivative i (fun y : CoordinateSpace n => B a b * y a * y b) x =
        B a b * (if i = a then 1 else 0) * x b + B a b * x a * (if i = b then 1 else 0) := by
    rw [coordinateDerivative_mul (f := fun y : CoordinateSpace n => B a b * y a)
        (g := fun y : CoordinateSpace n => y b) ((differentiable_const (B a b)).mul (happ a)) (happ b),
      coordinateDerivative_const_mul (happ a), coordinateDerivative_apply, coordinateDerivative_apply]
  rw [heq, coordinateDerivative_sum _ (fun a => Differentiable.fun_sum (fun b _ => hmul a b))]
  simp only [coordinateDerivative_sum _ (fun b => hmul _ b), hd,
    Finset.sum_add_distrib, mul_ite, ite_mul, mul_one, mul_zero, zero_mul]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [Matrix.mulVec, dotProduct]
  have hsym : (∑ a, B a i * x a) = ∑ a, B i a * x a := by
    apply Finset.sum_congr rfl
    intro a _
    rw [hB.apply i a]
  rw [hsym]
  ring

/-- Every quadratic-gradient coordinate has the proved compact-test dual
bound with exactly the constants used in the sharp budget. -/
theorem regular_quadratic_gradient_dual_bounds {n : ℕ} {φ : CoordinateSpace n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ ∞ φ)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (hgrad : ∀ x, coordinateGradient φ x ∈ K)
    (S : ℝ) (hHb : ∀ x i j, |coordinateHessian φ x i j| ≤ S)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsHermitian) (i : Fin n) :
    CompactNegativeSobolevBound (linearMomentMeasure φ (spectralMagnitudeRoot hB))
      (coordinateDerivative i (matrixQuadratic (spectralSign hB)))
      (steinDualConstant φ (spectralMagnitudeRoot hB) (fun j => 2 * spectralSign hB i j)) := by
  have heq : coordinateDerivative i (matrixQuadratic (spectralSign hB)) =
      (fun z => (fun j => 2 * spectralSign hB i j) ⬝ᵥ z) := by
    funext z
    rw [coordinateDerivative_matrixQuadratic _ (spectralSign_isSymm hB)]
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  rw [heq]
  exact linearMomentMeasure_compactNegativeSobolevBound hφ hK hgrad S hHb _ _

/-- Exact variance transport through the actual sign/root coordinates. -/
lemma variance_spectralCoordinates {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 1 φ) {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsHermitian) :
    variance (matrixQuadratic (spectralSign hB))
      (linearMomentMeasure φ (spectralMagnitudeRoot hB)) =
    variance (fun x => matrixQuadratic B (coordinateGradient φ x)) (potentialMeasure φ) := by
  rw [linearMomentMeasure, variance_map
    (contDiff_matrixQuadratic (spectralSign hB)).continuous.aemeasurable
    (continuous_linearMomentMap hφ (spectralMagnitudeRoot hB)).measurable.aemeasurable]
  congr 1
  funext x
  exact matrixQuadratic_spectralCoordinates hB _

/-- All L² obligations in the H⁻¹ step follow from the actual compact
moment image, including the quadratic itself and every first derivative. -/
lemma quadratic_linearMomentMeasure_memLp {n : ℕ} {φ : CoordinateSpace n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)] (hφ : ContDiff ℝ 1 φ)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (hgrad : ∀ x, coordinateGradient φ x ∈ K)
    (T B : Matrix (Fin n) (Fin n) ℝ) :
    MemLp (matrixQuadratic B) 2 (linearMomentMeasure φ T) ∧
      ∀ i, MemLp (coordinateDerivative i (matrixQuadratic B)) 2 (linearMomentMeasure φ T) := by
  refine ⟨memLp_linearMomentMeasure hφ hK hgrad T (contDiff_matrixQuadratic B).continuous 2, ?_⟩
  intro i
  exact memLp_linearMomentMeasure hφ hK hgrad T
    (smooth_coordinateDerivative (contDiff_matrixQuadratic B) i).continuous 2

/-- Actual centering of every quadratic-gradient component on the image law. -/
lemma integral_quadratic_gradient_linearMomentMeasure {n : ℕ} {φ : CoordinateSpace n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)] (hφ : ContDiff ℝ ∞ φ)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (hgrad : ∀ x, coordinateGradient φ x ∈ K)
    (T B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) (i : Fin n) :
    (∫ z, coordinateDerivative i (matrixQuadratic B) z ∂linearMomentMeasure φ T) = 0 := by
  have heq : coordinateDerivative i (matrixQuadratic B) =
      (fun z => (fun j => 2 * B i j) ⬝ᵥ z) := by
    funext z
    rw [coordinateDerivative_matrixQuadratic B hB]
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  rw [heq]
  exact integral_linearMomentMeasure_linear_eq_zero hφ hK hgrad T _

end GaussianTilt.Letwin
