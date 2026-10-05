import GaussianTilt.ActualUpperFlowNoncompact

/-! # The exact Euclidean gradient and energy identity in original Theorem 2.2 -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix Set Filter
open scoped Topology BigOperators Matrix.Norms.L2Operator Gradient

namespace GaussianTilt.Reference
variable {n : ℕ}

/-- The actual Euclidean gradient of the quadratic observable is `2 A x`. -/
lemma hasGradientAt_matrixQuadratic (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (x : Space n) :
    HasGradientAt (fun y : Space n ↦ matrixQuadratic A (fun i ↦ y i))
      ((2 : ℝ) • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) A x) x := by
  let L := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) A
  have hsym : ∀ u v : Space n, inner ℝ (L u) v = inner ℝ u (L v) :=
    Matrix.isHermitian_iff_isSymmetric.mp hA
  have hd := (hasFDerivAt_id x).inner ℝ L.hasFDerivAt
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hd using 1
  · funext y
    simp [matrixQuadratic, L, EuclideanSpace.inner_eq_star_dotProduct,
      Matrix.ofLp_toEuclideanCLM, star_trivial, dotProduct_comm]
    rfl
  · ext y
    change inner ℝ ((2 : ℝ) • L x) y = inner ℝ x (L y) + inner ℝ y (L x)
    rw [real_inner_smul_left, ← hsym x y, real_inner_comm y (L x)]
    ring

lemma gradient_matrixQuadratic (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (x : Space n) :
    gradient (fun y : Space n ↦ matrixQuadratic A (fun i ↦ y i)) x =
      (2 : ℝ) • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) A x :=
  (hasGradientAt_matrixQuadratic A hA x).gradient

/-- Isotropy evaluates the exact square-gradient energy, at noncompact scope. -/
lemma isotropic_quadratic_gradient_energy
    (μ : Measure (Space n)) [IsProbabilityMeasure μ] (hi : isotropic μ)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) :
    (∫ x, ‖gradient (fun y : Space n ↦ matrixQuadratic A (fun i ↦ y i)) x‖ ^ 2 ∂μ) =
      4 * Matrix.trace (A ^ 2) := by
  let L := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) A
  have hX := isotropic_coordinate_memLp hi
  have hY := Whitening.memLp_mulVec (X := Whitening.coordinates) hX A
  have hm : meanVector μ Whitening.coordinates = 0 := by
    ext i
    exact isotropic_coordinate_integral hi i
  have hc : covarianceMatrix μ Whitening.coordinates = 1 := by
    rw [← covariance_eq_covarianceMatrix hX, hi.2]
  have hAs : A.IsSymm := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hA
  have hM : secondMomentMatrix μ (fun x : Space n ↦ A *ᵥ Whitening.coordinates x) = A ^ 2 := by
    rw [secondMomentMatrix_eq_covariance_add_rankOne hY,
      Whitening.covarianceMatrix_mulVec (X := Whitening.coordinates) hX, hc,
      Whitening.meanVector_mulVec (X := Whitening.coordinates) (fun i ↦ (hX i).integrable (by norm_num)), hm,
      Matrix.mulVec_zero, Matrix.mul_one, hAs.eq]
    simp only [vecMulVec_zero, add_zero, pow_two]
  have hnorm : (∫ x : Space n, ‖L x‖ ^ 2 ∂μ) = Matrix.trace (A ^ 2) := by
    rw [← hM]
    have heq (x : Space n) : ‖L x‖ ^ 2 = ∑ i : Fin n, ((A *ᵥ Whitening.coordinates x) i) ^ 2 := by
      simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs,
        L, ← PiLp.ofLp_apply, Matrix.ofLp_toEuclideanCLM]
    simp_rw [heq]
    rw [integral_finset_sum _ (fun i _ ↦
      (memLp_two_iff_integrable_sq (hY i).aestronglyMeasurable).mp (hY i))]
    simp only [Matrix.trace, Matrix.diag_apply, secondMomentMatrix, pow_two]
  simp_rw [gradient_matrixQuadratic A hA, norm_smul, Real.norm_ofNat, mul_pow]
  rw [integral_const_mul]
  norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num]
  change 4 * (∫ x : Space n, ‖L x‖ ^ 2 ∂μ) = _
  rw [hnorm]

/-- Both the inequality and exact square-gradient equality from original2.2,
conditional solely on compact isotropic Letwin; no extra moment assumptions. -/
theorem original2_2_of_compact_bound
    (hL : IsotropicQuadraticVarianceBound)
    (μ : Measure (Space n)) [IsProbabilityMeasure μ]
    (hl : logconcave μ) (hi : isotropic μ)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) :
    ProbabilityTheory.variance (fun x : Space n ↦ matrixQuadratic A (fun i ↦ x i)) μ ≤
      2 * (∫ x, ‖gradient (fun y : Space n ↦ matrixQuadratic A (fun i ↦ y i)) x‖ ^ 2 ∂μ) ∧
    2 * (∫ x, ‖gradient (fun y : Space n ↦ matrixQuadratic A (fun i ↦ y i)) x‖ ^ 2 ∂μ) =
      8 * Matrix.trace (A ^ 2) := by
  rw [isotropic_quadratic_gradient_energy μ hi A hA]
  constructor
  · nlinarith [isotropic_quadratic_variance_of_compact_bound hL μ hl hi A hA]
  · ring

end GaussianTilt.Reference
