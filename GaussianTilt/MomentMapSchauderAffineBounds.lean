import GaussianTilt.MomentMapSchauderUniformEllipticity

/-!
# Quantitative Euclidean bounds for elliptic coefficient normalization

The square root of the actual frozen coefficient has norm at most √Λ,
and its actual matrix inverse has norm at most 1/√lam. These follow from
the given quadratic-form ellipticity and the identity PᵀP=A, not from an
assumed elliptic change-of-variables theorem.
-/
noncomputable section
open Matrix InnerProductSpace
open scoped BigOperators MatrixOrder
namespace GaussianTilt.MomentMapSchauder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma norm_toEuclideanCLM_sq (M : Matrix ι ι ℝ) (v : EuclideanSpace ℝ ι) :
    ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) M v‖ ^ 2 = euclideanQuadratic (Mᵀ * M) v := by
  rw [← real_inner_self_eq_norm_sq]
  change inner ℝ (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) M v) (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) M v) =
    v.ofLp ⬝ᵥ ((Mᵀ * M) *ᵥ v.ofLp)
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  simp only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanCLM, star_trivial]

lemma sqrt_transpose_mul_sqrt {A : Matrix ι ι ℝ} (hA : A.PosDef) :
    (CFC.sqrt A)ᵀ * CFC.sqrt A = A := by
  have hs : (CFC.sqrt A)ᵀ = CFC.sqrt A := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.posDef_sqrt.isHermitian.eq
  rw [hs]
  exact CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg

/-- Exact Euclidean energy identity of the frozen coefficient square root. -/
lemma norm_coefficient_sqrt_sq {A : Matrix ι ι ℝ} (hA : A.PosDef) (v : EuclideanSpace ℝ ι) :
    ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (CFC.sqrt A) v‖ ^ 2 = euclideanQuadratic A v := by
  rw [norm_toEuclideanCLM_sq, sqrt_transpose_mul_sqrt hA]

/-- Quantitative upper operator bound for the actual coefficient square root. -/
theorem norm_coefficient_sqrt_le {A : Matrix ι ι ℝ} (hA : A.PosDef)
    {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hupper : ∀ v : EuclideanSpace ℝ ι, euclideanQuadratic A v ≤ Λ * ‖v‖ ^ 2) :
    ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (CFC.sqrt A)‖ ≤ Real.sqrt Λ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro v
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt hΛ, norm_coefficient_sqrt_sq hA]
  exact hupper v

lemma toEuclideanCLM_inv_cancel {A : Matrix ι ι ℝ} (hA : A.PosDef) (v : EuclideanSpace ℝ ι) :
    Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A⁻¹ v) = v := by
  change (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A * Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A⁻¹) v = v
  rw [← map_mul, Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA.det_pos.ne'), map_one]
  rfl

/-- Quantitative inverse-radius control from the true lower ellipticity
bound, valid without diagonalizing or choosing eigenvectors. -/
theorem norm_inverse_coefficient_sqrt_le {A : Matrix ι ι ℝ} (hA : A.PosDef)
    {lam : ℝ} (hlam : 0 < lam)
    (hlower : ∀ v : EuclideanSpace ℝ ι, lam * ‖v‖ ^ 2 ≤ euclideanQuadratic A v) :
    ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (CFC.sqrt A)⁻¹‖ ≤ (Real.sqrt lam)⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
  intro v
  have hsqrt : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hb := hlower (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (CFC.sqrt A)⁻¹ v)
  rw [← norm_coefficient_sqrt_sq hA, toEuclideanCLM_inv_cancel hA.posDef_sqrt] at hb
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (inv_nonneg.mpr hsqrt.le) (norm_nonneg _))).mp
  rw [mul_pow, inv_pow, Real.sq_sqrt hlam.le]
  exact (le_inv_mul_iff₀ hlam).mpr hb

end GaussianTilt.MomentMapSchauder
