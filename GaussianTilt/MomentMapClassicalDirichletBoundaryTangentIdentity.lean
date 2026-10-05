import GaussianTilt.MomentMapClassicalDirichletBoundaryTangentBlock

/-! # Tangent-block identities linking the true boundary jets to the shear -/
noncomputable section
open Set Filter Matrix
open scoped Topology ContDiff BigOperators
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

def adaptedTangentBlock (u w : CoordinateSpace n → ℝ) (j : Fin n) (x : CoordinateSpace n) :
    Matrix (TangentIndex j) (TangentIndex j) ℝ :=
  (chartTangentMatrix w j x)ᵀ * coordinateHessian u x * chartTangentMatrix w j x

lemma adaptedTangentBlock_apply_dot (u w : CoordinateSpace n → ℝ) (j : Fin n)
    (x : CoordinateSpace n) (a b : TangentIndex j) :
    adaptedTangentBlock u w j x a b =
      chartTangentVector w j a x ⬝ᵥ (coordinateHessian u x *ᵥ chartTangentVector w j b x) := by
  simp only [adaptedTangentBlock, Matrix.mul_apply, Matrix.transpose_apply, chartTangentMatrix,
    dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro l _
  ring

lemma adaptedTangentBlock_apply (u w : CoordinateSpace n → ℝ) (j : Fin n)
    {x : CoordinateSpace n} (hu : ContDiffAt ℝ 2 u x) (a b : TangentIndex j) :
    adaptedTangentBlock u w j x a b =
      fderiv ℝ (fderiv ℝ u) x (chartTangentVector w j a x) (chartTangentVector w j b x) := by
  rw [adaptedTangentBlock_apply_dot,secondFDeriv_eq_hessianBilinear hu]

lemma adaptedTangentBlock_entry_formula (u w : CoordinateSpace n → ℝ) (j : Fin n)
    (x : CoordinateSpace n) (a b : TangentIndex j) :
    adaptedTangentBlock u w j x a b =
      coordinateHessian u x a b - coordinateHessian u x a j * boundaryChartCoefficient w j b x -
        boundaryChartCoefficient w j a x * coordinateHessian u x j b +
        coordinateHessian u x j j * boundaryChartCoefficient w j a x * boundaryChartCoefficient w j b x := by
  rw [adaptedTangentBlock_apply_dot]
  simp only [chartTangentVector, Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct,
    smul_dotProduct, dotProduct_sub, dotProduct_smul, Matrix.mulVec_single_one,
    single_dotProduct, one_mul, Matrix.col_apply, smul_eq_mul]
  ring

/-- Exact identification with the tangential block appearing in the
normal-completion worker's determinant-preserving shear. -/
lemma adaptedTangentBlock_eq_shear {u w : CoordinateSpace n → ℝ} {x : CoordinateSpace n}
    (hu : ContDiffAt ℝ 2 u x) (j : Fin n) :
    adaptedTangentBlock u w j x =
      (coordinateHessian u x).submatrix Subtype.val Subtype.val -
        vecMulVec (fun a : TangentIndex j => coordinateHessian u x a j)
          (fun a : TangentIndex j => boundaryChartCoefficient w j a x) -
        vecMulVec (fun a : TangentIndex j => boundaryChartCoefficient w j a x)
          (fun a : TangentIndex j => coordinateHessian u x a j) +
        coordinateHessian u x j j • vecMulVec
          (fun a : TangentIndex j => boundaryChartCoefficient w j a x)
          (fun a : TangentIndex j => boundaryChartCoefficient w j a x) := by
  ext a b
  rw [adaptedTangentBlock_entry_formula]
  have hs : coordinateHessian u x j b = coordinateHessian u x b j :=
    (coordinateHessian_isSymm_at hu).apply _ _
  simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.submatrix_apply,Matrix.vecMulVec_apply,
    Matrix.smul_apply,smul_eq_mul,hs]
  ring

/-- The actual zero-boundary jets identify the entire unknown tangential
block as a scalar multiple of the fixed defining block. -/
theorem adaptedTangentBlock_eq_scalar_defining {u w : CoordinateSpace n → ℝ}
    {x e : CoordinateSpace n} (hu : ContDiffAt ℝ 2 u x) (hw : ContDiffAt ℝ 2 w x)
    {j : Fin n} (hj : coordinateDerivative j w x ≠ 0) (he : fderiv ℝ w x e = 1)
    (hzero : ∀ᶠ y in 𝓝 x, w y = w x → u y = u x) :
    adaptedTangentBlock u w j x = (fderiv ℝ u x e) • chartTangentBlock w j x := by
  ext a b
  rw [adaptedTangentBlock_apply u w j hu,Matrix.smul_apply,chartTangentBlock_apply hw]
  exact secondFDeriv_tangent_bilinear_eq_of_level_constant hu hw he
    (chartTangentVector_tangent hj a) (chartTangentVector_tangent hj b) hzero

end GaussianTilt.MomentMapRegularity
