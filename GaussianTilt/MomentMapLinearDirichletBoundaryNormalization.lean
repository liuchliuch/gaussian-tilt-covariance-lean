import GaussianTilt.WhiteningMatrices
import GaussianTilt.MomentMapSchauderConstantCoefficients

/-! # Genuine boundary-preserving normalization of a frozen positive matrix

A true Householder isometry aligns the square-root normal. Composing it
with the actual positive square root preserves the half-space while
reducing the frozen coefficient to the Laplacian.
-/
noncomputable section
set_option maxHeartbeats 1500000
open Set Matrix InnerProductSpace
open scoped Topology BigOperators MatrixOrder
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapSchauder
variable {n : ℕ}

/-- A positive matrix has a genuine square-root coordinate map preserving
the chosen boundary plane, with no orthogonal-normalization premise. -/
theorem exists_boundary_preserving_square_root
    (j : Fin n) {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    ∃ P : KernelSpace n ≃L[ℝ] KernelSpace n, ∃ c : ℝ, 0 < c ∧
      (∀ x, (P x) j = c*x j) ∧
      ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n)).symm P.toContinuousLinearMap) *
        ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n)).symm P.toContinuousLinearMap)ᵀ = A ∧
      ‖P.toContinuousLinearMap‖ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (GaussianTilt.Whitening.root A)‖ ∧
      ‖P.symm.toContinuousLinearMap‖ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (GaussianTilt.Whitening.inverseRoot A)‖ := by
  let e := GaussianTilt.Whitening.rootEquiv hA
  let R : KernelSpace n →L[ℝ] KernelSpace n := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (GaussianTilt.Whitening.root A)
  let ej := EuclideanSpace.basisFun (Fin n) ℝ j
  let b := e ej
  let c := ‖b‖
  have hej : ‖ej‖ = 1 := by simp [ej, EuclideanSpace.basisFun_apply]
  have hb : b ≠ 0 := by
    intro hz
    have he : ej = 0 := e.injective (by simpa only [map_zero] using hz)
    rw [he, norm_zero] at hej
    norm_num at hej
  have hc : 0 < c := norm_pos_iff.mpr hb
  have hbn : ‖b‖ = ‖c • ej‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc, hej, mul_one]
  let Q : KernelSpace n ≃ₗᵢ[ℝ] KernelSpace n := (Submodule.span ℝ {b-c • ej})ᗮ.reflection
  have hQ : Q b = c • ej := Submodule.reflection_sub hbn
  have hQsym : Q.symm = Q := Submodule.reflection_symm
  let P := Q.toContinuousLinearEquiv.trans e
  have hP (x : KernelSpace n) : P x = e (Q x) := rfl
  have hRstar : star R = R := by
    dsimp only [R]
    rw [← map_star]
    exact congrArg (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n))
      (GaussianTilt.Whitening.root_posDef hA).isHermitian.isSelfAdjoint
  have hRs : (R : KernelSpace n →ₗ[ℝ] KernelSpace n).IsSymmetric :=
    (show IsSelfAdjoint R from hRstar).isSymmetric
  have hplane (x : KernelSpace n) : (P x) j = c*x j := by
    rw [hP]
    calc
      _ = inner ℝ ej (e (Q x)) := (EuclideanSpace.basisFun_inner (Fin n) ℝ (e (Q x)) j).symm
      _ = inner ℝ b (Q x) := (hRs ej (Q x)).symm
      _ = inner ℝ (Q b) x := by
        have hh := Q.inner_map_eq_flip b x
        rw [hQsym] at hh
        exact hh.symm
      _ = c*x j := by rw [hQ, inner_smul_left]; simp only [conj_trivial, ej, EuclideanSpace.basisFun_inner]
  have hQQ : (Q.toContinuousLinearEquiv.toContinuousLinearMap) * star (Q.toContinuousLinearEquiv.toContinuousLinearMap) = 1 := by
    have hQA : ContinuousLinearMap.adjoint Q.toContinuousLinearEquiv.toContinuousLinearMap =
        Q.symm.toContinuousLinearEquiv.toContinuousLinearMap := Q.adjoint_eq_symm
    rw [ContinuousLinearMap.star_eq_adjoint, hQA]
    apply ContinuousLinearMap.ext
    intro x
    exact Q.apply_symm_apply x
  have hPR : P.toContinuousLinearMap = R * Q.toContinuousLinearEquiv.toContinuousLinearMap := rfl
  have hRR : R*R = Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) A := by
    dsimp only [R]
    rw [← map_mul, GaussianTilt.Whitening.root_mul_root hA.posSemidef]
  have hPP : P.toContinuousLinearMap * star P.toContinuousLinearMap = Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) A := by
    rw [hPR, StarMul.star_mul, hRstar]
    calc
      _ = R*(Q.toContinuousLinearEquiv.toContinuousLinearMap * star Q.toContinuousLinearEquiv.toContinuousLinearMap)*R := by
        simp only [mul_assoc]
      _ = _ := by rw [hQQ, mul_one, hRR]
  refine ⟨P, c, hc, hplane, ?_, ?_, ?_⟩
  · apply (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n)).injective
    rw [map_mul]
    have htr (M : Matrix (Fin n) (Fin n) ℝ) : Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) Mᵀ = star (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) M) := by
      simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
        (map_star (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n)) M)
    change Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n)
      ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n)).symm P.toContinuousLinearMap) *
      Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n)
      (((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n)).symm P.toContinuousLinearMap)ᵀ) =
      Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) A
    rw [htr, StarAlgEquiv.apply_symm_apply]
    exact hPP
  · apply P.toContinuousLinearMap.opNorm_le_bound (norm_nonneg _)
    intro x
    change ‖e (Q x)‖ ≤ ‖R‖*‖x‖
    exact (R.le_opNorm (Q x)).trans_eq (by rw [Q.norm_map])
  · apply P.symm.toContinuousLinearMap.opNorm_le_bound (norm_nonneg _)
    intro x
    change ‖Q.symm (e.symm x)‖ ≤ _
    rw [Q.symm.norm_map]
    exact (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (GaussianTilt.Whitening.inverseRoot A)).le_opNorm x

end GaussianTilt.MomentMapLinearDirichlet
