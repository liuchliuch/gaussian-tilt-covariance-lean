import GaussianTilt.MomentMapLinearDirichletQuantitativeChartRaw

/-! # Matrix bounds and nonsingularity from actual inverse-chart derivatives -/
noncomputable section
set_option maxHeartbeats 2000000
open Matrix Set
open scoped BigOperators ContDiff Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapRegularity
variable {n : ℕ}

lemma euclideanCLMMatrix_comp (J G : KernelSpace n →L[ℝ] KernelSpace n) :
    euclideanCLMMatrix (J.comp G)=euclideanCLMMatrix J*euclideanCLMMatrix G := by
  exact (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).symm.map_mul J G

lemma euclideanCLMMatrix_id :
    euclideanCLMMatrix (ContinuousLinearMap.id ℝ (KernelSpace n))=(1:Matrix (Fin n) (Fin n) ℝ) :=
  (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).symm.map_one

lemma euclideanCLMMatrix_entry_bound (J : KernelSpace n →L[ℝ] KernelSpace n)
    {C : ℝ} (hJ : ‖J‖ ≤ C) (i k : Fin n) : |euclideanCLMMatrix J i k| ≤ C := by
  rw [euclideanCLMMatrix_entry]
  have hc : |(J (EuclideanSpace.basisFun (Fin n) ℝ k)) i| ≤
      ‖J (EuclideanSpace.basisFun (Fin n) ℝ k)‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (J (EuclideanSpace.basisFun (Fin n) ℝ k)) i
  have hb : ‖J (EuclideanSpace.basisFun (Fin n) ℝ k)‖ ≤ ‖J‖ := by
    simpa only [(EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.norm_eq_one, mul_one] using
      J.le_opNorm (EuclideanSpace.basisFun (Fin n) ℝ k)
  exact hc.trans (hb.trans hJ)

lemma flatteningJacobian_eq_derivative_matrix {w : KernelSpace n → ℝ}
    (hw : ContDiff ℝ ∞ w) (a : KernelSpace n) (j : Fin n) (x : KernelSpace n) :
    flatteningJacobian w j x=euclideanCLMMatrix (fderiv ℝ (flatteningMap w a j) x) := by
  rw [(hasFDerivAt_flatteningMap (hw.differentiable (by simp) x) a j).fderiv]
  rfl

/-- Both matrix bounds and the inverse equation come from derivatives of
the genuine chart maps. No algebraic nonsingularity hypothesis is added. -/
theorem regularLevel_chart_matrix_bounds {w : KernelSpace n → ℝ}
    (hw : ContDiff ℝ ∞ w) (a : KernelSpace n) (j : Fin n)
    (hj : fderiv ℝ w a (EuclideanSpace.basisFun (Fin n) ℝ j) ≠ 0)
    {z : KernelSpace n} {C : ℝ}
    (hz : z ∈ (regularLevelFlatteningChart hw a j hj).target)
    (hg : DifferentiableAt ℝ (regularLevelFlatteningChart hw a j hj).symm z)
    (hG : ‖fderiv ℝ (regularLevelFlatteningChart hw a j hj).symm z‖ ≤ C)
    (hJ : ‖fderiv ℝ (flatteningMap w a j) ((regularLevelFlatteningChart hw a j hj).symm z)‖ ≤ C) :
    let J := flatteningJacobian w j ((regularLevelFlatteningChart hw a j hj).symm z)
    let G := euclideanCLMMatrix (fderiv ℝ (regularLevelFlatteningChart hw a j hj).symm z)
    J*G=1 ∧ (∀ i k, |J i k| ≤ C) ∧ (∀ i k, |G i k| ≤ C) := by
  dsimp only
  rw [flatteningJacobian_eq_derivative_matrix hw a j]
  refine ⟨?_,euclideanCLMMatrix_entry_bound _ hJ,euclideanCLMMatrix_entry_bound _ hG⟩
  rw [← euclideanCLMMatrix_comp,(regularLevel_chart_derivative_inverse hw a j hj hz hg).1,euclideanCLMMatrix_id]

end GaussianTilt.MomentMapLinearDirichlet
