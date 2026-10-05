import GaussianTilt.MomentMapLinearDirichletFlatCutoffCalculus
import GaussianTilt.MomentMapLinearDirichletFlatReflection

/-! # Actual uniform bounds for compact tests vanishing on a flat boundary -/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff NNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma flatProjection_coordinate (j : Fin n) (x : KernelSpace n) :
    (x - x j • EuclideanSpace.basisFun (Fin n) ℝ j) j = 0 := by simp

lemma norm_sub_flatProjection (j : Fin n) (x : KernelSpace n) :
    ‖x - (x - x j • EuclideanSpace.basisFun (Fin n) ℝ j)‖ = |x j| := by
  rw [sub_sub_cancel, norm_smul, Real.norm_eq_abs,
    (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.norm_eq_one, mul_one]

/-- Zero boundary values give a true linear height bound by the actual
mean-value theorem and compact derivative bounds. -/
theorem exists_flat_test_bounds (j : Fin n) {ψ : KernelSpace n → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hzero : ∀ x : KernelSpace n, x j = 0 → ψ x = 0) :
    ∃ D M : ℝ, 0 ≤ D ∧ 0 ≤ M ∧
      (∀ x, |ψ x| ≤ D * |x j|) ∧
      (∀ x, |kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ j) ψ x| ≤ D) ∧
      (∀ x, |kernelLaplacian ψ x| ≤ M) := by
  obtain ⟨B, hB⟩ := (hψc.fderiv ℝ).exists_bound_of_continuous (hψ.continuous_fderiv (by simp))
  let D := max B 0
  have hD : 0 ≤ D := le_max_right _ _
  have hd (x : KernelSpace n) : ‖fderiv ℝ ψ x‖ ≤ D := (hB x).trans (le_max_left _ _)
  let L : ℝ≥0 := ⟨D, hD⟩
  have hLip : LipschitzWith L ψ := lipschitzWith_of_nnnorm_fderiv_le
    (hψ.differentiable (by simp)) (fun x => hd x)
  obtain ⟨M, hM⟩ := (hasCompactSupport_kernelLaplacian hψc).exists_bound_of_continuous
    (continuous_kernelLaplacian (contDiff_infty.mp hψ 2))
  refine ⟨D, max M 0, hD, le_max_right _ _, ?_, ?_, ?_⟩
  · intro x
    have hh := hLip.norm_sub_le x (x - x j • EuclideanSpace.basisFun (Fin n) ℝ j)
    rw [hzero _ (flatProjection_coordinate j x), sub_zero, Real.norm_eq_abs,
      norm_sub_flatProjection] at hh
    exact hh
  · intro x
    have hh := (fderiv ℝ ψ x).le_opNorm (EuclideanSpace.basisFun (Fin n) ℝ j)
    rw [(EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.norm_eq_one, mul_one] at hh
    exact hh.trans (hd x)
  · intro x
    exact (hM x).trans (le_max_left _ _)

end GaussianTilt.MomentMapLinearDirichlet
