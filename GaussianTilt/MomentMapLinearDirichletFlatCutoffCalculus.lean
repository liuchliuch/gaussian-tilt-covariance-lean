import GaussianTilt.MomentMapLinearDirichletFlatCutoff
import GaussianTilt.MomentMapSchauderEuclideanCutoff

/-! # Literal coordinate boundary-layer cutoff calculus -/
noncomputable section
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 1000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapSchauder
variable {n : ℕ}

lemma contDiff_coordinate_profile {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η) (j : Fin n) :
    ContDiff ℝ ∞ (fun x : KernelSpace n => η (x j)) :=
  hη.comp (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) j).contDiff

lemma kernelDerivative_coordinate_profile {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η)
    (j i : Fin n) (x : KernelSpace n) :
    kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i) (fun y => η (y j)) x =
      if i = j then deriv η (x j) else 0 := by
  classical
  let L : KernelSpace n →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin n => ℝ) j
  have h := ((hη.differentiable (by simp) (x j)).hasDerivAt).comp_hasFDerivAt x L.hasFDerivAt
  change HasFDerivAt (fun y : KernelSpace n => η (y j)) _ x at h
  unfold kernelDirectionalDerivative
  rw [h.fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  change deriv η (x j) * (EuclideanSpace.basisFun (Fin n) ℝ i) j = _
  by_cases hij : i = j
  · subst i; simp
  · simp [EuclideanSpace.basisFun_apply, EuclideanSpace.single_apply, hij, Ne.symm hij]

lemma kernelLaplacian_coordinate_profile {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η)
    (j : Fin n) (x : KernelSpace n) :
    kernelLaplacian (fun y => η (y j)) x = deriv (deriv η) (x j) := by
  classical
  have hd : ContDiff ℝ ∞ (deriv η) := (hη.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have he (i : Fin n) : kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i)
      (fun y => η (y j)) = if i = j then (fun y => deriv η (y j)) else (fun _ => 0) := by
    funext y
    rw [kernelDerivative_coordinate_profile hη]
    split_ifs <;> rfl
  have hterm (i : Fin n) : directionalHessian (fun y => η (y j)) x
      (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ i) =
        if i = j then deriv (deriv η) (x j) else 0 := by
    change kernelDirectionalDerivative _ (kernelDirectionalDerivative _ (fun y => η (y j))) x = _
    rw [he]
    split_ifs with hij
    · subst i
      simpa using kernelDerivative_coordinate_profile hd j j x
    · simp [kernelDirectionalDerivative]
  simp only [kernelLaplacian, hterm, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

lemma kernelLaplacian_mul_C2 {u χ : KernelSpace n → ℝ}
    (hu : ContDiff ℝ 2 u) (hχ : ContDiff ℝ 2 χ) (x : KernelSpace n) :
    kernelLaplacian (fun y => χ y * u y) x = χ x * kernelLaplacian u x +
      u x * kernelLaplacian χ x + 2 * ∑ i : Fin n,
        kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i) χ x *
          kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i) u x := by
  simp only [kernelLaplacian, directionalHessian_eq_fderiv_fderiv (hχ.mul hu),
    directionalHessian_eq_fderiv_fderiv hu, directionalHessian_eq_fderiv_fderiv hχ,
    secondFrechet_mul_apply hu hχ, Finset.sum_add_distrib, Finset.mul_sum, kernelDirectionalDerivative]
  repeat' rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma kernelLaplacian_coordinate_cutoff {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η)
    {ψ : KernelSpace n → ℝ} (hψ : ContDiff ℝ ∞ ψ) (j : Fin n) (x : KernelSpace n) :
    kernelLaplacian (fun y => η (y j) * ψ y) x =
      η (x j) * kernelLaplacian ψ x + ψ x * deriv (deriv η) (x j) +
        2 * deriv η (x j) * kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ j) ψ x := by
  classical
  rw [kernelLaplacian_mul_C2 (contDiff_infty.mp hψ 2) (contDiff_infty.mp (contDiff_coordinate_profile hη j) 2),
    kernelLaplacian_coordinate_profile hη]
  simp_rw [kernelDerivative_coordinate_profile hη, ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  ring

lemma tsupport_scaledFlatBoundaryStep_mul {ε : ℝ} {ψ : KernelSpace n → ℝ} (j : Fin n) :
    tsupport (fun x : KernelSpace n => scaledFlatBoundaryStep ε (x j) * ψ x) ⊆ tsupport ψ :=
  tsupport_mul_subset_right

lemma tsupport_scaledFlatBoundaryStep_mul_positive {ε : ℝ} (hε : 0 < ε)
    (ψ : KernelSpace n → ℝ) (j : Fin n) :
    tsupport (fun x : KernelSpace n => scaledFlatBoundaryStep ε (x j) * ψ x) ⊆ {x | 0 < x j} := by
  have hs : tsupport (fun x : KernelSpace n => scaledFlatBoundaryStep ε (x j) * ψ x) ⊆ {x | ε ≤ x j} := by
    apply closure_minimal _ (isClosed_le continuous_const (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) j).continuous)
    intro x hx
    by_contra hnot
    have ht : x j ≤ ε := (lt_of_not_ge hnot).le
    exact hx (by dsimp only; rw [scaledFlatBoundaryStep_zero hε ht, zero_mul])
  exact fun x hx => hε.trans_le (hs hx)

end GaussianTilt.MomentMapLinearDirichlet
