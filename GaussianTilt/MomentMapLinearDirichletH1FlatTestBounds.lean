import GaussianTilt.MomentMapLinearDirichletFlatBoundaryTest

/-! # First-order flat test bounds for genuine Sobolev reflection

Only the smooth test, rather than the weak solution, has a height bound.
This suffices for the first-order weak equation and avoids any pointwise
trace or linear-growth assumption on a Sobolev harmonic replacement.
-/
noncomputable section
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 1000
open MeasureTheory Set Filter
open scoped Topology ContDiff BigOperators
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma kernelDerivative_mul_infty {f g : KernelSpace n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (v x : KernelSpace n) :
    kernelDirectionalDerivative v (fun y => f y*g y) x=
      kernelDirectionalDerivative v f x*g x+f x*kernelDirectionalDerivative v g x := by
  unfold kernelDirectionalDerivative
  rw [fderiv_fun_mul (hf.differentiable (by simp) x) (hg.differentiable (by simp) x)]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
  ring

lemma kernelDerivative_coordinate_cutoff {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η)
    {ψ : KernelSpace n → ℝ} (hψ : ContDiff ℝ ∞ ψ) (j i : Fin n) (x : KernelSpace n) :
    kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i) (fun y => η (y j)*ψ y) x=
      (if i=j then deriv η (x j) else 0)*ψ x+
      η (x j)*kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i) ψ x := by
  rw [kernelDerivative_mul_infty (contDiff_coordinate_profile hη j) hψ,
    kernelDerivative_coordinate_profile hη]

lemma kernelDerivative_congr_nhds {f g : KernelSpace n → ℝ} {x : KernelSpace n}
    (he : f =ᶠ[𝓝 x] g) (v : KernelSpace n) :
    kernelDirectionalDerivative v f x=kernelDirectionalDerivative v g x := by
  unfold kernelDirectionalDerivative
  rw [he.fderiv_eq]

lemma kernelDerivative_zero_off_tsupport (f : KernelSpace n → ℝ) (v : KernelSpace n)
    {x : KernelSpace n} (hx : x ∉ tsupport f) : kernelDirectionalDerivative v f x=0 := by
  unfold kernelDirectionalDerivative
  rw [fderiv_of_notMem_tsupport ℝ hx]
  rfl

lemma exists_flat_test_first_bounds (j : Fin n) {ψ : KernelSpace n → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψ0 : ∀ x, x j=0 → ψ x=0) :
    ∃ D : ℝ, 0 ≤ D ∧ (∀ x, |ψ x| ≤ D*|x j|) ∧
      ∀ i x, |kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i) ψ x| ≤ D := by
  obtain ⟨D₀,M,hD₀,hM,hheight,_,_⟩ := exists_flat_test_bounds j hψ hψc hψ0
  obtain ⟨B,hB⟩ := (hψc.fderiv ℝ).exists_bound_of_continuous (hψ.continuous_fderiv (by simp))
  let D := max D₀ B
  refine ⟨D,hD₀.trans (le_max_left _ _),?_,?_⟩
  · intro x
    exact (hheight x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
  · intro i x
    have hh := (fderiv ℝ ψ x).le_opNorm (EuclideanSpace.basisFun (Fin n) ℝ i)
    rw [(EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.norm_eq_one,mul_one] at hh
    exact hh.trans ((hB x).trans (le_max_right _ _))

/-- All derivatives of the first-order cutoff test are uniformly bounded;
the cancellation uses only the actual smooth test's zero boundary value. -/
lemma scaledFlatBoundaryStep_test_first_bound (j i : Fin n) {ψ : KernelSpace n → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) {ε D M : ℝ} (hε : 0 < ε) (hD : 0 ≤ D) (hM : 0 ≤ M)
    (hheight : ∀ x, |ψ x| ≤ D*|x j|)
    (hgrad : ∀ i x, |kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i) ψ x| ≤ D)
    (hstep : ∀ t, |deriv flatBoundaryStep t| ≤ M) (x : KernelSpace n) :
    |kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i)
      (fun y => scaledFlatBoundaryStep ε (y j)*ψ y) x| ≤ D+2*M*D := by
  by_cases hx : x j ≤ 0
  · have hneigh : (fun y : KernelSpace n => scaledFlatBoundaryStep ε (y j)*ψ y) =ᶠ[𝓝 x] (fun _ => 0) := by
      have ht : x j < ε := lt_of_le_of_lt hx hε
      filter_upwards [(isOpen_lt (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) j).continuous continuous_const).mem_nhds ht]
        with y hy
      change y j < ε at hy
      rw [scaledFlatBoundaryStep_zero hε hy.le,zero_mul]
    rw [kernelDerivative_congr_nhds hneigh]
    have hz : kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i) (fun _ : KernelSpace n => (0:ℝ)) x=0 := by
      simp [kernelDirectionalDerivative]
    rw [hz,abs_zero]
    positivity
  · have hxpos : 0 < x j := lt_of_not_ge hx
    rw [kernelDerivative_coordinate_cutoff (scaledFlatBoundaryStep_contDiff ε) hψ]
    have hs : |scaledFlatBoundaryStep ε (x j)| ≤ 1 := by
      unfold scaledFlatBoundaryStep
      rw [abs_of_nonneg (flatBoundaryStep_nonneg _)]
      exact flatBoundaryStep_le_one _
    have hmain : |scaledFlatBoundaryStep ε (x j)*kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i) ψ x| ≤ D := by
      rw [abs_mul]
      simpa only [one_mul] using mul_le_mul hs (hgrad i x) (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
    have herr : |(if i=j then deriv (scaledFlatBoundaryStep ε) (x j) else 0)*ψ x| ≤ 2*M*D := by
      split_ifs
      · have hh := scaledFlatBoundaryStep_weighted_deriv_bound hε hxpos.le hM hstep
        have hv := hheight x
        rw [abs_of_pos hxpos] at hv
        rw [abs_mul]
        have hm := mul_le_mul_of_nonneg_left hv (abs_nonneg (deriv (scaledFlatBoundaryStep ε) (x j)))
        nlinarith [mul_le_mul_of_nonneg_right hh hD]
      · simp only [zero_mul,abs_zero]
        positivity
    exact (abs_add_le _ _).trans (by linarith)

end GaussianTilt.MomentMapLinearDirichlet
