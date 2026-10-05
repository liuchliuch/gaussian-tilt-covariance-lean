import GaussianTilt.MomentMapLinearDirichletBoundaryNormalization
import GaussianTilt.MomentMapLinearDirichletFlatteningPullback
import GaussianTilt.MomentMapLinearDirichletHarmonicKernel
import GaussianTilt.MomentMapSchauderLocalPatch

/-! # Quantitative half-space normalization and actual local frozen-PDE covariance -/
noncomputable section
set_option maxHeartbeats 1000000
open Set Filter Matrix
open scoped Topology ContDiff
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapSchauder
variable {n : ℕ}

lemma kernelLaplacian_comp_equiv_of_covariance
    (P : KernelSpace n ≃L[ℝ] KernelSpace n) {A : Matrix (Fin n) (Fin n) ℝ}
    (hPP : ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n)).symm P.toContinuousLinearMap) *
      ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n)).symm P.toContinuousLinearMap)ᵀ = A)
    {u : KernelSpace n → ℝ} (hu : ContDiff ℝ 2 u) (x : KernelSpace n) :
    kernelLaplacian (u ∘ P) x = euclideanEllipticOperator A u (P x) := by
  have he := kernelLaplacian_comp_matrix hu
    ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n)).symm P.toContinuousLinearMap) x
  rw [hPP, StarAlgEquiv.apply_symm_apply] at he
  exact he

/-- Only the actual local C² regularity of u at P x is required. -/
lemma kernelLaplacian_comp_equiv_of_covariance_at
    (P : KernelSpace n ≃L[ℝ] KernelSpace n) {A : Matrix (Fin n) (Fin n) ℝ}
    (hPP : ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n)).symm P.toContinuousLinearMap) *
      ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n)).symm P.toContinuousLinearMap)ᵀ = A)
    {u : KernelSpace n → ℝ} {x : KernelSpace n} (hu : ContDiffAt ℝ 2 u (P x)) :
    kernelLaplacian (u ∘ P) x = euclideanEllipticOperator A u (P x) := by
  obtain ⟨v, hv, he⟩ := exists_global_contDiff_eventuallyEq 2 hu
  have heP : v ∘ P =ᶠ[𝓝 x] u ∘ P := P.continuous.continuousAt.tendsto.eventually he
  rw [← kernelLaplacian_congr_nhds heP, kernelLaplacian_comp_equiv_of_covariance P hPP hv,
    euclideanEllipticOperator_congr_nhds he A]

/-- The constructed map has radius constants controlled by the actual
lower/upper ellipticity and preserves the positive normal coordinate. -/
theorem exists_quantitative_boundary_normalization
    (j : Fin n) {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    {lam Λ : ℝ} (hlam : 0 < lam) (hΛ : 0 ≤ Λ)
    (hlower : ∀ v : KernelSpace n, lam*‖v‖^2 ≤ euclideanQuadratic A v)
    (hupper : ∀ v : KernelSpace n, euclideanQuadratic A v ≤ Λ*‖v‖^2) :
    ∃ P : KernelSpace n ≃L[ℝ] KernelSpace n, ∃ c : ℝ, 0 < c ∧
      (∀ x, (P x) j=c*x j) ∧
      (∀ x, (P.symm x) j=c⁻¹*x j) ∧
      ‖P.toContinuousLinearMap‖ ≤ Real.sqrt Λ ∧
      ‖P.symm.toContinuousLinearMap‖ ≤ (Real.sqrt lam)⁻¹ ∧
      (∀ (u : KernelSpace n → ℝ) (x : KernelSpace n), ContDiffAt ℝ 2 u (P x) →
        kernelLaplacian (u ∘ P) x=euclideanEllipticOperator A u (P x)) ∧
      ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n)).symm P.toContinuousLinearMap) *
        ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n)).symm P.toContinuousLinearMap)ᵀ = A := by
  obtain ⟨P,c,hc,hplane,hPP,hP,hI⟩ := exists_boundary_preserving_square_root j hA
  refine ⟨P,c,hc,hplane,?_,hP.trans (norm_coefficient_sqrt_le hA hΛ hupper),
    hI.trans (norm_inverse_coefficient_sqrt_le hA hlam hlower),?_,hPP⟩
  · intro x
    have he := hplane (P.symm x)
    rw [P.apply_symm_apply] at he
    apply (mul_left_cancel₀ hc.ne')
    rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
    exact he.symm
  · intro u x hu
    exact kernelLaplacian_comp_equiv_of_covariance_at P hPP hu

lemma boundary_normalization_maps_halfball
    (P : KernelSpace n ≃L[ℝ] KernelSpace n) (j : Fin n) {c M r : ℝ}
    (hc : 0 < c) (hM : 0 < M) (hP : ‖P.toContinuousLinearMap‖ ≤ M)
    (hplane : ∀ x, (P x) j=c*x j) :
    MapsTo P {x | ‖x‖ < r/M ∧ 0 < x j} {x | ‖x‖ < r ∧ 0 < x j} ∧
      MapsTo P {x | ‖x‖ ≤ r/M ∧ 0 ≤ x j} {x | ‖x‖ ≤ r ∧ 0 ≤ x j} := by
  have hn (x : KernelSpace n) : ‖P x‖ ≤ M*‖x‖ :=
    (P.toContinuousLinearMap.le_opNorm x).trans (mul_le_mul_of_nonneg_right hP (norm_nonneg _))
  constructor
  · intro x hx
    refine ⟨?_, ?_⟩
    · have hh := (lt_div_iff₀ hM).mp hx.1
      nlinarith [hn x]
    · rw [hplane]
      exact mul_pos hc hx.2
  · intro x hx
    refine ⟨?_, ?_⟩
    · have hh := (le_div_iff₀ hM).mp hx.1
      nlinarith [hn x]
    · rw [hplane]
      exact mul_nonneg hc.le hx.2

end GaussianTilt.MomentMapLinearDirichlet
