import GaussianTilt.MomentMapLinearDirichletFlatBoundaryTest

/-!
# Genuine odd reflection of the flat weak harmonic equation

Measure preservation and the actual Laplacian covariance convert reflected
compact tests into odd tests. The proved boundary-layer limit makes those
odd tests admissible. Thus the odd extension is distribution-harmonic on
the full ball, and the actual Weyl construction supplies smoothness.
-/
noncomputable section
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 1000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma kernelLaplacian_sub_C2 {f g : KernelSpace n → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : KernelSpace n) :
    kernelLaplacian (fun y => f y - g y) x = kernelLaplacian f x - kernelLaplacian g x := by
  have hd (v : KernelSpace n) : (fun y => fderiv ℝ (fun z => f z - g z) y v) =
      fun y => fderiv ℝ f y v - fderiv ℝ g y v := by
    funext y
    rw [fderiv_fun_sub (hf.differentiable (by norm_num) y) (hg.differentiable (by norm_num) y),
      ContinuousLinearMap.sub_apply]
  simp only [kernelLaplacian, directionalHessian, hd,
    fderiv_fun_sub ((contDiff_directional_fderiv hf _).differentiable le_rfl x)
      ((contDiff_directional_fderiv hg _).differentiable le_rfl x),
    ContinuousLinearMap.sub_apply, Finset.sum_sub_distrib]

def flatOddExtension (j : Fin n) (u : KernelSpace n → ℝ) (x : KernelSpace n) : ℝ :=
  u x - u (flatReflection j x)

lemma flatOddExtension_eq_upper (j : Fin n) {u : KernelSpace n → ℝ}
    (hu0 : ∀ x, x j ≤ 0 → u x = 0) {x : KernelSpace n} (hx : 0 ≤ x j) :
    flatOddExtension j u x = u x := by
  have hT : u (flatReflection j x) = 0 := hu0 (flatReflection j x) (by
    rw [flatReflection_apply, if_pos rfl]
    exact neg_nonpos.mpr hx)
  rw [flatOddExtension, hT, sub_zero]

lemma flatOddExtension_reflect (j : Fin n) (u : KernelSpace n → ℝ) (x : KernelSpace n) :
    flatOddExtension j u (flatReflection j x) = -flatOddExtension j u x := by
  rw [flatOddExtension, flatReflection_involutive, flatOddExtension]
  ring

lemma flatOddExtension_memLp (j : Fin n) {u : KernelSpace n → ℝ} (hu : MemLp u 2 volume) :
    MemLp (flatOddExtension j u) 2 volume := hu.sub (hu.comp_measurePreserving (flatReflection j).measurePreserving)

/-- Odd reflection genuinely removes the flat boundary for the literal
weak harmonic equation. The linear boundary bound is the only boundary
input, and the cutoff-limit theorem proves its admissibility consequence. -/
theorem flatOddExtension_distribution_harmonic (j : Fin n) {u : KernelSpace n → ℝ}
    (hu : MemLp u 2 volume) {R C : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hu0 : ∀ x, x j ≤ 0 → u x = 0)
    (hug : ∀ x ∈ Metric.ball (0 : KernelSpace n) R, |u x| ≤ C * |x j|)
    (heq : ∀ φ : KernelSpace n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Metric.ball 0 R ∩ {x | 0 < x j} → (∫ x, u x * kernelLaplacian φ x) = 0) :
    ∀ ψ : KernelSpace n → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Metric.ball 0 R → (∫ x, flatOddExtension j u x * kernelLaplacian ψ x) = 0 := by
  intro ψ hψ hψc hψR
  have hui := hu.locallyIntegrable (by norm_num)
  have huTi := (hu.comp_measurePreserving (flatReflection j).measurePreserving).locallyIntegrable (by norm_num)
  have hψT : ContDiff ℝ ∞ (ψ ∘ flatReflection j) := hψ.comp (flatReflection j).toContinuousLinearEquiv.contDiff
  have hψTc : HasCompactSupport (ψ ∘ flatReflection j) := hψc.comp_homeomorph (flatReflection j).toHomeomorph
  have hψ2 := contDiff_infty.mp hψ 2
  have hψT2 := contDiff_infty.mp hψT 2
  have hi1 := integrable_locally_mul_laplacian hui hψ2 hψc
  have hi2 := integrable_locally_mul_laplacian huTi hψ2 hψc
  have hi3 := integrable_locally_mul_laplacian hui hψT2 hψTc
  dsimp only [Function.comp_def] at hi2
  have hchange : (∫ x, u (flatReflection j x) * kernelLaplacian ψ x) =
      ∫ x, u x * kernelLaplacian (ψ ∘ flatReflection j) x := by
    have hh := (flatReflection j).measurePreserving.integral_comp
      (flatReflection j).toHomeomorph.measurableEmbedding
      (fun x => u (flatReflection j x) * kernelLaplacian ψ x)
    have hTT (x : KernelSpace n) : flatReflection j (flatReflection j x) = x := flatReflection_involutive j x
    simpa only [hTT, kernelLaplacian_flatReflection hψ2] using hh.symm
  have htest := integral_mul_laplacian_flat_zero_test j hui hR hC hu0 hug heq
    (contDiff_oddReflectionTest j hψ) (hasCompactSupport_oddReflectionTest j hψc)
    (tsupport_oddReflectionTest_subset_ball j hψR) (fun x hx => oddReflectionTest_zero_on_plane j ψ hx)
  have hlap (x : KernelSpace n) : kernelLaplacian (oddReflectionTest j ψ) x =
      kernelLaplacian ψ x - kernelLaplacian (ψ ∘ flatReflection j) x :=
    kernelLaplacian_sub_C2 hψ2 hψT2 x
  simp_rw [hlap, mul_sub] at htest
  rw [integral_sub hi1 hi3] at htest
  simp only [flatOddExtension, sub_mul]
  rw [integral_sub hi1 hi2, hchange]
  exact htest

/-- The odd extension has a genuine smooth representative on the full
ball, including the former boundary hyperplane. -/
theorem flatOddExtension_smooth_representative [NeZero n] (j : Fin n) {u : KernelSpace n → ℝ}
    (hu : MemLp u 2 volume) {R C : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hu0 : ∀ x, x j ≤ 0 → u x = 0)
    (hug : ∀ x ∈ Metric.ball (0 : KernelSpace n) R, |u x| ≤ C * |x j|)
    (heq : ∀ φ : KernelSpace n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Metric.ball 0 R ∩ {x | 0 < x j} → (∫ x, u x * kernelLaplacian φ x) = 0) :
    (harmonicRepresentative (flatOddExtension j u) =ᵐ[volume] flatOddExtension j u) ∧
      ∀ x ∈ Metric.ball 0 R, ContDiffAt ℝ ∞ (harmonicRepresentative (flatOddExtension j u)) x := by
  have hi := (flatOddExtension_memLp j hu).locallyIntegrable (by norm_num)
  refine ⟨harmonicRepresentative_ae_eq hi, ?_⟩
  apply harmonicRepresentative_contDiffAt_of_distribution_harmonic Metric.isOpen_ball hi
    (B := 2*C*R) _ (flatOddExtension_distribution_harmonic j hu hR hC hu0 hug heq)
  intro x hx
  have hxT : flatReflection j x ∈ Metric.ball (0 : KernelSpace n) R := by
    simpa only [Metric.mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map] using hx
  have hcoord : |x j| ≤ R := (show |x j| ≤ ‖x‖ by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x j).trans
    (show ‖x‖ < R by simpa only [Metric.mem_ball, dist_zero_right] using hx).le
  have hTx : |flatReflection j x j| = |x j| := by simp [flatReflection_apply]
  have h1 := (hug x hx).trans (mul_le_mul_of_nonneg_left hcoord hC)
  have h2 := hug (flatReflection j x) hxT
  rw [hTx] at h2
  have h2' := h2.trans (mul_le_mul_of_nonneg_left hcoord hC)
  exact (abs_sub _ _).trans (by linarith)

end GaussianTilt.MomentMapLinearDirichlet
