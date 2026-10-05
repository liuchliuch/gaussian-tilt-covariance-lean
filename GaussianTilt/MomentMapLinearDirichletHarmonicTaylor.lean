import GaussianTilt.MomentMapLinearDirichletSmoothingDerivatives

/-!
# A genuine dimension-only harmonic quadratic approximation

The compact Newtonian smoothing kernel and its finite third-derivative
integral give a uniform Hessian Lipschitz bound. Actual Taylor's theorem
then yields a cubic remainder, with a constant independent of the locally
harmonic function. This is the harmonic improvement step for boundary
Campanato iteration after odd reflection.
-/
noncomputable section
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff Convolution
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapSchauder
variable {n : ℕ}

def interiorHarmonicBump (n : ℕ) : ContDiffBump (0 : KernelSpace n) :=
  ⟨1/4, 1/2, by norm_num, by norm_num⟩

lemma interiorHarmonicBump_eventually_one (n : ℕ) :
    (interiorHarmonicBump n : KernelSpace n → ℝ) =ᶠ[𝓝 0] (fun _ => 1) := by
  filter_upwards [Metric.ball_mem_nhds (0 : KernelSpace n) (by norm_num : (0 : ℝ) < 1/4)] with x hx
  exact (interiorHarmonicBump n).one_of_mem_closedBall (Metric.ball_subset_closedBall hx)

lemma harmonicSmoothing_eq_vectorKernelConvolution (χ f : KernelSpace n → ℝ) :
    harmonicSmoothing χ f = vectorKernelConvolution (fun y => harmonicSmoothingKernel χ (-y)) f := by
  rw [harmonicSmoothing_eq_convolution]
  have hL : rightScalarMul ℝ = (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) := by
    ext a b
    simp [rightScalarMul, mul_comm]
  simp only [vectorKernelConvolution, hL]

lemma interior_harmonic_reproducing [NeZero n] {h : KernelSpace n → ℝ}
    (hh : ContDiff ℝ 2 h) (hhc : HasCompactSupport h)
    (hharm : ∀ y ∈ Metric.ball (0 : KernelSpace n) 1, kernelLaplacian h y = 0)
    {x : KernelSpace n} (hx : x ∈ Metric.ball (0 : KernelSpace n) (1/4)) :
    (2 * (n : ℝ) * fundamentalApproxMass n)⁻¹ * harmonicSmoothing (interiorHarmonicBump n) h x = h x := by
  have he := harmonicSmoothingKernel_reproduces_at (interiorHarmonicBump n).contDiff
    (interiorHarmonicBump_eventually_one n) hh hhc x (by
      intro y hy
      apply hharm
      rw [(interiorHarmonicBump n).tsupport_eq] at hy
      have hy' : ‖y‖ ≤ 1/2 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hy
      have hx' : ‖x‖ < 1/4 := by simpa only [Metric.mem_ball, dist_zero_right] using hx
      change ‖y+x-0‖ < 1
      rw [sub_zero]
      have hn := norm_add_le y x
      linarith)
  have hN : (2 * (n : ℝ) * fundamentalApproxMass n) ≠ 0 := by
    have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
    exact (mul_pos (mul_pos (by norm_num) hn) (fundamentalApproxMass_pos n)).ne'
  change (2 * (n : ℝ) * fundamentalApproxMass n) * h x = harmonicSmoothing (interiorHarmonicBump n) h x at he
  rw [← he, inv_mul_cancel_left₀ hN]

/-- The cubic quadratic-jet remainder is derived from the explicit smooth
kernel, with a constant depending only on the dimension. -/
theorem exists_harmonic_quadratic_remainder_bound [NeZero n] :
    ∃ K : ℝ, 0 < K ∧ ∀ h : KernelSpace n → ℝ, ContDiff ℝ 2 h → HasCompactSupport h →
      (∀ y ∈ Metric.ball (0 : KernelSpace n) 1, kernelLaplacian h y = 0) →
      ∀ B : ℝ, 0 ≤ B → (∀ y, |h y| ≤ B) → ∀ z ∈ Metric.ball (0 : KernelSpace n) (1/4),
        |h z - h 0 - fderiv ℝ h 0 z - (1/2 : ℝ) * fderiv ℝ (fderiv ℝ h) 0 z z| ≤ K * B * ‖z‖ ^ 3 := by
  let χ := interiorHarmonicBump n
  let G := fun y : KernelSpace n => harmonicSmoothingKernel χ (-y)
  have hG : ContDiff ℝ ∞ G :=
    (contDiff_harmonicSmoothingKernel χ.contDiff (interiorHarmonicBump_eventually_one n)).comp contDiff_id.neg
  have hGc : HasCompactSupport G :=
    (hasCompactSupport_harmonicSmoothingKernel χ.hasCompactSupport (interiorHarmonicBump_eventually_one n)).comp_homeomorph (Homeomorph.neg _)
  obtain ⟨D, hD, hLip⟩ := exists_vectorKernelConvolution_second_lipschitz hG hGc
  let c := (2 * (n : ℝ) * fundamentalApproxMass n)⁻¹
  let L := |c| * D
  have hL : 0 ≤ L := mul_nonneg (abs_nonneg _) hD
  refine ⟨L/2+1, by positivity, ?_⟩
  intro h hh hhc hharm B hB hb z hz
  let s := fun x => c * harmonicSmoothing χ h x
  have hs : ContDiff ℝ ∞ s := contDiff_const.mul
    (contDiff_harmonicSmoothing χ.contDiff χ.hasCompactSupport (interiorHarmonicBump_eventually_one n) hh.continuous.locallyIntegrable)
  have he (x : KernelSpace n) (hx : x ∈ Metric.ball (0 : KernelSpace n) (1/4)) : s x = h x :=
    interior_harmonic_reproducing hh hhc hharm hx
  have he0 : s =ᶠ[𝓝 0] h := eventually_of_mem (Metric.ball_mem_nhds _ (by norm_num : (0 : ℝ) < 1/4)) he
  have hH (x y : KernelSpace n) :
      ‖fderiv ℝ (fderiv ℝ s) x - fderiv ℝ (fderiv ℝ s) y‖ ≤ L*B*‖x-y‖ := by
    have hsc : ContDiff ℝ 2 (harmonicSmoothing χ h) := contDiff_infty.mp
      (contDiff_harmonicSmoothing χ.contDiff χ.hasCompactSupport (interiorHarmonicBump_eventually_one n) hh.continuous.locallyIntegrable) 2
    rw [secondFrechet_const_mul_C2 c hsc, secondFrechet_const_mul_C2 c hsc,
      ← smul_sub, norm_smul, Real.norm_eq_abs,
      harmonicSmoothing_eq_vectorKernelConvolution]
    exact (mul_le_mul_of_nonneg_left (hLip h hh.continuous.locallyIntegrable B hB hb x y) (abs_nonneg _)).trans_eq (by dsimp [L, G]; ring)
  have ht := taylor_second_remainder_holder_bound (contDiff_infty.mp hs 2)
    (C := L*B) (α := 1) (mul_nonneg hL hB) (by norm_num) (0 : KernelSpace n) z (by
      intro t _
      simpa only [zero_add, sub_zero, Real.rpow_one] using hH (t • z) 0)
  simp only [zero_add, Real.rpow_one] at ht
  rw [he z hz, he0.eq_of_nhds, he0.fderiv_eq, he0.fderiv.fderiv_eq] at ht
  apply ht.trans
  nlinarith [norm_nonneg z, mul_nonneg hB (pow_nonneg (norm_nonneg z) 3)]

end GaussianTilt.MomentMapLinearDirichlet
