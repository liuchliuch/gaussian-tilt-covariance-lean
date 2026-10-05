import GaussianTilt.MomentMapLinearDirichletSmoothingL2Bounds
import GaussianTilt.MomentMapLinearDirichletHarmonicTaylor

/-! # Genuine harmonic oscillation controlled by local L² excess

The estimate permits subtraction of every constant. This is the excess
estimate, rather than only an energy bound, needed by Campanato iteration.
-/
noncomputable section
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 1000
open MeasureTheory Set Filter
open scoped Topology ContDiff BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic
variable {n : ℕ}

theorem exists_local_harmonic_L2_oscillation_bound [NeZero n] :
    ∃ K : ℝ, 0 < K ∧ ∀ h : KernelSpace n → ℝ,
      (∀ x ∈ Metric.ball (0:KernelSpace n) 2, ContDiffAt ℝ ∞ h x) →
      (∀ x ∈ Metric.ball (0:KernelSpace n) 2, kernelLaplacian h x=0) →
      ∀ q : ℝ, IntegrableOn (fun x => (h x-q)^2) (Metric.ball (0:KernelSpace n) 2) volume →
      ∀ x ∈ Metric.ball (0:KernelSpace n) 1, ∀ y ∈ Metric.ball (0:KernelSpace n) 1,
        (h x-h y)^2 ≤ K*(∫ z in Metric.ball (0:KernelSpace n) 2, (h z-q)^2)*‖x-y‖^2 := by
  let χ := interiorHarmonicBump n
  let J := fun y : KernelSpace n => harmonicSmoothingKernel χ (-y)
  have hJ : ContDiff ℝ ∞ J :=
    (contDiff_harmonicSmoothingKernel χ.contDiff (interiorHarmonicBump_eventually_one n)).comp contDiff_id.neg
  have hJc : HasCompactSupport J :=
    (hasCompactSupport_harmonicSmoothingKernel χ.hasCompactSupport (interiorHarmonicBump_eventually_one n)).comp_homeomorph (Homeomorph.neg _)
  obtain ⟨D,hD,hLip⟩ := exists_vectorKernelConvolution_L2_lipschitz hJ hJc
  let c := (2*(n:ℝ)*fundamentalApproxMass n)⁻¹
  let K := (|c| *D)^2+1
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K,hK,?_⟩
  intro h hh hhar q hEx x hx y hy
  let η : ContDiffBump (0:KernelSpace n) := ⟨3/2,7/4,by norm_num,by norm_num⟩
  let g := fun z => η z*(h z-q)
  have hηB {z : KernelSpace n} (hz : z ∈ tsupport (η:KernelSpace n → ℝ)) : z ∈ Metric.ball (0:KernelSpace n) 2 := by
    rw [η.tsupport_eq] at hz
    exact Metric.closedBall_subset_ball (by norm_num : (7/4:ℝ)<2) hz
  have hg : ContDiff ℝ ∞ g := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    by_cases hz : z ∈ tsupport (η:KernelSpace n → ℝ)
    · exact η.contDiff.contDiffAt.mul ((hh z (hηB hz)).sub contDiffAt_const)
    · apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hz] with t ht
      change η t*(h t-q)=0
      simp only [ht,Pi.zero_apply,zero_mul]
  have hgc : HasCompactSupport g := η.hasCompactSupport.mul_right
  have hgLp : MemLp g 2 volume := hg.continuous.memLp_of_hasCompactSupport hgc
  have hgsq : ‖hgLp.toLp g‖^2 ≤ ∫ z in Metric.ball (0:KernelSpace n) 2, (h z-q)^2 := by
    rw [norm_toLp_sq_eq_integral hgLp,← integral_indicator Metric.isOpen_ball.measurableSet]
    apply integral_mono hgLp.integrable_sq (hEx.integrable_indicator Metric.isOpen_ball.measurableSet)
    intro z
    by_cases hz : z ∈ Metric.ball (0:KernelSpace n) 2
    · rw [indicator_of_mem hz]
      change (η z*(h z-q))^2 ≤ (h z-q)^2
      have hη0 := η.nonneg (x := z)
      have hη1 := η.le_one (x := z)
      have hs : (η z)^2 ≤ 1 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hs (sq_nonneg (h z-q))]
    · have hη0 : η z=0 := image_eq_zero_of_notMem_tsupport (fun hh => hz (hηB hh))
      rw [indicator_of_notMem hz]
      simp only [g,hη0,zero_mul,zero_pow (by decide : (2:ℕ)≠0),le_refl]
  have he (z : KernelSpace n) (hz : z ∈ Metric.ball (0:KernelSpace n) (3/2)) : g z=h z-q := by
    change η z*(h z-q)=h z-q
    rw [η.one_of_mem_closedBall (Metric.ball_subset_closedBall hz),one_mul]
  have hge (z : KernelSpace n) (hz : z ∈ Metric.ball (0:KernelSpace n) (3/2)) : g =ᶠ[𝓝 z] (fun t => h t-q) :=
    eventually_of_mem (Metric.isOpen_ball.mem_nhds hz) he
  have hghar (z : KernelSpace n) (hz : z ∈ Metric.ball (0:KernelSpace n) (3/2)) : kernelLaplacian g z=0 := by
    rw [kernelLaplacian_congr_nhds (hge z hz)]
    have hz2 := Metric.ball_subset_ball (by norm_num : (3/2:ℝ)≤2) hz
    have hconst : kernelLaplacian (fun t => h t-q) z=kernelLaplacian h z := by
      simp only [kernelLaplacian,directionalHessian]
      have hd : fderiv ℝ (fun t => h t-q) = fderiv ℝ h := by
        funext t
        exact fderiv_sub_const _
      simp only [hd]
    rw [hconst,hhar z hz2]
  have hN : 2*(n:ℝ)*fundamentalApproxMass n ≠ 0 := by
    have hn : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
    exact (mul_pos (mul_pos (by norm_num) hn) (fundamentalApproxMass_pos n)).ne'
  have hrep (z : KernelSpace n) (hz : z ∈ Metric.ball (0:KernelSpace n) 1) :
      c*vectorKernelConvolution J g z=h z-q := by
    have hr := harmonicSmoothingKernel_reproduces_at χ.contDiff (interiorHarmonicBump_eventually_one n)
      (contDiff_infty.mp hg 2) hgc z (by
        intro t ht
        apply hghar
        rw [χ.tsupport_eq] at ht
        have htn : ‖t‖ ≤ 1/2 := by simpa only [Metric.mem_closedBall,dist_zero_right] using ht
        have hzn : ‖z‖ < 1 := by simpa only [Metric.mem_ball,dist_zero_right] using hz
        change ‖t+z-0‖ < 3/2
        rw [sub_zero]
        linarith [norm_add_le t z])
    change (2*(n:ℝ)*fundamentalApproxMass n)*g z=harmonicSmoothing χ g z at hr
    rw [harmonicSmoothing_eq_vectorKernelConvolution] at hr
    rw [← hr]
    change (2*(n:ℝ)*fundamentalApproxMass n)⁻¹*((2*(n:ℝ)*fundamentalApproxMass n)*g z)=h z-q
    rw [inv_mul_cancel_left₀ hN,he z (Metric.ball_subset_ball (by norm_num : (1:ℝ)≤3/2) hz)]
  have hp := hLip g hgLp x y
  have hdiff : |h x-h y| ≤ (|c| *D)*‖hgLp.toLp g‖*‖x-y‖ := by
    have hid : h x-h y=c*(vectorKernelConvolution J g x-vectorKernelConvolution J g y) := by
      rw [mul_sub,hrep x hx,hrep y hy]
      ring
    rw [hid,abs_mul]
    exact (mul_le_mul_of_nonneg_left hp (abs_nonneg c)).trans_eq (by ring)
  have hs := pow_le_pow_left₀ (abs_nonneg _) hdiff 2
  rw [sq_abs] at hs
  have hE := integral_nonneg (μ := volume.restrict (Metric.ball (0:KernelSpace n) 2)) (fun z => sq_nonneg (h z-q))
  have ht := mul_le_mul_of_nonneg_left hgsq (mul_nonneg (sq_nonneg (|c| *D)) (sq_nonneg ‖x-y‖))
  dsimp only [K]
  nlinarith [mul_nonneg hE (sq_nonneg ‖x-y‖)]

end GaussianTilt.MomentMapLinearDirichlet
