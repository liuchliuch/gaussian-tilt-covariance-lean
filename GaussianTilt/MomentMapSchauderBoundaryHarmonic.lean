import GaussianTilt.MomentMapLinearDirichletHarmonicTaylorLocal
import GaussianTilt.MomentMapSchauderLocalization
import GaussianTilt.MomentMapSchauderBoundaryPotential

/-! # Quantitative interior harmonic jet bounds for boundary reconstruction -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1800000
open Set MeasureTheory Filter
open scoped ContDiff Topology
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapLinearDirichlet
variable {n : ℕ}

/-- The actual compact harmonic smoothing identity gives derivative
bounds and a Hessian Lipschitz estimate proportional to the function size. -/
theorem exists_compact_harmonic_interior_jet_bounds [NeZero n] :
    ∃ C : ℝ, 0 < C ∧ ∀ h : KernelSpace n → ℝ, ContDiff ℝ 2 h → HasCompactSupport h →
      (∀ y ∈ Metric.ball (0 : KernelSpace n) 1, kernelLaplacian h y=0) →
      ∀ B : ℝ, 0 ≤ B → (∀ y, |h y| ≤ B) →
      ‖fderiv ℝ h 0‖ ≤ C*B ∧ ‖fderiv ℝ (fderiv ℝ h) 0‖ ≤ C*B ∧
      (∀ x ∈ Metric.ball (0 : KernelSpace n) (1/8), ∀ y ∈ Metric.ball (0 : KernelSpace n) (1/8),
        ‖fderiv ℝ (fderiv ℝ h) x-fderiv ℝ (fderiv ℝ h) y‖ ≤ C*B*‖x-y‖) := by
  let χ := interiorHarmonicBump n
  let G := fun y : KernelSpace n => harmonicSmoothingKernel χ (-y)
  have hG : ContDiff ℝ ∞ G :=
    (contDiff_harmonicSmoothingKernel χ.contDiff (interiorHarmonicBump_eventually_one n)).comp contDiff_id.neg
  have hGc : HasCompactSupport G :=
    (hasCompactSupport_harmonicSmoothingKernel χ.hasCompactSupport (interiorHarmonicBump_eventually_one n)).comp_homeomorph (Homeomorph.neg _)
  obtain ⟨D, hD, hLip⟩ := exists_vectorKernelConvolution_second_lipschitz hG hGc
  let c := (2*(n : ℝ)*fundamentalApproxMass n)⁻¹
  let L := |c| * D
  have hL : 0 ≤ L := mul_nonneg (abs_nonneg _) hD
  let C := 257+L
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro h hh hhc hhar B hB hb
  let s := fun x => c*harmonicSmoothing χ h x
  have hs : ContDiff ℝ ∞ s := contDiff_const.mul
    (contDiff_harmonicSmoothing χ.contDiff χ.hasCompactSupport (interiorHarmonicBump_eventually_one n) hh.continuous.locallyIntegrable)
  have he : ∀ x ∈ Metric.ball (0 : KernelSpace n) (1/4), s x=h x :=
    fun x hx => interior_harmonic_reproducing hh hhc hhar hx
  have heN : ∀ x ∈ Metric.ball (0 : KernelSpace n) (1/4), s =ᶠ[𝓝 x] h :=
    fun x hx => eventually_of_mem (Metric.isOpen_ball.mem_nhds hx) he
  have hH : ∀ x y : KernelSpace n,
      ‖fderiv ℝ (fderiv ℝ s) x-fderiv ℝ (fderiv ℝ s) y‖ ≤ (L*B)*‖x-y‖ := by
    intro x y
    have hsc : ContDiff ℝ 2 (harmonicSmoothing χ h) := contDiff_infty.mp
      (contDiff_harmonicSmoothing χ.contDiff χ.hasCompactSupport (interiorHarmonicBump_eventually_one n) hh.continuous.locallyIntegrable) 2
    rw [secondFrechet_const_mul_C2 c hsc, secondFrechet_const_mul_C2 c hsc,
      ← smul_sub, norm_smul, Real.norm_eq_abs, harmonicSmoothing_eq_vectorKernelConvolution]
    exact (mul_le_mul_of_nonneg_left (hLip h hh.continuous.locallyIntegrable B hB hb x y) (abs_nonneg c)).trans_eq
      (by dsimp [L, G]; ring)
  have hsb : ∀ x ∈ Metric.closedBall (0 : KernelSpace n) (1/8), |s x| ≤ B := by
    intro x hx
    rw [he x (Metric.closedBall_subset_ball (by norm_num : (1/8 : ℝ) < 1/4) hx)]
    exact hb x
  have hsh : ∀ x ∈ Metric.closedBall (0 : KernelSpace n) (1/8), ∀ y ∈ Metric.closedBall (0 : KernelSpace n) (1/8),
      ‖fderiv ℝ (fderiv ℝ s) x-fderiv ℝ (fderiv ℝ s) y‖ ≤ (L*B)*‖x-y‖^(1 : ℝ) := by
    intro x hx y hy
    simpa only [Real.rpow_one] using hH x y
  have hg := gradient_interpolation_on_closedBall (contDiff_infty.mp hs 2)
    (by norm_num : (0 : ℝ)<1/8) hB (mul_nonneg hL hB) (by norm_num : (0 : ℝ)≤1) hsb hsh
  have hq := hessian_interpolation_on_closedBall (contDiff_infty.mp hs 2)
    (by norm_num : (0 : ℝ)<1/8) hB (mul_nonneg hL hB) (by norm_num : (0 : ℝ)≤1) hsb hsh
  have h0 := heN 0 (Metric.mem_ball_self (by norm_num : (0 : ℝ)<1/4))
  rw [h0.fderiv_eq] at hg
  rw [h0.fderiv.fderiv_eq] at hq
  norm_num only [Real.rpow_one] at hg hq
  refine ⟨?_, ?_, ?_⟩
  · dsimp [C]
    nlinarith [mul_nonneg hL hB]
  · dsimp [C]
    nlinarith [mul_nonneg hL hB]
  · intro x hx y hy
    have hx' := Metric.ball_subset_ball (by norm_num : (1/8 : ℝ)≤1/4) hx
    have hy' := Metric.ball_subset_ball (by norm_num : (1/8 : ℝ)≤1/4) hy
    rw [← (heN x hx').fderiv.fderiv_eq, ← (heN y hy').fderiv.fderiv_eq]
    exact (hH x y).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (show L ≤ C by dsimp [C]; linarith) hB) (norm_nonneg _))

/-- The quantitative estimate uses only local classical harmonicity on
B₂ and a local value bound; no global smoothness or support is assumed. -/
theorem exists_local_harmonic_interior_jet_bounds [NeZero n] :
    ∃ C : ℝ, 0 < C ∧ ∀ h : KernelSpace n → ℝ,
      ContDiffOn ℝ 2 h (Metric.ball (0 : KernelSpace n) 2) →
      (∀ y ∈ Metric.ball (0 : KernelSpace n) 2, kernelLaplacian h y=0) →
      ∀ B : ℝ, 0 ≤ B → (∀ y ∈ Metric.ball (0 : KernelSpace n) 2, |h y| ≤ B) →
      ‖fderiv ℝ h 0‖ ≤ C*B ∧ ‖fderiv ℝ (fderiv ℝ h) 0‖ ≤ C*B ∧
      (∀ x ∈ Metric.ball (0 : KernelSpace n) (1/8), ∀ y ∈ Metric.ball (0 : KernelSpace n) (1/8),
        ‖fderiv ℝ (fderiv ℝ h) x-fderiv ℝ (fderiv ℝ h) y‖ ≤ C*B*‖x-y‖) := by
  obtain ⟨C, hC, hbound⟩ := exists_compact_harmonic_interior_jet_bounds (n := n)
  refine ⟨C, hC, ?_⟩
  intro h hh hhar B hB hb
  let η : ContDiffBump (0 : KernelSpace n) := ⟨1, 3/2, by norm_num, by norm_num⟩
  let g := fun x => η x*h x
  have hs : tsupport (η : KernelSpace n → ℝ) ⊆ Metric.ball 0 2 := by
    rw [η.tsupport_eq]
    exact Metric.closedBall_subset_ball (by norm_num)
  have hg : ContDiff ℝ 2 g := contDiff_cutoff_mul_of_contDiffOn Metric.isOpen_ball hh
    (contDiff_infty.mp η.contDiff 2) hs
  have hgc : HasCompactSupport g := η.hasCompactSupport.mul_right
  have hgb : ∀ x, |g x| ≤ B := by
    intro x
    by_cases hx : x ∈ tsupport (η : KernelSpace n → ℝ)
    · change |η x*h x| ≤ B
      rw [abs_mul, abs_of_nonneg η.nonneg]
      exact (mul_le_mul η.le_one (hb x (hs hx)) (abs_nonneg _) zero_le_one).trans_eq (one_mul B)
    · change |η x*h x| ≤ B
      rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, abs_zero]
      exact hB
  have he : ∀ x ∈ Metric.ball (0 : KernelSpace n) 1, g x=h x := by
    intro x hx
    change η x*h x=h x
    rw [η.one_of_mem_closedBall (Metric.ball_subset_closedBall hx), one_mul]
  have heN : ∀ x ∈ Metric.ball (0 : KernelSpace n) 1, g =ᶠ[𝓝 x] h :=
    fun x hx => eventually_of_mem (Metric.isOpen_ball.mem_nhds hx) he
  have hghar : ∀ x ∈ Metric.ball (0 : KernelSpace n) 1, kernelLaplacian g x=0 := by
    intro x hx
    rw [kernelLaplacian_congr_nhds (heN x hx)]
    exact hhar x (Metric.ball_subset_ball (by norm_num : (1 : ℝ)≤2) hx)
  have hq := hbound g hg hgc hghar B hB hgb
  have h0 := heN 0 (Metric.mem_ball_self zero_lt_one)
  refine ⟨by simpa only [h0.fderiv_eq] using hq.1,
    by simpa only [h0.fderiv.fderiv_eq] using hq.2.1, ?_⟩
  intro x hx y hy
  have hx' := Metric.ball_subset_ball (by norm_num : (1/8 : ℝ)≤1) hx
  have hy' := Metric.ball_subset_ball (by norm_num : (1/8 : ℝ)≤1) hy
  simpa only [(heN x hx').fderiv.fderiv_eq, (heN y hy').fderiv.fderiv_eq] using hq.2.2 x hx y hy

end GaussianTilt.MomentMapSchauder
