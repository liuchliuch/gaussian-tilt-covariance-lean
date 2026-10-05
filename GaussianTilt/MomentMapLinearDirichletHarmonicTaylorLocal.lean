import GaussianTilt.MomentMapLinearDirichletFlatClassicalReflection

/-!
# Local harmonic quadratic approximation without a global regularity premise

A constructed compact cutoff agrees with the original function near the
unit ball. Pointwise local C² regularity proves that its product is globally
C², so the actual harmonic Taylor estimate applies using only local data.
-/
noncomputable section
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 1000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

/-- A dimension-only cubic Taylor bound from solely local C² harmonicity
and a local supremum bound on the ball of radius two. -/
theorem exists_local_harmonic_quadratic_remainder_bound [NeZero n] :
    ∃ K : ℝ, 0 < K ∧ ∀ h : KernelSpace n → ℝ,
      (∀ x ∈ Metric.ball (0 : KernelSpace n) 2, ContDiffAt ℝ 2 h x) →
      (∀ x ∈ Metric.ball (0 : KernelSpace n) 2, kernelLaplacian h x = 0) →
      ∀ B : ℝ, 0 ≤ B → (∀ x ∈ Metric.ball (0 : KernelSpace n) 2, |h x| ≤ B) →
      ∀ z ∈ Metric.ball (0 : KernelSpace n) (1/4),
        |h z - h 0 - fderiv ℝ h 0 z - (1/2 : ℝ) * fderiv ℝ (fderiv ℝ h) 0 z z| ≤ K * B * ‖z‖ ^ 3 := by
  obtain ⟨K, hK, hTaylor⟩ := exists_harmonic_quadratic_remainder_bound (n := n)
  refine ⟨K, hK, ?_⟩
  intro h hh hhar B hB hb z hz
  let η : ContDiffBump (0 : KernelSpace n) := ⟨1, 3/2, by norm_num, by norm_num⟩
  let g := fun x => η x * h x
  have hηB {x : KernelSpace n} (hx : x ∈ tsupport (η : KernelSpace n → ℝ)) :
      x ∈ Metric.ball (0 : KernelSpace n) 2 := by
    rw [η.tsupport_eq] at hx
    exact Metric.closedBall_subset_ball (by norm_num : (3/2 : ℝ) < 2) hx
  have hg : ContDiff ℝ 2 g := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ tsupport (η : KernelSpace n → ℝ)
    · exact (contDiff_infty.mp η.contDiff 2).contDiffAt.mul (hh x (hηB hx))
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      change η y * h y = 0
      simp only [hy, Pi.zero_apply, zero_mul]
  have hgc : HasCompactSupport g := η.hasCompactSupport.mul_right
  have hgb (x : KernelSpace n) : |g x| ≤ B := by
    by_cases hx : x ∈ tsupport (η : KernelSpace n → ℝ)
    · change |η x * h x| ≤ B
      rw [abs_mul, abs_of_nonneg η.nonneg]
      exact (mul_le_mul η.le_one (hb x (hηB hx)) (abs_nonneg _) (by norm_num)).trans_eq (one_mul B)
    · change |η x * h x| ≤ B
      rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, abs_zero]
      exact hB
  have he (x : KernelSpace n) (hx : x ∈ Metric.ball (0 : KernelSpace n) 1) : g x = h x := by
    change η x * h x = h x
    rw [η.one_of_mem_closedBall (Metric.ball_subset_closedBall hx), one_mul]
  have heN {x : KernelSpace n} (hx : x ∈ Metric.ball (0 : KernelSpace n) 1) : g =ᶠ[𝓝 x] h :=
    eventually_of_mem (Metric.isOpen_ball.mem_nhds hx) he
  have hghar (x : KernelSpace n) (hx : x ∈ Metric.ball (0 : KernelSpace n) 1) : kernelLaplacian g x = 0 := by
    rw [kernelLaplacian_congr_nhds (heN hx)]
    exact hhar x (Metric.ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2) hx)
  have ht := hTaylor g hg hgc hghar B hB hgb z hz
  have hz1 := Metric.ball_subset_ball (by norm_num : (1/4 : ℝ) ≤ 1) hz
  have h01 : (0 : KernelSpace n) ∈ Metric.ball 0 1 := Metric.mem_ball_self (by norm_num)
  rw [he z hz1, he 0 h01, (heN h01).fderiv_eq, (heN h01).fderiv.fderiv_eq] at ht
  exact ht

end GaussianTilt.MomentMapLinearDirichlet
