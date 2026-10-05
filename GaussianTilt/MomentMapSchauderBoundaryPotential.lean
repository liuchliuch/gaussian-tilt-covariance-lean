import GaussianTilt.MomentMapLinearDirichletNewtonianPotentialRegularity

/-! # Quantitative Newtonian Hessian bounds for the boundary reconstruction

The constant survives the actual mollified Hessian limit and is linear in
the data norms. No support-radius-dependent qualitative constant is used.
-/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1600000
open Set MeasureTheory Filter
open scoped ContDiff Topology
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapLinearDirichlet
variable {n : ℕ}

/-- The dimension/exponent-only singular-integral Hölder estimate holds
for the true C² potential of compact Hölder data, not just smooth data. -/
theorem exists_holder_newtonian_hessian_quantitative [NeZero n]
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : KernelSpace n → ℝ, Continuous f → HasCompactSupport f →
      ∀ F H : ℝ, 0 ≤ F → 0 ≤ H → (∀ x, |f x| ≤ F) →
      (∀ x y, |f x-f y| ≤ H*‖x-y‖^α) →
      ∀ x y, ‖x-y‖ ≤ 1 →
        ‖fderiv ℝ (fderiv ℝ (newtonianPotential f)) x-fderiv ℝ (fderiv ℝ (newtonianPotential f)) y‖ ≤
          C*(F+H)*‖x-y‖^α := by
  obtain ⟨C, hC, hbound⟩ := exists_newtonianPotential_secondFrechet_holder (n := n) hα hα1
  refine ⟨C, hC, ?_⟩
  intro f hf hs F H hF hH hfb hfh x y hxy
  let R := ‖x‖+‖y‖+1
  have hR : 0 < R := by dsimp [R]; positivity
  obtain ⟨j, hj, σ, hσ, hlim⟩ := exists_newtonianPotential_holder_jet hf hs hα hα1 hH hR.le hfh
  have hx : x ∈ interior (Metric.closedBall (0 : KernelSpace n) R) := by
    rw [interior_closedBall _ hR.ne', Metric.mem_ball, dist_zero_right]
    dsimp [R]
    linarith [norm_nonneg y]
  have hy : y ∈ interior (Metric.closedBall (0 : KernelSpace n) R) := by
    rw [interior_closedBall _ hR.ne', Metric.mem_ball, dist_zero_right]
    dsimp [R]
    linarith [norm_nonneg x]
  have hxlim : Tendsto (fun k => fderiv ℝ (fderiv ℝ (newtonianPotential (harmonicMollify (σ k) f))) x)
      atTop (𝓝 (fderiv ℝ (fderiv ℝ (newtonianPotential f)) x)) := by
    rw [potential_second_eq_jet hα j hj hx]
    exact hlim ⟨x, interior_subset hx⟩
  have hylim : Tendsto (fun k => fderiv ℝ (fderiv ℝ (newtonianPotential (harmonicMollify (σ k) f))) y)
      atTop (𝓝 (fderiv ℝ (fderiv ℝ (newtonianPotential f)) y)) := by
    rw [potential_second_eq_jet hα j hj hy]
    exact hlim ⟨y, interior_subset hy⟩
  apply le_of_tendsto' ((hxlim.sub hylim).norm)
  intro k
  exact hbound (harmonicMollify (σ k) f) (harmonicMollify_smooth hf.locallyIntegrable _)
    (harmonicMollify_compact hs _) F H hF hH (harmonicMollify_bound hfb _)
    (harmonicMollify_holder hf hfh _) x y hxy

/-- A fixed compact support radius gives a uniform actual Hessian bound
at the origin, linear in the forcing supremum and Hölder constants. -/
theorem exists_holder_newtonian_hessian_origin_bound [NeZero n]
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : KernelSpace n → ℝ, Continuous f → HasCompactSupport f →
      Function.support f ⊆ Metric.closedBall 0 A →
      ∀ F H : ℝ, 0 ≤ F → 0 ≤ H → (∀ x, |f x| ≤ F) →
      (∀ x y, |f x-f y| ≤ H*‖x-y‖^α) →
      ‖fderiv ℝ (fderiv ℝ (newtonianPotential f)) 0‖ ≤ C*(F+H) := by
  obtain ⟨Ch, hCh, hholder⟩ := exists_holder_newtonian_hessian_quantitative (n := n) hα hα1
  let Z := newtonianLocalMass n (1+A)
  have hZ : 0 ≤ Z := newtonianLocalMass_nonneg _ _
  refine ⟨16*Z+2*Ch+1, by positivity, ?_⟩
  intro f hf hs hfs F H hF hH hfb hfh
  have hp := newtonianPotential_contDiff_two hf hs hα hα1 hH hfh
  have hPb : ∀ y ∈ Metric.closedBall (0 : KernelSpace n) (1/2), |newtonianPotential f y| ≤ F*Z := by
    intro y hy
    exact newtonianPotential_local_bound (R := 1) hF hfb hfs
      ((show ‖y‖ ≤ 1/2 by simpa only [Metric.mem_closedBall, dist_zero_right] using hy).trans (by norm_num))
  have hPH : ∀ y ∈ Metric.closedBall (0 : KernelSpace n) (1/2), ∀ z ∈ Metric.closedBall (0 : KernelSpace n) (1/2),
      ‖fderiv ℝ (fderiv ℝ (newtonianPotential f)) y-fderiv ℝ (fderiv ℝ (newtonianPotential f)) z‖ ≤
        (Ch*(F+H))*‖y-z‖^α := by
    intro y hy z hz
    apply hholder f hf hs F H hF hH hfb hfh y z
    have hy' : ‖y‖ ≤ 1/2 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hy
    have hz' : ‖z‖ ≤ 1/2 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    exact (norm_sub_le _ _).trans (by linarith)
  have hh := hessian_interpolation_on_closedBall hp (by norm_num : (0 : ℝ) < 1/2)
    (mul_nonneg hF hZ) (mul_nonneg hCh.le (add_nonneg hF hH)) hα.le hPb hPH
  have hhalf : (1/2 : ℝ)^α ≤ 1 := Real.rpow_le_one (by norm_num) (by norm_num) hα.le
  norm_num only [one_div, inv_pow, one_pow, inv_inv] at hh
  have hterm := mul_le_mul_of_nonneg_left hhalf (show 0 ≤ 2*(Ch*(F+H)) by positivity)
  have hF' : F ≤ F+H := by linarith
  have hfirst := mul_le_mul_of_nonneg_left hF' (show 0 ≤ 16*Z by positivity)
  nlinarith

/-- A fixed compact support radius gives a uniform actual gradient bound
at the origin, linear in the forcing supremum and Hölder constants. -/
theorem exists_holder_newtonian_gradient_origin_bound [NeZero n]
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : KernelSpace n → ℝ, Continuous f → HasCompactSupport f →
      Function.support f ⊆ Metric.closedBall 0 A →
      ∀ F H : ℝ, 0 ≤ F → 0 ≤ H → (∀ x, |f x| ≤ F) →
      (∀ x y, |f x-f y| ≤ H*‖x-y‖^α) →
      ‖fderiv ℝ (newtonianPotential f) 0‖ ≤ C*(F+H) := by
  obtain ⟨Ch, hCh, hholder⟩ := exists_holder_newtonian_hessian_quantitative (n := n) hα hα1
  let Z := newtonianLocalMass n (1+A)
  have hZ : 0 ≤ Z := newtonianLocalMass_nonneg _ _
  refine ⟨16*Z+2*Ch+1, by positivity, ?_⟩
  intro f hf hs hfs F H hF hH hfb hfh
  have hp := newtonianPotential_contDiff_two hf hs hα hα1 hH hfh
  have hPb : ∀ y ∈ Metric.closedBall (0 : KernelSpace n) (1/2), |newtonianPotential f y| ≤ F*Z := by
    intro y hy
    exact newtonianPotential_local_bound (R := 1) hF hfb hfs
      ((show ‖y‖ ≤ 1/2 by simpa only [Metric.mem_closedBall, dist_zero_right] using hy).trans (by norm_num))
  have hPH : ∀ y ∈ Metric.closedBall (0 : KernelSpace n) (1/2), ∀ z ∈ Metric.closedBall (0 : KernelSpace n) (1/2),
      ‖fderiv ℝ (fderiv ℝ (newtonianPotential f)) y-fderiv ℝ (fderiv ℝ (newtonianPotential f)) z‖ ≤
        (Ch*(F+H))*‖y-z‖^α := by
    intro y hy z hz
    apply hholder f hf hs F H hF hH hfb hfh y z
    have hy' : ‖y‖ ≤ 1/2 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hy
    have hz' : ‖z‖ ≤ 1/2 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    exact (norm_sub_le _ _).trans (by linarith)
  have hh := gradient_interpolation_on_closedBall hp (by norm_num : (0 : ℝ) < 1/2)
    (mul_nonneg hF hZ) (mul_nonneg hCh.le (add_nonneg hF hH)) hα.le hPb hPH
  have hhalf : (1/2 : ℝ)^α ≤ 1 := Real.rpow_le_one (by norm_num) (by norm_num) hα.le
  norm_num only [one_div, inv_pow, one_pow, inv_inv] at hh
  have hterm := mul_le_mul_of_nonneg_left hhalf (show 0 ≤ 2*(Ch*(F+H)) by positivity)
  have hF' : F ≤ F+H := by linarith
  have hfirst := mul_le_mul_of_nonneg_left hF' (show 0 ≤ 16*Z by positivity)
  nlinarith

end GaussianTilt.MomentMapSchauder
