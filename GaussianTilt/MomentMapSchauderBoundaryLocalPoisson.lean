import GaussianTilt.MomentMapSchauderBoundaryPoisson
import GaussianTilt.MomentMapSchauderCutoffHolder

/-! # Local-data quantitative Poisson estimate -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 2000000
open Set
open scoped ContDiff
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapLinearDirichlet
variable {n : ℕ}

/-- The fixed cutoff extends only the forcing. Thus its compactness is
constructed, while the equation and the solution remain genuinely local. -/
theorem exists_local_unit_poisson_jet_bound [NeZero n]
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ u f : KernelSpace n → ℝ,
      ContDiffOn ℝ 2 u (Metric.ball 0 2) → Continuous f →
      (∀ x ∈ Metric.ball (0 : KernelSpace n) 2, kernelLaplacian u x=f x) →
      ∀ U F H : ℝ, 0 ≤ U → 0 ≤ F → 0 ≤ H →
      (∀ x ∈ Metric.ball (0 : KernelSpace n) 2, |u x| ≤ U) →
      (∀ x ∈ Metric.ball (0 : KernelSpace n) 4, |f x| ≤ F) →
      (∀ x ∈ Metric.ball (0 : KernelSpace n) 4, ∀ y ∈ Metric.ball (0 : KernelSpace n) 4,
        |f x-f y| ≤ H*‖x-y‖^α) →
      ‖fderiv ℝ u 0‖ ≤ C*(U+F+H) ∧ ‖fderiv ℝ (fderiv ℝ u) 0‖ ≤ C*(U+F+H) ∧
      (∀ x ∈ Metric.ball (0 : KernelSpace n) (1/8), ∀ y ∈ Metric.ball (0 : KernelSpace n) (1/8),
        ‖fderiv ℝ (fderiv ℝ u) x-fderiv ℝ (fderiv ℝ u) y‖ ≤ C*(U+F+H)*‖x-y‖^α) := by
  obtain ⟨C,hC,hbound⟩ := exists_unit_poisson_interior_jet_bound (n := n) hα hα1
  obtain ⟨B₁,B₂,B₃,hB₁,hB₂,hB₃,hcut⟩ :=
    exists_scaled_cutoff_jet_holder_bounds (E := KernelSpace n) hα.le hα1.le
  let χ := scaledInteriorCutoff (0 : KernelSpace n) 2
  let L := (B₁+2)*(2:ℝ)^(-α)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hχH : ∀ x y, |χ x-χ y| ≤ L*‖x-y‖^α :=
    (hcut 0 2 (by norm_num)).2.2.1
  have hχB : ∀ x, |χ x| ≤ 1 := by
    intro x
    rw [abs_of_nonneg (scaledInteriorCutoff_nonneg 0 x 2)]
    exact scaledInteriorCutoff_le_one 0 x 2
  have hχ0 : ∀ x ∉ Metric.ball (0 : KernelSpace n) 4, χ x=0 := by
    intro x hx
    apply scaledInteriorCutoff_zero (by norm_num : (0:ℝ)<2)
    simpa only [Metric.mem_ball, dist_zero_right, not_lt,sub_zero,show (2:ℝ)*2=4 by norm_num] using hx
  refine ⟨C*(1+L),by positivity,?_⟩
  intro u f hu hf heq U F H hU hF hH huB hfB hfH
  let g := fun x => χ x*f x
  have hg : Continuous g := (scaledInteriorCutoff_contDiff 0 2).continuous.mul hf
  have hgc : HasCompactSupport g := (scaledInteriorCutoff_compact 0 (by norm_num : (0:ℝ)<2)).mul_right
  have hgs : Function.support g ⊆ Metric.closedBall 0 4 := by
    intro x hx
    by_contra hx'
    have hn : x ∉ Metric.ball (0 : KernelSpace n) 4 := fun h => hx' (Metric.ball_subset_closedBall h)
    exact hx (by simp only [g,hχ0 x hn,zero_mul])
  have hgB : ∀ x, |g x| ≤ F := by
    intro x
    by_cases hx : x ∈ Metric.ball (0 : KernelSpace n) 4
    · exact (abs_mul _ _).le.trans ((mul_le_mul (hχB x) (hfB x hx) (abs_nonneg _) zero_le_one).trans_eq (one_mul F))
    · simpa only [g,hχ0 x hx,zero_mul,abs_zero] using hF
  have hgH : ∀ x y, |g x-g y| ≤ (H+F*L)*‖x-y‖^α := by
    simpa only [one_mul] using global_holder_cutoff_product zero_le_one hF hL hH hχB hfB hχH hfH hχ0
  have hge : ∀ x ∈ Metric.ball (0 : KernelSpace n) 2, g x=f x := by
    intro x hx
    change χ x*f x=f x
    rw [show χ x=1 from scaledInteriorCutoff_one (by norm_num) (by
      simpa only [sub_zero] using (show ‖x‖ < 2 by simpa only [Metric.mem_ball,dist_zero_right] using hx).le),one_mul]
  have hh := hbound u g hu hg hgc hgs (fun x hx => (heq x hx).trans (hge x hx).symm)
    U F (H+F*L) hU hF (by positivity) huB hgB hgH
  have htotal : C*(U+F+(H+F*L)) ≤ C*(1+L)*(U+F+H) := by
    have h := mul_le_mul_of_nonneg_left
      (show U+F+(H+F*L) ≤ (1+L)*(U+F+H) by nlinarith [mul_nonneg hL hU,mul_nonneg hL hH]) hC.le
    nlinarith
  exact ⟨hh.1.trans htotal,hh.2.1.trans htotal,fun x hx y hy =>
    (hh.2.2 x hx y hy).trans (mul_le_mul_of_nonneg_right htotal (Real.rpow_nonneg (norm_nonneg _) α))⟩

end GaussianTilt.MomentMapSchauder
