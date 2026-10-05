import GaussianTilt.MomentMapLinearDirichletFlatNormalization

/-!
# Genuine normalized flat quadratic improvement

The actual Poisson correction, odd harmonic Taylor estimate, numerical
scale choice, and concrete residual construction are combined. The output
is an admissible rescaled weak solution with supremum at most one, rather
than an assumed improvement-of-flatness premise.
-/
noncomputable section
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 1000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

/-- An actual scale and threshold make the constructed normalized
polynomial residual no larger than one. Hölder forcing is centered at zero;
the separate constant-forcing quadratic must be subtracted before use. -/
theorem exists_flat_normalized_improvement [NeZero n] {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ θ ε : ℝ, 0 < θ ∧ θ ≤ 1/8 ∧ 0 < ε ∧ ε ≤ 1/4 ∧
      ∀ (j : Fin n) (u f : KernelSpace n → ℝ), FlatWeakPoisson j u f →
      Continuous f → HasCompactSupport f →
      ∀ H : ℝ, 0 ≤ H → (∀ x y, |f x-f y| ≤ H*‖x-y‖^α) → f 0 = 0 → H*2^α ≤ ε →
      (∀ x ∈ Metric.ball (0 : KernelSpace n) 2, |u x| ≤ 1) →
      ∃ A : KernelSpace n →L[ℝ] ℝ, ∃ Q : KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ,
        (∀ x, x j = 0 → flatTaylorPolynomial A Q x = 0) ∧
        (∀ x, kernelLaplacian (flatTaylorPolynomial A Q) x = 0) ∧
        FlatWeakPoisson j (normalizedFlatResidual j θ α u (flatTaylorPolynomial A Q))
          (normalizedFlatSource θ α f) ∧
        (∀ x ∈ Metric.ball (0 : KernelSpace n) 2,
          |normalizedFlatResidual j θ α u (flatTaylorPolynomial A Q) x| ≤ 1) := by
  obtain ⟨K,hK,hstep⟩ := exists_flat_poisson_quadratic_step (n := n)
  obtain ⟨θ,ε,hθ,hθ8,hε,hε4,hnum⟩ := exists_flat_quadratic_improvement_constants hK hα hα1
  refine ⟨θ,ε,hθ,hθ8,hε,hε4,?_⟩
  intro j u f hu hfc hfs H hH hholder hf0 hsmall hub
  obtain ⟨C,hC,hgrowth⟩ := hu.growth
  let F := H*2^α
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hfb : ∀ x ∈ flatUpperBall j 2, |f x| ≤ F :=
    fun x hx => holder_force_bound_of_zero hα.le hH hf0 hholder x hx.1
  obtain ⟨A,Q,hPlane,hHarm,hError⟩ := hstep j u hu.memLp C 1 hC (by norm_num)
    hu.zero_lower hgrowth hub hu.continuous f hfc hfs α H F hα hα1 hH hF hholder hfb hu.equation
  have hθ1 : θ ≤ 1 := hθ8.trans (by norm_num)
  have hres := hu.normalizedResidual hθ hθ1 α (contDiff_flatTaylorPolynomial A Q) hPlane hHarm
  refine ⟨A,Q,hPlane,hHarm,hres,?_⟩
  intro x hx
  by_cases hxj : 0 < x j
  · have hxn : ‖x‖ < 2 := by simpa only [Metric.mem_ball, dist_zero_right] using hx
    have hnorm : ‖θ • x‖ = θ*‖x‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hθ]
    have hθx : θ • x ∈ Metric.ball (0 : KernelSpace n) (1/4) := by
      rw [Metric.mem_ball, dist_zero_right, hnorm]
      nlinarith
    have ht : ‖θ • x‖ ≤ 2*θ := by rw [hnorm]; nlinarith
    have hθxj : 0 ≤ (θ • x) j := by change 0 ≤ θ*x j; positivity
    have herr := (hError (θ • x) hθx hθxj).trans
      (hnum 1 F ‖θ • x‖ (by norm_num) le_rfl hF hsmall (norm_nonneg _) ht)
    rw [normalizedFlatResidual_eq (show x ∈ flatUpperBall j 2 from ⟨hx,hxj⟩), abs_mul,
      abs_of_pos (flatNormalizationFactor_pos hθ α)]
    exact (mul_le_mul_of_nonneg_left herr (flatNormalizationFactor_pos hθ α).le).trans_eq
      (flatNormalizationFactor_cancel hθ α)
  · rw [hres.zero_lower x (le_of_not_gt hxj), abs_zero]
    norm_num

end GaussianTilt.MomentMapLinearDirichlet
