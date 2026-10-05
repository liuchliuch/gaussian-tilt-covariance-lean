import GaussianTilt.OperatorDynamics

/-! # Integrated differential estimates with a variable continuous coefficient -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology Interval Matrix.Norms.L2Operator

namespace GaussianTilt.UpperDynamics

/-- Grönwall with a variable continuous coefficient, proved directly from the
right-slope interface by strict barriers and a vanishing perturbation. -/
theorem le_exp_integral_of_rightSlope {f g : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hg : Continuous g)
    (hs : RightSlopeBound f (fun t ↦ g t * f t) a b) :
    ∀ t ∈ Icc a b, f t ≤ f a * Real.exp (∫ x in a..t, g x) := by
  intro t ht
  have hbound (ε : ℝ) (hε : 0 < ε) :
      f t ≤ Real.exp (∫ x in a..t, g x) * (f a + ε * (t - a)) := by
    let B : ℝ → ℝ := fun x ↦ Real.exp (∫ u in a..x, g u) * (f a + ε * (x - a))
    have hd (x : ℝ) : HasDerivAt B
        (g x * B x + ε * Real.exp (∫ u in a..x, g u)) x := by
      have hi := intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable a x)
        hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt
      have h := hi.exp.mul
        ((hasDerivAt_const x (f a)).add (((hasDerivAt_id x).sub_const a).const_mul ε))
      convert h using 1 <;> dsimp [B] <;> ring
    apply image_le_of_liminf_slope_right_lt_deriv_boundary hf hs
      (B := B) (B' := fun x ↦ g x * B x + ε * Real.exp (∫ u in a..x, g u))
    · simp [B]
    · exact hd
    · intro x hx heq
      rw [heq]
      exact lt_add_of_pos_right _ (mul_pos hε (Real.exp_pos _))
    · exact ht
  have hc : ContinuousWithinAt
      (fun ε : ℝ ↦ Real.exp (∫ x in a..t, g x) * (f a + ε * (t - a))) (Ioi 0) 0 := by
    exact (continuous_const.mul (continuous_const.add (continuous_id.mul continuous_const))).continuousAt.continuousWithinAt
  have h := continuousWithinAt_const.closure_le (by simp : (0 : ℝ) ∈ closure (Ioi 0)) hc
    (fun ε (hε : ε ∈ Ioi 0) ↦ hbound ε hε)
  simpa [mul_comm] using h

end GaussianTilt.UpperDynamics

namespace GaussianTilt.CompactProbability
variable {n : ℕ} (P : CompactProbability n)

lemma momentHS_continuous : Continuous P.momentHS := by
  apply Real.continuous_sqrt.comp
  exact continuous_iff_continuousAt.mpr fun t ↦ (P.momentHSSquare_hasDerivAt t).continuousAt

lemma momentHS_rightSlope_of_quadratic_bound (hiso : Reference.isotropic P.measure)
    (hn : 0 < n) {a b : ℝ}
    (hquad : ∀ t ∈ Ico a b, ∀ B : Matrix (Fin n) (Fin n) ℝ, B.IsHermitian →
      ProbabilityTheory.variance (fun x : Point n ↦ matrixQuadratic B (fun i ↦ x i))
        (P.tilt t) ≤ 10 * Matrix.trace ((B * P.momentMatrix t) ^ 2)) :
    UpperDynamics.RightSlopeBound P.momentHS
      (fun t ↦ 10 * ‖P.momentMatrix t‖ * P.momentHS t) a b := by
  apply UpperDynamics.rightSlopeBound_of_hasDerivWithinAt
    (f' := fun t ↦ deriv P.momentHS t)
  · intro t ht
    exact (P.momentHS_hasDerivAt hiso hn t).differentiableAt.hasDerivAt.hasDerivWithinAt
  · intro t ht
    have hS := P.momentHS_pos hiso hn t
    have hderiv := (P.momentHS_hasDerivAt hiso hn t).differentiableAt.hasDerivAt.log hS.ne'
    have hlog := (le_abs_self (deriv (fun s ↦ Real.log (P.momentHS s)) t)).trans
      (P.log_momentHS_bound_of_quadratic_bound hiso hn (hquad t ht))
    rw [hderiv.deriv] at hlog
    exact (div_le_iff₀ hS).mp hlog

/-- Both integrated estimates of original Corollary 3.3, with the quantitative
quadratic-variance inequality isolated as the remaining analytic input. -/
theorem integrated_moments_of_quadratic_bound (hiso : Reference.isotropic P.measure)
    (hn : 0 < n) {a b : ℝ} (hab : a ≤ b)
    (hquad : ∀ t ∈ Ico a b, ∀ B : Matrix (Fin n) (Fin n) ℝ, B.IsHermitian →
      ProbabilityTheory.variance (fun x : Point n ↦ matrixQuadratic B (fun i ↦ x i))
        (P.tilt t) ≤ 10 * Matrix.trace ((B * P.momentMatrix t) ^ 2)) :
    P.momentHS b ≤ P.momentHS a * Real.exp (10 * ∫ x in a..b, ‖P.momentMatrix x‖) ∧
    ‖P.momentMatrix b‖ ≤ ‖P.momentMatrix a‖ * Real.exp (10 * ∫ x in a..b, P.momentHS x) := by
  have hS := UpperDynamics.le_exp_integral_of_rightSlope P.momentHS_continuous.continuousOn
    (continuous_const.mul P.momentMatrix_continuous.norm)
    (P.momentHS_rightSlope_of_quadratic_bound hiso hn hquad) b ⟨hab, le_rfl⟩
  have hu := UpperDynamics.le_exp_integral_of_rightSlope P.momentMatrix_continuous.norm.continuousOn
    (continuous_const.mul P.momentHS_continuous)
    (P.momentOperatorNorm_rightSlope_of_quadratic_bound hquad) b ⟨hab, le_rfl⟩
  simpa only [intervalIntegral.integral_const_mul] using And.intro hS hu

end GaussianTilt.CompactProbability
