import GaussianTilt.MomentMapLinearDirichletFlatCentering

/-!
# Actual flat weak Poisson boundary expansion for arbitrary forcing

A genuine normal quadratic removes the nonzero forcing trace. Its compact
upper-half-space subtraction preserves the weak equation. The centered
Campanato endpoint then gives the actual symmetric boundary Taylor
polynomial with the correct inhomogeneous Laplacian.
-/
noncomputable section
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 1000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma flatTaylorPolynomial_add (A A' : KernelSpace n →L[ℝ] ℝ)
    (Q Q' : KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ) (x : KernelSpace n) :
    flatTaylorPolynomial (A+A') (Q+Q') x =
      flatTaylorPolynomial A Q x+flatTaylorPolynomial A' Q' x := by
  simp only [flatTaylorPolynomial,ContinuousLinearMap.add_apply]
  ring

/-- A scale-uniform boundary Schauder expansion derived from the literal
weak equation, without boundary differentiability or a zero forcing trace. -/
theorem exists_flat_boundary_poisson_expansion [NeZero n] {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : Fin n) (u f : KernelSpace n → ℝ),
      FlatWeakPoisson j u f → Continuous f → ∀ B H : ℝ,
      0 ≤ B → 0 ≤ H → (∀ x y, |f x-f y| ≤ H*‖x-y‖^α) →
      (∀ x ∈ Metric.ball (0 : KernelSpace n) 2, |u x| ≤ B) →
      ∃ A : KernelSpace n →L[ℝ] ℝ, ∃ Q : KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ,
        (∀ v w, Q v w = Q w v) ∧
        (∀ x, x j = 0 → flatTaylorPolynomial A Q x = 0) ∧
        (∀ x, kernelLaplacian (flatTaylorPolynomial A Q) x = -f 0) ∧
        (∀ x, ‖x‖ ≤ 1 → 0 ≤ x j →
          |u x-flatTaylorPolynomial A Q x| ≤ C*(B+H+|f 0|)*‖x‖^(2+α)) := by
  obtain ⟨C,hC,hCentered⟩ := exists_centered_flat_boundary_expansion (n := n) hα hα1
  obtain ⟨D,hD,hCutoff⟩ := exists_flat_centered_forcing_bound (n := n) hα.le hα1.le
  refine ⟨C*(3+D),by positivity,?_⟩
  intro j u f hu hfc B H hB hH hfH huB
  let Q₀ := flatNormalQuadraticForm j (-f 0)
  let P₀ := flatTaylorPolynomial 0 Q₀
  let g := fun x => flatResidualBump n x*(f x-f 0)
  have hP₀ : ContDiff ℝ ∞ P₀ := contDiff_flatTaylorPolynomial 0 Q₀
  have hPplane : ∀ x, x j = 0 → P₀ x = 0 := by
    intro x hx
    simp only [P₀,Q₀,flatNormalQuadratic_polynomial,hx,zero_pow (by decide : 2 ≠ 0),mul_zero]
  have hPlap : ∀ x, kernelLaplacian P₀ x = -f 0 := flatNormalQuadratic_laplacian j (-f 0)
  have hg : Continuous g := (flatResidualBump n).continuous.mul (hfc.sub continuous_const)
  have hgc : HasCompactSupport g := (flatResidualBump n).hasCompactSupport.mul_right
  have hg0 : g 0 = 0 := by simp only [g,sub_self,mul_zero]
  have hgH : ∀ x y, |g x-g y| ≤ (D*H)*‖x-y‖^α := hCutoff f H hH hfH
  have hsource : ∀ x ∈ flatUpperBall j 2, g x = f x+kernelLaplacian P₀ x := by
    intro x hx
    rw [hPlap]
    dsimp [g]
    rw [(flatResidualBump n).one_of_mem_closedBall (Metric.ball_subset_closedBall hx.1),one_mul]
    ring
  have hv := hu.subtractSmooth hfc hg hP₀ hPplane hsource
  have hPbound : ∀ x ∈ Metric.ball (0 : KernelSpace n) 2, |P₀ x| ≤ 2*|f 0| := by
    intro x hx
    have hn : ‖x‖ < 2 := by simpa only [Metric.mem_ball,dist_zero_right] using hx
    have hj : |x j| ≤ ‖x‖ := PiLp.norm_apply_le x j
    have hj2 : (x j)^2 ≤ 4 := by nlinarith [sq_abs (x j),abs_nonneg (x j)]
    simp only [P₀,Q₀,flatNormalQuadratic_polynomial,abs_mul,abs_div,abs_neg,abs_of_pos (by norm_num : (0:ℝ)<2),abs_sq]
    nlinarith [mul_le_mul_of_nonneg_left hj2 (abs_nonneg (f 0))]
  have hvB : ∀ x ∈ Metric.ball (0 : KernelSpace n) 2, |flatResidual j u P₀ x| ≤ B+2*|f 0| := by
    apply flatResidual_bound (by positivity) hu.zero_lower
    intro x hx _
    exact (abs_sub _ _).trans (add_le_add (huB x hx) (hPbound x hx))
  obtain ⟨A,Q,hQs,hPlane,hLap,hRem⟩ := hCentered j (flatResidual j u P₀) g hv hg hgc
    (B+2*|f 0|) (D*H) (by positivity) (by positivity) hgH hg0 hvB
  have hadd : ∀ x, flatTaylorPolynomial A (Q+Q₀) x = flatTaylorPolynomial A Q x+P₀ x := by
    intro x
    simpa only [add_zero] using flatTaylorPolynomial_add A 0 Q Q₀ x
  have hfinalplane : ∀ x, x j = 0 → flatTaylorPolynomial A (Q+Q₀) x = 0 := by
    intro x hx
    rw [hadd,hPlane x hx,hPplane x hx,add_zero]
  refine ⟨A,Q+Q₀,?_,hfinalplane,?_,?_⟩
  · intro v w
    simp only [ContinuousLinearMap.add_apply]
    rw [hQs v w,flatNormalQuadraticForm_symmetric j (-f 0) v w]
  · intro x
    rw [funext hadd,kernelLaplacian_add_C2 (contDiff_infty.mp (contDiff_flatTaylorPolynomial A Q) 2)
      (contDiff_infty.mp hP₀ 2),hLap,hPlap,zero_add]
  · intro x hx hxj
    have hb : x ∈ Metric.ball (0 : KernelSpace n) 2 := by
      rw [Metric.mem_ball,dist_zero_right]; linarith
    by_cases hj : 0 < x j
    · have he : u x-flatTaylorPolynomial A (Q+Q₀) x =
          flatResidual j u P₀ x-flatTaylorPolynomial A Q x := by
        rw [hadd,flatResidual_eq j u P₀ ⟨hb,hj⟩]; ring
      rw [he]
      apply (hRem x hx hxj).trans
      have hh : B+2*|f 0|+D*H ≤ (3+D)*(B+H+|f 0|) := by
        nlinarith [mul_nonneg hD.le hB,mul_nonneg hD.le (abs_nonneg (f 0))]
      have hmul := mul_le_mul_of_nonneg_left hh hC.le
      have hp := Real.rpow_nonneg (norm_nonneg x) (2+α)
      nlinarith [mul_le_mul_of_nonneg_right hmul hp]
    · have hz : x j = 0 := le_antisymm (le_of_not_gt hj) hxj
      rw [hu.zero_lower x hz.le,hfinalplane x hz,sub_self,abs_zero]
      positivity

end GaussianTilt.MomentMapLinearDirichlet
