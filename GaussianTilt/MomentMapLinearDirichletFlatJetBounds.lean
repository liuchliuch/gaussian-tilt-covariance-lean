import GaussianTilt.MomentMapLinearDirichletFlatUniform

/-! # Uniform bounds for the actual limiting flat boundary jets -/
noncomputable section
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 1000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff Gradient ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapRegularity GaussianTilt.MomentMapSchauder
variable {n : ℕ}

/-- The genuine boundary expansion also bounds its actual gradient and
symmetric Hessian. The proof extracts coefficients on a real interior ball
of the half-ball and never assumes a boundary derivative limit. -/
theorem exists_uniform_flat_boundary_jets [NeZero n] {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : Fin n) (u f : KernelSpace n → ℝ),
      FlatWeakPoisson j u f → Continuous f → ∀ B H F : ℝ,
      0 ≤ B → 0 ≤ H → 0 ≤ F → (∀ x y, |f x-f y| ≤ H*‖x-y‖^α) →
      (∀ x ∈ Metric.ball (0 : KernelSpace n) 2, |u x| ≤ B) →
      (∀ x ∈ Metric.ball (0 : KernelSpace n) 2, |f x| ≤ F) →
      ∀ a : KernelSpace n, ‖a‖ ≤ 1 → a j = 0 →
      ∃ p : KernelSpace n, ∃ T : KernelSpace n →L[ℝ] KernelSpace n,
        (∀ v w, inner ℝ (T v) w = inner ℝ v (T w)) ∧
        ‖p‖ ≤ C*(B+H+F) ∧ ‖T‖ ≤ C*(B+H+F) ∧
        (∀ h, h j = 0 → quadraticJet 0 p 0 T h = 0) ∧
        (∀ h, kernelLaplacian (quadraticJet 0 p 0 T) h = -f a) ∧
        (∀ h, ‖h‖ ≤ 1/4 → 0 ≤ h j →
          |u (a+h)-quadraticJet 0 p 0 T h| ≤ C*(B+H+F)*‖h‖^(2+α)) := by
  obtain ⟨C,hC,hExpansion⟩ := exists_uniform_flat_boundary_poisson_expansions (n := n) hα hα1
  let D := 1024*(1+C)
  have hD : 0 < D := by dsimp [D]; positivity
  have hCD : C ≤ D := by dsimp [D]; linarith
  refine ⟨D,hD,?_⟩
  intro j u f hu hfc B H F hB hH hF hfH huB hfB a ha haj
  obtain ⟨A,Q,hQ,hPlane,hLap,hRem⟩ := hExpansion j u f hu hfc B H hB hH hfH huB a ha haj
  let P := flatTaylorPolynomial A Q
  let p := gradient P 0
  let T := frechetHessian P 0
  have hrepr : P = quadraticJet 0 p 0 T := funext (flatTaylorPolynomial_eq_quadraticJet A Q)
  have hTs : ∀ v w, inner ℝ (T v) w = inner ℝ v (T w) := flatTaylorPolynomial_frechetHessian_symmetric A Q
  let N := B+H+F
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hab : a ∈ Metric.ball (0 : KernelSpace n) 2 := by
    rw [Metric.mem_ball,dist_zero_right]; linarith
  have hfa := hfB a hab
  have hRem' : ∀ h, ‖h‖ ≤ 1/4 → 0 ≤ h j →
      |u (a+h)-quadraticJet 0 p 0 T h| ≤ C*N*‖h‖^(2+α) := by
    intro h hh hhj
    have hb := hRem h hh hhj
    rw [← hrepr]
    exact hb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (show B+H+|f a| ≤ N by dsimp [N]; linarith) hC.le)
      (Real.rpow_nonneg (norm_nonneg h) _))
  have hPoly : ∀ h : KernelSpace n, ‖h‖ ≤ 1/4 → 0 ≤ h j →
      |quadraticJet 0 p 0 T h| ≤ (1+C)*N := by
    intro h hh hhj
    have hsum : a+h ∈ Metric.ball (0 : KernelSpace n) 2 := by
      rw [Metric.mem_ball,dist_zero_right]
      have hb := norm_add_le a h
      linarith
    have hpow : ‖h‖^(2+α) ≤ 1 := Real.rpow_le_one (norm_nonneg h) (by linarith) (by linarith)
    have hb := hRem' h hh hhj
    have ht : C*N*‖h‖^(2+α) ≤ C*N := mul_le_of_le_one_right (mul_nonneg hC.le hN) hpow
    have hn : B ≤ N := by dsimp [N]; linarith
    have hp : |quadraticJet 0 p 0 T h| ≤ |u (a+h)|+|u (a+h)-quadraticJet 0 p 0 T h| := by
      have he : quadraticJet 0 p 0 T h = u (a+h)-(u (a+h)-quadraticJet 0 p 0 T h) := by ring
      calc
        _ = |u (a+h)-(u (a+h)-quadraticJet 0 p 0 T h)| := congrArg abs he
        _ ≤ _ := abs_sub _ _
    nlinarith [huB (a+h) hsum]
  obtain ⟨_,hpBound,hTBound⟩ := quadraticJet_halfBall_coefficients j 0 p T hTs
    (by norm_num : (0:ℝ)<1/4) (by positivity : 0 ≤ (1+C)*N) hPoly
  refine ⟨p,T,hTs,?_,?_,?_,?_,?_⟩
  · dsimp [D]
    nlinarith [mul_nonneg (by positivity : 0 ≤ 1+C) hN]
  · convert hTBound using 1 <;> dsimp [D,N] <;> ring
  · intro h hh
    rw [← hrepr]
    exact hPlane h hh
  · intro h
    rw [← hrepr]
    exact hLap h
  · intro h hh hhj
    exact (hRem' h hh hhj).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCD hN) (Real.rpow_nonneg (norm_nonneg h) _))

end GaussianTilt.MomentMapLinearDirichlet
