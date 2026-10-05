import GaussianTilt.MomentMapSchauderLinearUniform
import GaussianTilt.MomentMapSchauderSourceThirdOrder

/-! # Genuine one-derivative linear Schauder bootstrap

From a literal linear equation and C¹,α coefficients/forcing, the theorem
constructs uniform quotient estimates, takes an actual derivative limit,
and obtains C³,α regularity of a C²,α solution.
-/
noncomputable section
set_option maxSynthPendingDepth 1000
open Matrix Set
open scoped ContDiff
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

theorem exists_linear_third_order_holder [NeZero n]
    {u f : KernelSpace n → ℝ} (hu : ContDiff ℝ 2 u) (hf : ContDiff ℝ 1 f)
    {A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, ContDiff ℝ 1 (fun x => A x i j))
    (a : KernelSpace n) {R Hu Hf HA α : ℝ} (hR : 0 < R)
    (hHu : 0 ≤ Hu) (hHf : 0 ≤ Hf) (hHA : 0 ≤ HA) (hα : 0 < α) (hα1 : α < 1)
    (hpos : ∀ x ∈ Metric.closedBall a (2*R), (A x).PosDef)
    (heq : ∀ x ∈ Metric.closedBall a (2*R), euclideanEllipticOperator (A x) u x=f x)
    (hAH : ∀ x ∈ Metric.closedBall a (2*R), ∀ y ∈ Metric.closedBall a (2*R), ∀ i j,
      ‖fderiv ℝ (fun z => A z i j) x-fderiv ℝ (fun z => A z i j) y‖ ≤ HA*‖x-y‖^α)
    (huH : ∀ x ∈ Metric.closedBall a (2*R), ∀ y ∈ Metric.closedBall a (2*R),
      ‖fderiv ℝ (fderiv ℝ u) x-fderiv ℝ (fderiv ℝ u) y‖ ≤ Hu*‖x-y‖^α)
    (hfH : ∀ x ∈ Metric.closedBall a (2*R), ∀ y ∈ Metric.closedBall a (2*R),
      ‖fderiv ℝ f x-fderiv ℝ f y‖ ≤ Hf*‖x-y‖^α) :
    ∃ r C : ℝ, 0 < r ∧ r ≤ R ∧ 0 < C ∧ ContDiffOn ℝ 3 u (Metric.ball a r) ∧
      (∀ x ∈ Metric.ball a r, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x‖ ≤ C) ∧
      (∀ x ∈ Metric.ball a r, ∀ y ∈ Metric.ball a r,
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x-fderiv ℝ (fderiv ℝ (fderiv ℝ u)) y‖ ≤ C*‖x-y‖^α) := by
  obtain ⟨r, C, hr, hrR, hC, hq⟩ := exists_uniform_linear_difference_schauder
    hu hf hA a hR hHu hHf hHA hα hα1 hpos heq hAH huH hfH
  obtain ⟨hc, hb, hh⟩ := contDiffOn_three_of_uniform_second_difference_bounds hu a hr hR hC.le hα hq
  exact ⟨r/2, C, by linarith, by linarith, hC, hc, hb, hh⟩

/-- Local C¹,α coefficient and forcing moduli give a genuine global C³
solution. Only the original C²,α solution and literal PDE are inputs. -/
theorem linear_solution_contDiff_three [NeZero n]
    {u f : KernelSpace n → ℝ} (hu : ContDiff ℝ 2 u) (hf : ContDiff ℝ 1 f)
    {A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, ContDiff ℝ 1 (fun x => A x i j))
    (hpos : ∀ x, (A x).PosDef)
    (heq : ∀ x, euclideanEllipticOperator (A x) u x=f x)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hloc : ∀ a : KernelSpace n, ∃ R Hu Hf HA : ℝ,
      0 < R ∧ 0 ≤ Hu ∧ 0 ≤ Hf ∧ 0 ≤ HA ∧
      (∀ x ∈ Metric.closedBall a (2*R), ∀ y ∈ Metric.closedBall a (2*R), ∀ i j,
        ‖fderiv ℝ (fun z => A z i j) x-fderiv ℝ (fun z => A z i j) y‖ ≤ HA*‖x-y‖^α) ∧
      (∀ x ∈ Metric.closedBall a (2*R), ∀ y ∈ Metric.closedBall a (2*R),
        ‖fderiv ℝ (fderiv ℝ u) x-fderiv ℝ (fderiv ℝ u) y‖ ≤ Hu*‖x-y‖^α) ∧
      (∀ x ∈ Metric.closedBall a (2*R), ∀ y ∈ Metric.closedBall a (2*R),
        ‖fderiv ℝ f x-fderiv ℝ f y‖ ≤ Hf*‖x-y‖^α)) :
    ContDiff ℝ 3 u := by
  apply contDiff_iff_contDiffAt.mpr
  intro a
  obtain ⟨R, Hu, Hf, HA, hR, hHu, hHf, hHA, hAH, huH, hfH⟩ := hloc a
  obtain ⟨r, C, hr, _, _, hc, _⟩ := exists_linear_third_order_holder
    hu hf hA a hR hHu hHf hHA hα hα1 (fun x _ => hpos x) (fun x _ => heq x) hAH huH hfH
  exact hc.contDiffAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))

end GaussianTilt.MomentMapSchauder
