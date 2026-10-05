import GaussianTilt.MomentMapRegularityReferenceFactory
import GaussianTilt.MomentMapRegularityStrongSmoothness

/-! # Exact remaining classical Dirichlet obligation for the original compact Letwin bound

This file makes no solvability assertion. It proves that the actual smooth
inner-domain solver, once constructed, discharges the entire remaining
source regularity and original compact variance chain.
-/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin

 theorem strongBallSourceSmoothness_of_classical_inner_solvers
    (hsolve : ∀ (n:ℕ) [NeZero n], ∀ (S:Set (E n)) (d:SmoothInnerDomain S ∅),
      ∃ v : E n → ℝ, Continuous v ∧ ContDiffOn ℝ ∞ v (interior d.body) ∧ ConvexOn ℝ d.body v ∧
        (∀ x∈frontier d.body, v x=0) ∧
        (∀ x∈interior d.body, (coordinateHessian (coordinatePullback v) (coordinateEquiv n x)).PosDef) ∧
        ∀ x∈interior d.body, (coordinateHessian (coordinatePullback v) (coordinateEquiv n x)).det=1) :
    StrongBallSourceSmoothness := by
  apply strongBallSourceSmoothness_of_classical_references
  intro n hn
  exact exists_smooth_unit_reference_of_classical_inner_solver (hsolve n)

 theorem isotropicQuadraticVarianceBound_of_classical_inner_solvers
    (hsolve : ∀ (n:ℕ) [NeZero n], ∀ (S:Set (E n)) (d:SmoothInnerDomain S ∅),
      ∃ v : E n → ℝ, Continuous v ∧ ContDiffOn ℝ ∞ v (interior d.body) ∧ ConvexOn ℝ d.body v ∧
        (∀ x∈frontier d.body, v x=0) ∧
        (∀ x∈interior d.body, (coordinateHessian (coordinatePullback v) (coordinateEquiv n x)).PosDef) ∧
        ∀ x∈interior d.body, (coordinateHessian (coordinatePullback v) (coordinateEquiv n x)).det=1) :
    Reference.IsotropicQuadraticVarianceBound :=
  isotropicQuadraticVarianceBound_of_strong_ball_smoothness
    (strongBallSourceSmoothness_of_classical_inner_solvers hsolve)

end GaussianTilt.MomentMapRegularity
