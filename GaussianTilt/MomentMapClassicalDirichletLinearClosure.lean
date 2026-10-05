import GaussianTilt.MomentMapSchauderGlobalCofactorEstimate
import GaussianTilt.MomentMapClassicalDirichletContinuationFinal

/-! # Concrete cofactor inversion and nonlinear continuation from the actual Laplace start

The cofactor estimate is the proved global boundary Schauder estimate, not
an input. This module isolates only the literal Laplace surjectivity still
supplied by the genuine weak boundary construction.
-/
noncomputable section
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 1000
open Set Filter Matrix
open scoped Topology ContDiff BoundedContinuousFunction
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin GaussianTilt.HolderSpace GaussianTilt.MomentMapSchauder
variable {n : ℕ}
namespace SmoothInnerDomain
variable {S A : Set (E n)} (d : SmoothInnerDomain S A)

/-- The actual cofactor Banach derivative is invertible once the genuine
positive Laplace starting map is surjective. Its uniform homotopy inverse
estimate is derived here from the completed global Schauder theorem. -/
theorem cofactor_derivative_bijective_of_laplace_surjective [NeZero n]
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (j : zeroBoundary (CoordinateSpace n) ℝ d.coordinate_body_convex α)
    (hpd : ∀ x : {y | d.coordinateDefining y ≤ 0},
      (hessianMatrix d.coordinate_body_convex α j.1 x).PosDef)
    (hstart : Function.Surjective (ellipticDirichletOperator d.coordinate_body_convex α
      (identityFields {y | d.coordinateDefining y ≤ 0} α))) :
    Function.Bijective (fderiv ℝ (dirichletMongeAmpere d.coordinate_body_convex α 0) j) := by
  obtain ⟨C,hC,hbound⟩ := exists_smooth_domain_cofactor_homotopy_uniform_estimate d hα hα1 j.1 hpd
  exact dirichletMongeAmpere_fderiv_bijective_of_uniform_estimate d.coordinate_body_convex α j hC hbound hstart

/-- Every other nonlinear step, including fixed-exponent closedness and
the actual smooth initial solution, is already proved. Only the exact
linear Laplace starting inverse is supplied to this closure theorem. -/
theorem exists_classical_unit_dirichlet_of_laplace_surjective [NeZero n]
    (hstart : ∀ α : ℝ, 0 < α → α < 1 →
      Function.Surjective (ellipticDirichletOperator d.coordinate_body_convex α
        (identityFields {y | d.coordinateDefining y ≤ 0} α))) :
    ∃ u : E n → ℝ, Continuous u ∧ ContDiffOn ℝ ∞ u (interior d.body) ∧
      ConvexOn ℝ d.body u ∧ (∀ x ∈ frontier d.body, u x=0) ∧
      (∀ x ∈ interior d.body, (coordinateHessian (coordinatePullback u) (coordinateEquiv n x)).PosDef) ∧
      (∀ x ∈ interior d.body, (coordinateHessian (coordinatePullback u) (coordinateEquiv n x)).det=1) := by
  apply d.exists_classical_unit_dirichlet_of_linearized_bijective
  intro α hα hα1 t ht j hpd hMA
  apply d.cofactor_derivative_bijective_of_laplace_surjective hα hα1 j _ (hstart α hα hα1)
  intro x
  have hh := hpd x x.2
  rw [intrinsicHessian_eq_stored d.coordinate_body_convex α j.1 x] at hh
  exact hh

end SmoothInnerDomain
end GaussianTilt.MomentMapRegularity
