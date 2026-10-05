import GaussianTilt.MomentMapLinearDirichletSmoothDomainSurjectivity
import GaussianTilt.MomentMapClassicalDirichletLinearClosure

/-! # The genuine classical unit-density Monge–Ampère Dirichlet solver

The weak-to-classical Laplace starting inverse, global cofactor Schauder
estimate, true Banach derivative inversion, and full nonlinear continuation
are all proved. The result is interior smoothness on the actual domain;
no global smooth extension of the unknown is asserted or assumed.
-/
noncomputable section
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 1000
open Set Filter Matrix
open scoped Topology ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin GaussianTilt.HolderSpace GaussianTilt.MomentMapLinearDirichlet
variable {n : ℕ}
namespace SmoothInnerDomain
variable {S A : Set (E n)} (d : SmoothInnerDomain S A)

/-- The literal Monge–Ampère derivative has a genuine inverse on the
actual zero-boundary Hölder Banach domain at every positive Hessian jet. -/
theorem cofactor_derivative_bijective [NeZero n]
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (j : zeroBoundary (CoordinateSpace n) ℝ d.coordinate_body_convex α)
    (hpd : ∀ x : {y | d.coordinateDefining y ≤ 0},
      (hessianMatrix d.coordinate_body_convex α j.1 x).PosDef) :
    Function.Bijective (fderiv ℝ (dirichletMongeAmpere d.coordinate_body_convex α 0) j) :=
  d.cofactor_derivative_bijective_of_laplace_surjective hα hα1 j hpd
    (smoothDomain_laplace_surjective d hα hα1)

/-- Every genuinely constructed smooth strongly convex inner domain has
a continuous convex zero-boundary unit-density solution, smooth and strictly
elliptic throughout its actual interior. No regularity or solver premise remains. -/
theorem exists_classical_unit_dirichlet [NeZero n] :
    ∃ u : E n → ℝ, Continuous u ∧ ContDiffOn ℝ ∞ u (interior d.body) ∧
      ConvexOn ℝ d.body u ∧ (∀ x ∈ frontier d.body, u x=0) ∧
      (∀ x ∈ interior d.body, (coordinateHessian (coordinatePullback u) (coordinateEquiv n x)).PosDef) ∧
      (∀ x ∈ interior d.body, (coordinateHessian (coordinatePullback u) (coordinateEquiv n x)).det=1) :=
  d.exists_classical_unit_dirichlet_of_laplace_surjective
    (fun _ hα hα1 => smoothDomain_laplace_surjective d hα hα1)

end SmoothInnerDomain
end GaussianTilt.MomentMapRegularity
