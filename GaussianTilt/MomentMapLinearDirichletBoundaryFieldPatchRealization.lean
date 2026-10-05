import GaussianTilt.MomentMapLinearDirichletSmoothDomainBoundaryJetPullback
import GaussianTilt.MomentMapLinearDirichletCoordinateJetFieldsEmbedding

/-! # Physical boundary regularity from the actual recovered weak coordinate fields

The recovered gradient and Hessian create a true flat Hölder jet. The
constructed IFT chart then creates the physical local fields required by
the final global Laplace gluing, including the genuine curvature term.
-/
noncomputable section
set_option maxHeartbeats 2000000
open Set Filter Matrix
open scoped Topology ContDiff BoundedContinuousFunction Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.HolderSpace GaussianTilt.MomentMapRegularity GaussianTilt.Letwin GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapSchauder
variable {n : ℕ}

theorem boundary_secondFieldPatch_of_inverse_model_fields
    {S A : Set (E n)} (d : SmoothInnerDomain S A)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {f : Space {y | d.coordinateDefining y ≤ 0} ℝ α}
    (data : SmoothDomainLaplaceStartData d α f)
    (a : E n) (ha : a ∈ frontier d.body) (q : Fin n)
    (hq : fderiv ℝ d.defining a (EuclideanSpace.basisFun (Fin n) ℝ q)≠0)
    {s r : ℝ} (hs : 0 < s) (hr : 0 < r) (hr1 : r ≤ 1)
    (ψ : CoordinateSpace n → CoordinateSpace n)
    (hψ : ∀ y ∈ rawChartClosedBall (n := n) 1,
      ψ =ᶠ[𝓝 y] scaledRawInverseChart d.smooth a q hq s)
    (G : CoordinateSpace n → CoordinateSpace n)
    (H : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hu : ContinuousOn (data.representative ∘ ψ) (coordinateClosedHalfBall q r))
    (hG : ContinuousOn G (coordinateClosedHalfBall q r))
    (hH : ContinuousOn H (coordinateClosedHalfBall q r))
    (hDu : ∀ x ∈ coordinateClosedHalfBall q r,
      HasFDerivWithinAt (data.representative ∘ ψ) (coordinateCovector (G x)) (coordinateClosedHalfBall q r) x)
    (hDG : ∀ k x, x ∈ coordinateClosedHalfBall q r →
      HasFDerivWithinAt (fun y => G y k) (coordinateCovector (H x k)) (coordinateClosedHalfBall q r) x)
    (hHolder : BoundedHolderOn α H (coordinateClosedHalfBall q r)) :
    Nonempty (SecondFieldPatch d.body α data.euclideanRepresentative a) := by
  obtain ⟨J,hJ,hFirst,hSecond⟩ := exists_halfBall_jet_of_closed_coordinate_fields q hr hα hα1
    (data.representative ∘ ψ) G H hu hG hH hDu hDG hHolder
  exact boundary_secondFieldPatch_of_inverse_model_jet d hα hα1 data a ha q hq hs hr hr1 ψ hψ J hJ

end GaussianTilt.MomentMapLinearDirichlet
