import GaussianTilt.MomentMapLinearDirichletSmoothDomainStartInterior
import GaussianTilt.MomentMapLinearDirichletCoordinateJetEquation

/-! # Final Laplace preimage assembly, with the remaining boundary input explicit

All starting-data existence, interior regularity, cover/gluing, compatibility,
coordinate transfer, sign and Banach-operator realization are discharged here.
The only local analytic input is the actual physical boundary field patch.
-/
noncomputable section
set_option maxHeartbeats 2000000
open Set
open scoped Topology BoundedContinuousFunction
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.HolderSpace GaussianTilt.MomentMapRegularity GaussianTilt.Letwin
variable {n : ℕ}

/-- Once actual boundary fields have been constructed for the common weak
representative, the raw Hölder Laplace preimage follows with no further
existence, global regularity or compatibility assumptions. -/
theorem raw_laplace_preimage_of_boundary_secondFieldPatches [NeZero n]
    {S A : Set (E n)} (d : SmoothInnerDomain S A)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (f : Space {y | d.coordinateDefining y ≤ 0} ℝ α)
    (data : SmoothDomainLaplaceStartData d α f)
    (hboundary : ∀ z ∈ frontier d.body,
      Nonempty (SecondFieldPatch d.body α data.euclideanRepresentative z)) :
    ∃ j : zeroBoundary (CoordinateSpace n) ℝ d.coordinate_body_convex α,
      ellipticDirichletOperator d.coordinate_body_convex α
        (identityFields {y | d.coordinateDefining y ≤ 0} α) j=f := by
  have hint : (interior d.body).Nonempty := by
    rw [d.interior_body]
    exact d.negative_nonempty
  have hp : ∀ x : d.body, Nonempty (SecondFieldPatch d.body α data.euclideanRepresentative x) := by
    intro x
    by_cases hx : (x : E n) ∈ interior d.body
    · exact data.interior_secondFieldPatch hα hα1 x hx
    · exact hboundary x ⟨subset_closure x.2,hx⟩
  obtain ⟨J,hJ⟩ := exists_zeroBoundary_jet_of_secondFieldPatches d.convex_body d.compact_sublevel
    hint hα hα1.le data.euclideanRepresentative_continuous.continuousOn
    data.euclideanRepresentative_zero_frontier hp
  exact exists_raw_laplace_jet_of_euclidean_jet d hα hα1.le f J data.euclideanRepresentative hJ
    data.euclideanRepresentative_positive_equation

end GaussianTilt.MomentMapLinearDirichlet
