import GaussianTilt.MomentMapLinearDirichletJetPatchEquation
import GaussianTilt.MomentMapHolderCoordinateJetTransport
import GaussianTilt.MomentMapLinearDirichletCoordinates

/-! # Exact transfer of the constructed Euclidean Dirichlet jet to the raw inverse -/
noncomputable section
set_option maxHeartbeats 2000000
open Set Matrix
open scoped Topology BoundedContinuousFunction
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.HolderSpace GaussianTilt.MomentMapRegularity GaussianTilt.Letwin
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

/-- A genuine Euclidean zero-boundary jet solving the positive Laplace
problem produces a preimage under the actual raw-coordinate Banach operator.
This is coordinate and operator transfer; boundary regularity of the weak
solution is supplied by the separately constructed Euclidean jet. -/
theorem exists_raw_laplace_jet_of_euclidean_jet
    {S A : Set (E n)} (d : SmoothInnerDomain S A)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (f : Space {y | d.coordinateDefining y ≤ 0} ℝ α)
    (J : zeroBoundary (E n) ℝ d.convex_body α) (u : E n → ℝ)
    (hv : ∀ x : d.body, value d.body ℝ α (jetValue (E n) ℝ d.convex_body α J.1) x=u x)
    (heq : ∀ x, ∀ hx : x ∈ d.domain, kernelLaplacian u x =
      value {y | d.coordinateDefining y ≤ 0} ℝ α f
        ⟨coordinateEquiv n x,by
          change d.defining ((coordinateEquiv n).symm (coordinateEquiv n x)) ≤ 0
          simpa only [ContinuousLinearEquiv.symm_apply_apply] using (show d.defining x<0 from hx).le⟩) :
    ∃ j : zeroBoundary (CoordinateSpace n) ℝ d.coordinate_body_convex α,
      ellipticDirichletOperator d.coordinate_body_convex α
        (identityFields {y | d.coordinateDefining y ≤ 0} α) j=f := by
  obtain ⟨C,D,hC,hD,htrans⟩ := d.exists_euclidean_coordinate_jet_transport hα hα1
  obtain ⟨j,hj,hJ,hvalue⟩ := htrans J
  refine ⟨j,?_⟩
  have hint : (interior {y | d.coordinateDefining y ≤ 0}).Nonempty := by
    rw [d.coordinate_body_interior,d.coordinate_domain_eq]
    have hn : d.domain.Nonempty := d.negative_nonempty
    exact hn.image _
  apply laplace_jet_eq_of_actual_interior_equation d.coordinate_body_convex
    d.coordinate_body_compact.isClosed hint hα f j (u ∘ (coordinateEquiv n).symm)
  · intro x
    have hxs : (coordinateEquiv n).symm x ∈ d.body := x.2
    rw [hvalue x,extendValue_mem α _ hxs]
    exact hv ⟨(coordinateEquiv n).symm x,x.2⟩
  · intro x hx
    rw [d.coordinate_body_interior] at hx
    have hxi : (coordinateEquiv n).symm x ∈ d.domain := hx
    have ht := euclideanLaplacian_toLp_any u (x : CoordinateSpace n)
    change euclideanLaplacian (u ∘ (coordinateEquiv n).symm) x =
      kernelLaplacian u ((coordinateEquiv n).symm x) at ht
    have he := heq ((coordinateEquiv n).symm x) hxi
    have hl : Matrix.trace (coordinateHessian (u ∘ (coordinateEquiv n).symm) x) =
        euclideanLaplacian (u ∘ (coordinateEquiv n).symm) x := by
      simp only [Matrix.trace,Matrix.diag_apply,coordinateHessian,euclideanLaplacian]
    rw [hl,ht,he]
    congr 1

end GaussianTilt.MomentMapLinearDirichlet
