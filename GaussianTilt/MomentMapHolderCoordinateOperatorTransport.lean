import GaussianTilt.MomentMapHolderCoordinateJetTransport
import GaussianTilt.MomentMapHolderEllipticOperator
import GaussianTilt.MomentMapLinearDirichletFlatteningCoordinates
import GaussianTilt.MomentMapCalabiAffine

/-! # Exact elliptic PDE transfer for actual raw/Euclidean Hölder jets -/
noncomputable section
set_option maxHeartbeats 2000000
open Set Filter Matrix
open scoped Topology ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin GaussianTilt.HolderSpace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapLinearDirichlet
variable {n : ℕ}
namespace SmoothInnerDomain
variable {S A : Set (E n)} (d : SmoothInnerDomain S A)

theorem coordinate_transport_elliptic_equation {α : ℝ} (hα : 0 < α)
    (J : zeroBoundary (CoordinateSpace n) ℝ d.coordinate_body_convex α)
    (j : zeroBoundary (E n) ℝ d.convex_body α)
    (hvalue : ∀ x : d.body, value d.body ℝ α (jetValue (E n) ℝ d.convex_body α j.1) x =
      extendValue α (jetValue (CoordinateSpace n) ℝ d.coordinate_body_convex α J.1) (coordinateEquiv n x))
    (B : Fin n → Fin n → Space {y | d.coordinateDefining y ≤ 0} ℝ α)
    {x : E n} (hx : x ∈ interior d.body) :
    euclideanEllipticOperator (fun i k => extendValue α (B i k) (coordinateEquiv n x))
      (extendValue α (jetValue (E n) ℝ d.convex_body α j.1)) x =
    extendValue α (ellipticDirichletOperator d.coordinate_body_convex α B J) (coordinateEquiv n x) := by
  let c := coordinateEquiv n
  let u := extendValue α (jetValue (CoordinateSpace n) ℝ d.coordinate_body_convex α J.1)
  let v := extendValue α (jetValue (E n) ℝ d.convex_body α j.1)
  have hxi : c x ∈ interior {y | d.coordinateDefining y ≤ 0} := by
    have he : c '' interior d.body = interior (c '' d.body) := c.toHomeomorph.image_interior d.body
    rw [d.coordinate_body_eq, ← he]
    exact mem_image_of_mem c hx
  have hxs := interior_subset hxi
  have he : u =ᶠ[𝓝 (c x)] coordinatePullback v := by
    have hn : ∀ᶠ y in 𝓝 (c x), c.symm y ∈ interior d.body := by
      have hh := c.symm.continuous.tendsto (c x) (isOpen_interior.mem_nhds (by simpa only [c.symm_apply_apply] using hx))
      exact hh
    filter_upwards [hn] with y hy
    have hv := hvalue ⟨c.symm y,interior_subset hy⟩
    rw [← extendValue_mem α _ (interior_subset hy)] at hv
    simpa only [coordinatePullback,Function.comp_apply,c.apply_symm_apply] using hv.symm
  rw [extendValue_mem α _ hxs,ellipticDirichletOperator_eq_actual d.coordinate_body_convex hα B J ⟨c x,hxs⟩ hxi]
  have hcoeff : (fun i k => extendValue α (B i k) (coordinateEquiv n x)) =
      (fun i k => value _ ℝ α (B i k) ⟨c x,hxs⟩) := by
    funext i k
    exact extendValue_mem α (B i k) hxs
  rw [hcoeff]
  change euclideanEllipticOperator (fun i k => value _ ℝ α (B i k) ⟨c x,hxs⟩) v x =
    linearizedMA (fun i k => value _ ℝ α (B i k) ⟨c x,hxs⟩) u (c x)
  rw [linearizedMA,coordinateHessian_congr_nhds he]
  exact (linearizedMA_coordinatePullback_at _
    ((jet_contDiffOn_two d.convex_body hα j.1).contDiffAt (isOpen_interior.mem_nhds hx))).symm

end SmoothInnerDomain
end GaussianTilt.MomentMapRegularity
