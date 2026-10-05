import GaussianTilt.MomentMapHolderLinearEquivTransport
import GaussianTilt.MomentMapClassicalDirichletGeometryCoordinates

/-! # Actual raw-coordinate / Euclidean zero-boundary Hölder jet transport -/
noncomputable section
set_option maxHeartbeats 1000000
open Set
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin GaussianTilt.HolderSpace
variable {n : ℕ}
namespace SmoothInnerDomain
variable {S A : Set (E n)} (d : SmoothInnerDomain S A)

theorem exists_coordinate_euclidean_jet_transport {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      ∀ J : zeroBoundary (CoordinateSpace n) ℝ d.coordinate_body_convex α,
      ∃ j : zeroBoundary (E n) ℝ d.convex_body α,
        ‖j‖ ≤ C*‖J‖ ∧ ‖J‖ ≤ D*‖j‖ ∧
        (∀ x : d.body, value d.body ℝ α (jetValue (E n) ℝ d.convex_body α j.1) x =
          extendValue α (jetValue (CoordinateSpace n) ℝ d.coordinate_body_convex α J.1) (coordinateEquiv n x)) ∧
        (∀ x : d.body, value d.body ((E n) →L[ℝ] ℝ) α (jetFirst (E n) ℝ d.convex_body α j.1) x =
          chartFirst (extendValue α (jetFirst (CoordinateSpace n) ℝ d.coordinate_body_convex α J.1)) (coordinateEquiv n) x) ∧
        (∀ x : d.body, value d.body ((E n) →L[ℝ] (E n) →L[ℝ] ℝ) α
          (jetSecond (E n) ℝ d.convex_body α j.1) x =
          chartSecond (extendValue α (jetFirst (CoordinateSpace n) ℝ d.coordinate_body_convex α J.1))
            (extendValue α (jetSecond (CoordinateSpace n) ℝ d.coordinate_body_convex α J.1)) (coordinateEquiv n) x) := by
  have hTi : (interior d.body).Nonempty := by rw [d.interior_body]; exact d.negative_nonempty
  have hSi : (interior {x | d.coordinateDefining x ≤ 0}).Nonempty := by
    have he : (coordinateEquiv n) '' interior d.body = interior ((coordinateEquiv n) '' d.body) :=
      (coordinateEquiv n).toHomeomorph.image_interior d.body
    rw [d.coordinate_body_eq, ← he]
    exact hTi.image _
  exact exists_zeroBoundary_linearEquiv_transport d.coordinate_body_convex d.convex_body
    d.coordinate_body_compact d.compact_sublevel hSi hTi hα hα1 (coordinateEquiv n) d.coordinate_body_eq.symm

/-- The inverse coordinate transfer, for the genuine Euclidean weak
Dirichlet solution after boundary regularity has been constructed. -/
theorem exists_euclidean_coordinate_jet_transport {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      ∀ J : zeroBoundary (E n) ℝ d.convex_body α,
      ∃ j : zeroBoundary (CoordinateSpace n) ℝ d.coordinate_body_convex α,
        ‖j‖ ≤ C*‖J‖ ∧ ‖J‖ ≤ D*‖j‖ ∧
        (∀ x : {y | d.coordinateDefining y ≤ 0},
          value {y | d.coordinateDefining y ≤ 0} ℝ α
            (jetValue (CoordinateSpace n) ℝ d.coordinate_body_convex α j.1) x =
          extendValue α (jetValue (E n) ℝ d.convex_body α J.1) ((coordinateEquiv n).symm x)) := by
  have hEi : (interior d.body).Nonempty := by rw [d.interior_body]; exact d.negative_nonempty
  have hRi : (interior {x | d.coordinateDefining x ≤ 0}).Nonempty := by
    have he : (coordinateEquiv n) '' interior d.body = interior ((coordinateEquiv n) '' d.body) :=
      (coordinateEquiv n).toHomeomorph.image_interior d.body
    rw [d.coordinate_body_eq, ← he]
    exact hEi.image _
  have hRE : (coordinateEquiv n).symm '' {y | d.coordinateDefining y ≤ 0} = d.body := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact hy
    · intro hx
      refine ⟨coordinateEquiv n x,?_,(coordinateEquiv n).symm_apply_apply x⟩
      simpa only [coordinateDefining,coordinatePullback,Function.comp_apply,ContinuousLinearEquiv.symm_apply_apply] using hx
  obtain ⟨C,D,hC,hD,htrans⟩ := exists_zeroBoundary_linearEquiv_transport d.convex_body d.coordinate_body_convex
    d.compact_sublevel d.coordinate_body_compact hEi hRi hα hα1 (coordinateEquiv n).symm hRE
  refine ⟨C,D,hC,hD,?_⟩
  intro J
  obtain ⟨j,hj,hJ,hv,hD,hH⟩ := htrans J
  exact ⟨j,hj,hJ,hv⟩

end SmoothInnerDomain
end GaussianTilt.MomentMapRegularity
