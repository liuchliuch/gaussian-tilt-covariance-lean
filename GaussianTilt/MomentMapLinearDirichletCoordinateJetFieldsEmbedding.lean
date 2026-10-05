import GaussianTilt.MomentMapLinearDirichletCoordinateJetFieldsHolder
import GaussianTilt.MomentMapLinearDirichletJetPatchEmbedding
import GaussianTilt.MomentMapLinearDirichletVariableWeakClosedGeometry

/-! # A genuine raw Hölder jet from the recovered coordinate weak fields

The first/second fields are actual continuous linear maps. The lower
Hölder estimates and both closed-domain segment FTC identities are derived
from the true within derivatives, rather than added as compatibility data.
-/
noncomputable section
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 500000
set_option maxSynthPendingDepth 1000
open Set Filter Matrix
open scoped Topology ContDiff BigOperators Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapRegularity GaussianTilt.HolderSpace GaussianTilt.MomentMapSchauder
variable {n : ℕ}

/-- Construct the actual compatible Hölder Banach jet from the continuous
first-gradient and recovered Hessian fields of the weak solution. -/
theorem exists_jet_of_closed_coordinate_fields
    {S : Set (CoordinateSpace n)} (hS : Convex ℝ S) (hSc : IsCompact S) (hint : (interior S).Nonempty)
    {α : ℝ} (hα : 0<α) (hα1 : α≤1)
    (u : CoordinateSpace n→ℝ) (G : CoordinateSpace n → CoordinateSpace n)
    (H : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hu : ContinuousOn u S) (hG : ContinuousOn G S) (hH : ContinuousOn H S)
    (hDu : ∀ x∈S,HasFDerivWithinAt u (coordinateCovector (G x)) S x)
    (hDG : ∀ k x,x∈S → HasFDerivWithinAt (fun y=>G y k) (coordinateCovector (H x k)) S x)
    (hHolder : BoundedHolderOn α H S) :
    ∃ j : Jet (CoordinateSpace n) ℝ hS α,
      (∀ x : S,value S ℝ α (jetValue (CoordinateSpace n) ℝ hS α j) x=u x) ∧
      (∀ x : S,value S (CoordinateSpace n→L[ℝ]ℝ) α (jetFirst (CoordinateSpace n) ℝ hS α j) x=coordinateCovector (G x)) ∧
      (∀ x : S,value S (CoordinateSpace n→L[ℝ]CoordinateSpace n→L[ℝ]ℝ) α
        (jetSecond (CoordinateSpace n) ℝ hS α j) x=coordinateHessianBilinear (H x)) := by
  let D := fun x=>coordinateCovector (G x)
  let K := fun x=>coordinateHessianBilinear (H x)
  have hDc : ContinuousOn D S := (coordinateCovector (n:=n)).continuous.comp_continuousOn hG
  have hKc : ContinuousOn K S := (coordinateHessianBilinear (n:=n)).continuous.comp_continuousOn hH
  have hD (x : CoordinateSpace n) (hx : x∈interior S) : HasFDerivAt u (D x) x :=
    (hDu x (interior_subset hx)).hasFDerivAt (mem_interior_iff_mem_nhds.mp hx)
  have hK (x : CoordinateSpace n) (hx : x∈interior S) : HasFDerivAt D (K x) x :=
    (hasFDerivWithinAt_coordinateCovector_of_rows (fun k=>hDG k x (interior_subset hx))).hasFDerivAt
      (mem_interior_iff_mem_nhds.mp hx)
  obtain ⟨Cu,_,huh⟩ := exists_holder_bound_of_continuous_interior_field hS hSc hint hα.le hα1 hu hDc hD
  obtain ⟨CD,_,hDh⟩ := exists_holder_bound_of_continuous_interior_field hS hSc hint hα.le hα1 hDc hKc hK
  obtain ⟨CH,_,_,hKh⟩ := hHolder.map (coordinateHessianBilinear (n:=n))
  exact exists_jet_of_continuous_holder_interior_fields hS hSc hint u D K hu hDc hKc huh hDh
    (fun x hx y hy=>by simpa only [dist_eq_norm] using hKh x hx y hy) hD hK

/-- The concrete raw closed-half-ball constructor consumed by the true
physical boundary chart pullback. -/
theorem exists_halfBall_jet_of_closed_coordinate_fields
    (q : Fin n) {r α : ℝ} (hr : 0<r) (hα : 0<α) (hα1 : α≤1)
    (u : CoordinateSpace n→ℝ) (G : CoordinateSpace n → CoordinateSpace n)
    (H : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hu : ContinuousOn u (coordinateClosedHalfBall q r))
    (hG : ContinuousOn G (coordinateClosedHalfBall q r))
    (hH : ContinuousOn H (coordinateClosedHalfBall q r))
    (hDu : ∀ x∈coordinateClosedHalfBall q r,
      HasFDerivWithinAt u (coordinateCovector (G x)) (coordinateClosedHalfBall q r) x)
    (hDG : ∀ k x,x∈coordinateClosedHalfBall q r →
      HasFDerivWithinAt (fun y=>G y k) (coordinateCovector (H x k)) (coordinateClosedHalfBall q r) x)
    (hHolder : BoundedHolderOn α H (coordinateClosedHalfBall q r)) :
    ∃ j : Jet (CoordinateSpace n) ℝ (convex_coordinateClosedHalfBall q r) α,
      (∀ x : coordinateClosedHalfBall q r,
        value _ ℝ α (jetValue _ ℝ (convex_coordinateClosedHalfBall q r) α j) x=u x) ∧
      (∀ x : coordinateClosedHalfBall q r,
        value _ (CoordinateSpace n→L[ℝ]ℝ) α (jetFirst _ ℝ (convex_coordinateClosedHalfBall q r) α j) x=coordinateCovector (G x)) ∧
      (∀ x : coordinateClosedHalfBall q r,
        value _ (CoordinateSpace n→L[ℝ]CoordinateSpace n→L[ℝ]ℝ) α
          (jetSecond _ ℝ (convex_coordinateClosedHalfBall q r) α j) x=coordinateHessianBilinear (H x)) :=
  exists_jet_of_closed_coordinate_fields (convex_coordinateClosedHalfBall q r)
    (isCompact_coordinateClosedHalfBall q r) (interior_coordinateClosedHalfBall_nonempty q hr)
    hα hα1 u G H hu hG hH hDu hDG hHolder

end GaussianTilt.MomentMapLinearDirichlet
