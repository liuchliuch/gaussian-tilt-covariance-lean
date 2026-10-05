import GaussianTilt.MomentMapClassicalDirichletBoundaryWithinSlopes
import GaussianTilt.MomentMapClassicalDirichletGeometryCoordinates

/-! # Actual intrinsic Hölder-jet fields and their boundary identities -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 500000
open Set Filter Matrix
open scoped Topology ContDiff BigOperators
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin GaussianTilt.HolderSpace
variable {n : ℕ}

def intrinsicValue {S : Set (CoordinateSpace n)} (hS : Convex ℝ S) (α : ℝ)
    (j : Jet (CoordinateSpace n) ℝ hS α) : CoordinateSpace n → ℝ :=
  extendValue α (jetValue (CoordinateSpace n) ℝ hS α j)

def intrinsicFirst {S : Set (CoordinateSpace n)} (hS : Convex ℝ S) (α : ℝ)
    (j : Jet (CoordinateSpace n) ℝ hS α) : CoordinateSpace n → CoordinateSpace n →L[ℝ] ℝ :=
  extendValue α (jetFirst (CoordinateSpace n) ℝ hS α j)

def intrinsicSecond {S : Set (CoordinateSpace n)} (hS : Convex ℝ S) (α : ℝ)
    (j : Jet (CoordinateSpace n) ℝ hS α) : CoordinateSpace n → CoordinateSpace n →L[ℝ] CoordinateSpace n →L[ℝ] ℝ :=
  extendValue α (jetSecond (CoordinateSpace n) ℝ hS α j)

lemma intrinsicSecond_bilinear_eq_reverse_hessian
    {S : Set (CoordinateSpace n)} (hS : Convex ℝ S) (α : ℝ)
    (j : Jet (CoordinateSpace n) ℝ hS α) (x : S) (v z : CoordinateSpace n) :
    intrinsicSecond hS α j x v z = z ⬝ᵥ (hessianMatrix hS α j x *ᵥ v) := by
  rw [intrinsicSecond,extendValue_mem α _ x.2]
  have hv : (∑ i, v i • (Pi.single i 1 : CoordinateSpace n)) = v := by ext i; simp [Pi.single_apply]
  have hz : (∑ i, z i • (Pi.single i 1 : CoordinateSpace n)) = z := by ext i; simp [Pi.single_apply]
  conv_lhs => rw [← hv,← hz]
  simp only [map_sum,map_smul,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
    smul_eq_mul,Finset.mul_sum,dotProduct,Matrix.mulVec,holder_hessianMatrix_apply,
    hessianEntry,ContinuousLinearMap.comp_apply,ContinuousLinearMap.apply_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro l _
  ring

lemma intrinsicSecond_symmetric_on_body
    {S : Set (CoordinateSpace n)} (hS : Convex ℝ S) (hSc : IsClosed S)
    (hint : (interior S).Nonempty) {α : ℝ} (hα : 0 < α)
    (j : Jet (CoordinateSpace n) ℝ hS α) (x : S) (v z : CoordinateSpace n) :
    intrinsicSecond hS α j x v z = intrinsicSecond hS α j x z v := by
  rw [intrinsicSecond_bilinear_eq_reverse_hessian,intrinsicSecond_bilinear_eq_reverse_hessian,
    symmetric_dot_mulVec _ (holder_hessianMatrix_isSymm_on_body hS hSc hint hα j x),dotProduct_comm]

namespace SmoothInnerDomain
variable {S A : Set (E n)} (d : SmoothInnerDomain S A)

lemma coordinate_body_interior_nonempty : (interior {x | d.coordinateDefining x ≤ 0}).Nonempty := by
  rw [d.coordinate_body_interior,d.coordinate_domain_eq]
  exact (show d.domain.Nonempty from d.negative_nonempty).image (coordinateEquiv n)

/-- The actual first and full bilinear tangential second boundary jets of a
zero-boundary Hölder jet, with multiplier bounded by the scaled barriers. -/
theorem intrinsic_boundary_jet_data {α a b : ℝ} (hα : 0 < α)
    (j : zeroBoundary (CoordinateSpace n) ℝ d.coordinate_body_convex α)
    {x : CoordinateSpace n} (hx : x ∈ frontier {y | d.coordinateDefining y ≤ 0})
    (hbar : ∀ y ∈ {z | d.coordinateDefining z ≤ 0},
      b*d.coordinateDefining y ≤ intrinsicValue d.coordinate_body_convex α j.1 y ∧
      intrinsicValue d.coordinate_body_convex α j.1 y ≤ a*d.coordinateDefining y) :
    ∃ lam : ℝ, a ≤ lam ∧ lam ≤ b ∧
      intrinsicFirst d.coordinate_body_convex α j.1 x = lam • fderiv ℝ d.coordinateDefining x ∧
      ∀ v z : CoordinateSpace n, fderiv ℝ d.coordinateDefining x v = 0 →
        fderiv ℝ d.coordinateDefining x z = 0 →
        intrinsicSecond d.coordinate_body_convex α j.1 x v z =
          lam*fderiv ℝ (fderiv ℝ d.coordinateDefining) x v z := by
  have hxS := d.coordinate_body_compact.isClosed.frontier_subset hx
  have hx0 := d.coordinate_zero_boundary x hx
  let u := intrinsicValue d.coordinate_body_convex α j.1
  let D := intrinsicFirst d.coordinate_body_convex α j.1
  let H := intrinsicSecond d.coordinate_body_convex α j.1
  have hu (y : CoordinateSpace n) (hy : d.coordinateDefining y ≤ 0) :
      HasFDerivWithinAt u (D y) {z | d.coordinateDefining z ≤ 0} y :=
    jet_hasFDerivWithinAt d.coordinate_body_convex hα j.1 hy
  have hD : HasFDerivWithinAt D (H x) {z | d.coordinateDefining z ≤ 0} x :=
    jet_first_hasFDerivWithinAt d.coordinate_body_convex hα j.1 hxS
  have hw : ContDiffAt ℝ 2 d.coordinateDefining x := (contDiff_infty.mp d.coordinateDefining_smooth 2).contDiffAt
  obtain ⟨k,hk⟩ := d.coordinate_transverse_index hx0
  let e := (coordinateDerivative k d.coordinateDefining x)⁻¹ • (Pi.single k 1 : CoordinateSpace n)
  have he : fderiv ℝ d.coordinateDefining x e = 1 := by
    simp only [e,map_smul,smul_eq_mul]
    exact inv_mul_cancel₀ hk
  have huzero (y : CoordinateSpace n) (hy : d.coordinateDefining y = 0) : u y = 0 := by
    apply zeroBoundary_value d.coordinate_body_convex d.coordinate_body_compact.isClosed α j
    rwa [d.coordinate_body_frontier]
  have hlevelS : ∀ᶠ y in 𝓝 x, d.coordinateDefining y = d.coordinateDefining x → d.coordinateDefining y ≤ 0 :=
    Eventually.of_forall (fun y hy => (hy.trans hx0).le)
  have hlevelU : ∀ᶠ y in 𝓝 x, d.coordinateDefining y = d.coordinateDefining x → u y = u x :=
    Eventually.of_forall (fun y hy => (huzero y (hy.trans hx0)).trans (huzero x hx0).symm)
  have hmul := within_normal_multiplier_bounds_of_barriers (hu x hxS) (hw.differentiableAt (by norm_num))
    he (huzero x hx0) hx0 (Eventually.of_forall (fun y hy => hy.le))
    (Eventually.of_forall (fun y hy => hbar y hy.le))
  refine ⟨D x e,hmul.1,hmul.2,firstJet_eq_smul_of_level_constant (hu x hxS) hw he hlevelS hlevelU,?_⟩
  intro v z hv hz
  exact secondJet_tangent_bilinear_eq_of_level_constant hu hD hxS hw he hv hz
    (intrinsicSecond_symmetric_on_body d.coordinate_body_convex d.coordinate_body_compact.isClosed
      d.coordinate_body_interior_nonempty hα j.1 ⟨x,hxS⟩) hlevelS hlevelU

end SmoothInnerDomain
end GaussianTilt.MomentMapRegularity
