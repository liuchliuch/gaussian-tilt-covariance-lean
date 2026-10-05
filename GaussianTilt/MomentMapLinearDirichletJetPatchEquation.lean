import GaussianTilt.MomentMapLinearDirichletJetPatchEmbedding
import GaussianTilt.MomentMapHolderCofactorOperator
import GaussianTilt.MomentMapCalabiAffine

/-! # The glued jet satisfies the actual closed-domain elliptic equation

The interior equation is transferred through the literal value equality.
Continuity and full-dimensional convex-body density then give equality in
the Hölder codomain, including the boundary.
-/
noncomputable section
set_option maxHeartbeats 2000000
open Set Filter Matrix
open scoped Topology BoundedContinuousFunction
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.HolderSpace GaussianTilt.MomentMapRegularity GaussianTilt.Letwin
variable {n : ℕ}

/-- Pointwise interior PDE data for the actual value representative imply
equality under the genuine Banach-space elliptic operator. -/
theorem elliptic_jet_eq_of_actual_interior_equation
    {S : Set (CoordinateSpace n)} (hS : Convex ℝ S) (hSc : IsClosed S)
    (hint : (interior S).Nonempty) {α : ℝ} (hα : 0 < α)
    (A : Fin n → Fin n → Space S ℝ α) (f : Space S ℝ α)
    (J : zeroBoundary (CoordinateSpace n) ℝ hS α) (u : CoordinateSpace n → ℝ)
    (hvalue : ∀ x : S, value S ℝ α (jetValue (CoordinateSpace n) ℝ hS α J.1) x=u x)
    (heq : ∀ x : S, (x : CoordinateSpace n) ∈ interior S →
      linearizedMA (show Matrix (Fin n) (Fin n) ℝ from fun i k => value S ℝ α (A i k) x) u x =
        value S ℝ α f x) :
    ellipticDirichletOperator hS α A J=f := by
  let out := ellipticDirichletOperator hS α A J
  have he : EqOn (extendValue α out) (extendValue α f) S := by
    have hclosed := closed_patch_eq_of_interior_eq hS hSc hint isOpen_univ
      ((continuousOn_extendValue α out).mono inter_subset_left)
      ((continuousOn_extendValue α f).mono inter_subset_left)
    have hi : EqOn (extendValue α out) (extendValue α f) (interior S ∩ univ) := by
      intro x hx
      have hxs : x ∈ S := interior_subset hx.1
      have hv : extendValue α (jetValue (CoordinateSpace n) ℝ hS α J.1) =ᶠ[𝓝 x] u := by
        filter_upwards [isOpen_interior.mem_nhds hx.1] with y hy
        rw [extendValue_mem α _ (interior_subset hy)]
        exact hvalue ⟨y,interior_subset hy⟩
      rw [extendValue_mem α _ hxs,extendValue_mem α _ hxs]
      change value S ℝ α (ellipticDirichletOperator hS α A J) ⟨x,hxs⟩ = _
      rw [ellipticDirichletOperator_eq_actual hS hα A J ⟨x,hxs⟩ hx.1]
      rw [linearizedMA,coordinateHessian_congr_nhds hv]
      exact heq ⟨x,hxs⟩ hx.1
    simpa only [inter_univ] using hclosed hi
  apply value_injective S ℝ α
  apply BoundedContinuousFunction.ext
  intro x
  have hh := he x.2
  simpa only [extendValue_mem α _ x.2] using hh

/-- The sign convention is the positive Laplacian. In particular weak
Poisson solutions for the negative datum feed this theorem directly. -/
theorem laplace_jet_eq_of_actual_interior_equation
    {S : Set (CoordinateSpace n)} (hS : Convex ℝ S) (hSc : IsClosed S)
    (hint : (interior S).Nonempty) {α : ℝ} (hα : 0 < α)
    (f : Space S ℝ α) (J : zeroBoundary (CoordinateSpace n) ℝ hS α)
    (u : CoordinateSpace n → ℝ)
    (hvalue : ∀ x : S, value S ℝ α (jetValue (CoordinateSpace n) ℝ hS α J.1) x=u x)
    (heq : ∀ x : S, (x : CoordinateSpace n) ∈ interior S →
      Matrix.trace (coordinateHessian u x)=value S ℝ α f x) :
    ellipticDirichletOperator hS α (identityFields S α) J=f := by
  apply elliptic_jet_eq_of_actual_interior_equation hS hSc hint hα _ f J u hvalue
  intro x hx
  simpa only [value_identityFields,linearizedMA,Matrix.one_mul] using heq x hx

end GaussianTilt.MomentMapLinearDirichlet
