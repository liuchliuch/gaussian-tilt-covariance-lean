import GaussianTilt.MomentMapClassicalDirichletIntrinsicInterior
import Mathlib.Analysis.Convex.Deriv

/-! # Convexity of genuine positive-semidefinite intrinsic jets -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 500000
open Set Filter Matrix
open scoped Topology ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin GaussianTilt.HolderSpace

/-- The actual within-domain second field suffices for convexity, even
when a segment is contained in the boundary of the domain. -/
theorem convexOn_of_within_second_fields
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} (hS : Convex ℝ S) {u : E → ℝ} {D : E → E →L[ℝ] ℝ}
    {H : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hu : ∀ x ∈ S, HasFDerivWithinAt u (D x) S x)
    (hD : ∀ x ∈ S, HasFDerivWithinAt D (H x) S x)
    (hpos : ∀ x ∈ S, ∀ v, 0 ≤ H x v v) : ConvexOn ℝ S u := by
  refine ⟨hS,?_⟩
  intro x hx y hy a b ha hb hab
  let γ : ℝ → E := AffineMap.lineMap x y
  let f : ℝ → ℝ := u ∘ γ
  let f₁ : ℝ → ℝ := fun t => D (γ t) (y-x)
  let f₂ : ℝ → ℝ := fun t => H (γ t) (y-x) (y-x)
  have hmaps : MapsTo γ (Icc (0:ℝ) 1) S := hS.mapsTo_lineMap hx hy
  have hfirst (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      HasDerivWithinAt f (f₁ t) (Icc (0:ℝ) 1) t :=
    (hu _ (hmaps ht)).comp_hasDerivWithinAt t AffineMap.hasDerivWithinAt_lineMap hmaps
  have hsecond (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      HasDerivWithinAt f₁ (f₂ t) (Icc (0:ℝ) 1) t := by
    let L : (E →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ (y-x)
    have hd := L.hasFDerivAt.comp_hasFDerivWithinAt (γ t) (hD _ (hmaps ht))
    exact hd.comp_hasDerivWithinAt t AffineMap.hasDerivWithinAt_lineMap hmaps
  have hfc : ConvexOn ℝ (Icc (0:ℝ) 1) f :=
    convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
      (fun t ht => (hfirst t ht).continuousWithinAt)
      (fun t ht => (hfirst t (interior_subset ht)).mono interior_subset)
      (fun t ht => (hsecond t (interior_subset ht)).mono interior_subset)
      (fun t ht => hpos _ (hmaps (interior_subset ht)) _)
  have hh := hfc.2 (show (0:ℝ) ∈ Icc 0 1 by simp) (show (1:ℝ) ∈ Icc 0 1 by simp) ha hb hab
  have hae : a = 1-b := by linarith
  simpa [f,γ,AffineMap.lineMap_apply_module,hae] using hh

variable {n : ℕ}

/-- Positive semidefiniteness of the stored Hessian gives actual convexity
of the represented function on its entire convex domain. -/
theorem intrinsicValue_convexOn_of_posSemidef
    {S : Set (CoordinateSpace n)} (hS : Convex ℝ S) {α : ℝ} (hα : 0 < α)
    (j : Jet (CoordinateSpace n) ℝ hS α)
    (hp : ∀ x ∈ S, (intrinsicHessian hS α j x).PosSemidef) :
    ConvexOn ℝ S (intrinsicValue hS α j) := by
  apply convexOn_of_within_second_fields hS
    (fun x hx => jet_hasFDerivWithinAt hS hα j hx)
    (fun x hx => jet_first_hasFDerivWithinAt hS hα j hx)
  intro x hx v
  change 0 ≤ intrinsicSecond hS α j x v v
  rw [intrinsicSecond_bilinear_eq_reverse_hessian hS α j ⟨x,hx⟩ v v,
    ← intrinsicHessian_eq_stored hS α j ⟨x,hx⟩]
  exact (hp x hx).2 v

/-- The representative already used by the Banach construction is the
continuous zero extension of a genuine zero-boundary jet. -/
theorem continuous_intrinsicValue_zeroBoundary
    {S : Set (CoordinateSpace n)} (hS : Convex ℝ S) (hSc : IsClosed S) (α : ℝ)
    (j : zeroBoundary (CoordinateSpace n) ℝ hS α) : Continuous (intrinsicValue hS α j.1) := by
  have hb (x : CoordinateSpace n) (hx : x ∈ frontier S) : intrinsicValue hS α j.1 x = 0 := by
    exact zeroBoundary_value hS hSc α j hx
  have he : S.indicator (intrinsicValue hS α j.1) = intrinsicValue hS α j.1 := by
    ext x
    by_cases hx : x ∈ S
    · simp only [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx,intrinsicValue,extendValue,hx]
  rw [← he]
  apply continuous_indicator hb
  rw [hSc.closure_eq]
  exact continuousOn_extendValue α _

end GaussianTilt.MomentMapRegularity
