import GaussianTilt.MomentMapClassicalDirichletGeometryHessian
import GaussianTilt.MomentMapCoordinateTransport

/-! # Actual raw-coordinate defining-domain geometry -/
noncomputable section
open Set Filter Matrix
open scoped Topology ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

lemma secondFDeriv_coordinatePullback {f : E n → ℝ} (hf : ContDiff ℝ 2 f)
    (x v : CoordinateSpace n) :
    fderiv ℝ (fderiv ℝ (coordinatePullback f)) x v v =
      fderiv ℝ (fderiv ℝ f) ((coordinateEquiv n).symm x)
        ((coordinateEquiv n).symm v) ((coordinateEquiv n).symm v) := by
  have hraw := contDiff_coordinatePullback hf
  have h1 := second_deriv_affine_line_comp hraw x v 0
  have h2 := second_deriv_affine_line_comp hf ((coordinateEquiv n).symm x)
    ((coordinateEquiv n).symm v) 0
  have heq : (fun t : ℝ => coordinatePullback f (x+t • v)) =
      (fun t : ℝ => f ((coordinateEquiv n).symm x+t • (coordinateEquiv n).symm v)) := by
    funext t
    simp only [coordinatePullback, Function.comp_apply, map_add, map_smul]
  rw [heq] at h1
  simp only [zero_smul, add_zero] at h1 h2
  exact h1.symm.trans h2

namespace SmoothInnerDomain
variable {S A : Set (E n)} (d : SmoothInnerDomain S A)

def coordinateDefining : CoordinateSpace n → ℝ := coordinatePullback d.defining

lemma coordinateDefining_smooth : ContDiff ℝ ∞ d.coordinateDefining :=
  contDiff_coordinatePullback d.smooth

/-- Strict positive definiteness of the actual coordinate Hessian is
transported from the proven differential lower bound. -/
lemma coordinateDefining_hessian_posDef (x : CoordinateSpace n) :
    (coordinateHessian d.coordinateDefining x).PosDef := by
  have hf := contDiff_infty.mp d.coordinateDefining_smooth 2
  constructor
  · simpa only [Matrix.IsSymm, Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using
      coordinateHessian_isSymm_at hf.contDiffAt
  · intro v hv
    change 0 < star v ⬝ᵥ (coordinateHessian d.coordinateDefining x).mulVec v
    simp only [star_trivial]
    change 0 < matrixQuadratic (coordinateHessian d.coordinateDefining x) v
    rw [← secondFDeriv_eq_hessianQuadratic hf.contDiffAt]
    change 0 < fderiv ℝ (fderiv ℝ (coordinatePullback d.defining)) x v v
    rw [secondFDeriv_coordinatePullback (contDiff_infty.mp d.smooth 2)]
    exact d.hessian_positive _ (fun hz => hv ((coordinateEquiv n).symm.injective (by simpa using hz)))

lemma coordinate_body_eq : {x | d.coordinateDefining x ≤ 0} = (coordinateEquiv n) '' d.body := by
  ext x
  constructor
  · intro hx
    exact ⟨(coordinateEquiv n).symm x, hx, (coordinateEquiv n).apply_symm_apply x⟩
  · rintro ⟨y,hy,rfl⟩
    simpa [coordinateDefining, coordinatePullback] using hy

lemma coordinate_domain_eq : {x | d.coordinateDefining x < 0} = (coordinateEquiv n) '' d.domain := by
  ext x
  constructor
  · intro hx
    exact ⟨(coordinateEquiv n).symm x, hx, (coordinateEquiv n).apply_symm_apply x⟩
  · rintro ⟨y,hy,rfl⟩
    simpa [coordinateDefining, coordinatePullback] using hy

lemma coordinate_body_compact : IsCompact {x | d.coordinateDefining x ≤ 0} := by
  rw [d.coordinate_body_eq]
  exact d.compact_sublevel.image (coordinateEquiv n).continuous

lemma coordinate_body_convex : Convex ℝ {x | d.coordinateDefining x ≤ 0} := by
  rw [d.coordinate_body_eq]
  exact d.convex_body.linear_image (coordinateEquiv n).toLinearMap

lemma coordinate_body_interior : interior {x | d.coordinateDefining x ≤ 0} =
    {x | d.coordinateDefining x < 0} := by
  rw [d.coordinate_body_eq, d.coordinate_domain_eq]
  have hh := (coordinateEquiv n).toHomeomorph.image_interior d.body
  change (coordinateEquiv n) '' interior d.body = interior ((coordinateEquiv n) '' d.body) at hh
  rw [← hh, d.interior_body]

lemma coordinate_body_frontier : frontier {x | d.coordinateDefining x ≤ 0} =
    {x | d.coordinateDefining x = 0} := by
  rw [frontier, d.coordinate_body_compact.isClosed.closure_eq, d.coordinate_body_interior]
  ext x
  simp only [mem_diff, mem_setOf_eq, not_lt]
  exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le,h.ge⟩⟩

lemma coordinate_zero_boundary : ∀ x ∈ frontier {x | d.coordinateDefining x ≤ 0},
    d.coordinateDefining x = 0 := by
  intro x hx
  rwa [d.coordinate_body_frontier] at hx

lemma coordinate_body_nonempty : ({x | d.coordinateDefining x ≤ 0} : Set (CoordinateSpace n)).Nonempty := by
  obtain ⟨x,hx⟩ := d.negative_nonempty
  refine ⟨coordinateEquiv n x, ?_⟩
  simpa [coordinateDefining, coordinatePullback] using hx.le

lemma coordinate_contains : (coordinateEquiv n) '' A ⊆ {x | d.coordinateDefining x < 0} := by
  rw [d.coordinate_domain_eq]
  exact image_mono d.contains

lemma coordinate_body_inside : {x | d.coordinateDefining x ≤ 0} ⊆
    interior ((coordinateEquiv n) '' S) := by
  rw [d.coordinate_body_eq]
  have hh := (coordinateEquiv n).toHomeomorph.image_interior S
  change (coordinateEquiv n) '' interior S = interior ((coordinateEquiv n) '' S) at hh
  rw [← hh]
  exact image_mono d.sublevel_inside

lemma coordinate_gradient_ne_zero {x : CoordinateSpace n} (hx : d.coordinateDefining x = 0) :
    coordinateGradient d.coordinateDefining x ≠ 0 := by
  have horig := d.regular_level ((coordinateEquiv n).symm x) hx
  change coordinateGradient (coordinatePullback d.defining) x ≠ 0
  rw [coordinateGradient_pullback ((contDiff_infty.mp d.smooth 1).differentiable le_rfl)]
  exact fun h => horig ((coordinateEquiv n).injective (by simpa using h))

lemma coordinate_transverse_index {x : CoordinateSpace n} (hx : d.coordinateDefining x = 0) :
    ∃ j : Fin n, coordinateDerivative j d.coordinateDefining x ≠ 0 := by
  by_contra! hz
  apply d.coordinate_gradient_ne_zero hx
  exact funext hz

end SmoothInnerDomain
end GaussianTilt.MomentMapRegularity
