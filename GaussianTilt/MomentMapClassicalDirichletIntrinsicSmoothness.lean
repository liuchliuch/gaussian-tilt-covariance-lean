import GaussianTilt.MomentMapClassicalDirichletIntrinsicConvexity
import GaussianTilt.MomentMapSchauderCoordinateDensity

/-! # Actual interior smoothness of positive intrinsic continuation jets -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 500000
open Set Filter Matrix
open scoped Topology ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin GaussianTilt.HolderSpace GaussianTilt.MomentMapSchauder
variable {n : ℕ}

lemma intrinsicHessian_entry_holder
    {S : Set (CoordinateSpace n)} (hS : Convex ℝ S) (α : ℝ)
    (j : Jet (CoordinateSpace n) ℝ hS α) {x y : CoordinateSpace n} (hx : x ∈ S) (hy : y ∈ S)
    (i l : Fin n) :
    |intrinsicHessian hS α j x i l-intrinsicHessian hS α j y i l| ≤
      ‖jetSecond (CoordinateSpace n) ℝ hS α j‖*‖x-y‖^α := by
  have hh := norm_value_sub_le S (CoordinateSpace n →L[ℝ] CoordinateSpace n →L[ℝ] ℝ) α
    (jetSecond (CoordinateSpace n) ℝ hS α j) ⟨x,hx⟩ ⟨y,hy⟩
  have hL : |intrinsicHessian hS α j x i l-intrinsicHessian hS α j y i l| ≤
      ‖intrinsicSecond hS α j x-intrinsicSecond hS α j y‖ := by
    have h1 := ((intrinsicSecond hS α j x-intrinsicSecond hS α j y) (Pi.single l 1)).le_opNorm (Pi.single i 1)
    have h2 := (intrinsicSecond hS α j x-intrinsicSecond hS α j y).le_opNorm (Pi.single l 1)
    simp only [Pi.norm_single,norm_one,mul_one] at h1 h2
    simpa only [intrinsicHessian,ContinuousLinearMap.sub_apply,Real.norm_eq_abs] using h1.trans h2
  apply hL.trans
  simpa only [intrinsicSecond,extendValue_mem α _ hx,extendValue_mem α _ hy,
    Subtype.dist_eq,dist_eq_norm] using hh

/-- Interior smoothness follows from the true C²,α jet, actual positive
Hessian, and spatially smooth positive density. It is not a premise of
the classical a priori chain. -/
theorem intrinsicValue_contDiffOn_infty_of_positive_density [NeZero n]
    {S : Set (CoordinateSpace n)} (hS : Convex ℝ S) {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (j : Jet (CoordinateSpace n) ℝ hS α) {ρ : CoordinateSpace n → ℝ}
    (hρ : ContDiffOn ℝ ∞ ρ (interior S)) (hρpos : ∀ x ∈ interior S, 0 < ρ x)
    (hp : ∀ x ∈ interior S, (intrinsicHessian hS α j x).PosDef)
    (hMA : ∀ x ∈ interior S, (intrinsicHessian hS α j x).det = ρ x) :
    ContDiffOn ℝ ∞ (intrinsicValue hS α j) (interior S) := by
  apply coordinate_positive_density_contDiffOn_infty_of_holder_entries isOpen_interior
    (jet_contDiffOn_two hS hα j) hρ hρpos hα hα1
    (norm_nonneg (jetSecond (CoordinateSpace n) ℝ hS α j))
  · intro x hx
    have hh := hp x hx
    rw [intrinsicHessian_eq_actual hS hα j hx] at hh
    exact hh
  · intro x hx
    have hh := hMA x hx
    rw [intrinsicHessian_eq_actual hS hα j hx] at hh
    exact hh
  · intro x hx y hy i l
    have hh := intrinsicHessian_entry_holder hS α j (interior_subset hx) (interior_subset hy) i l
    rw [intrinsicHessian_eq_actual hS hα j hx,intrinsicHessian_eq_actual hS hα j hy] at hh
    exact hh

namespace SmoothInnerDomain
variable {S A : Set (E n)} (d : SmoothInnerDomain S A)

/-- Every positive solution jet of the actual forcing homotopy is
interior C∞, including the nonconstant intermediate densities. -/
theorem intrinsic_dirichletContinuation_interior_smooth [NeZero n]
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (j : zeroBoundary (CoordinateSpace n) ℝ d.coordinate_body_convex α)
    (hp : ∀ y ∈ {z | d.coordinateDefining z ≤ 0}, (intrinsicHessian d.coordinate_body_convex α j.1 y).PosDef)
    (hMA : ∀ y ∈ {z | d.coordinateDefining z ≤ 0},
      (intrinsicHessian d.coordinate_body_convex α j.1 y).det = dirichletContinuationDensity d.coordinateDefining t y) :
    ContDiffOn ℝ ∞ (intrinsicValue d.coordinate_body_convex α j.1) (interior {y | d.coordinateDefining y ≤ 0}) := by
  apply intrinsicValue_contDiffOn_infty_of_positive_density d.coordinate_body_convex hα hα1 j.1
    (ρ := dirichletContinuationDensity d.coordinateDefining t)
  · exact ((contDiff_dirichletContinuationDensity d.coordinateDefining_smooth).comp
      (contDiff_const.prodMk contDiff_id)).contDiffOn
  · intro x hx
    exact dirichletContinuationDensity_pos ht (d.coordinateDefining_hessian_posDef x)
  · exact fun x hx => hp x (interior_subset hx)
  · exact fun x hx => hMA x (interior_subset hx)

end SmoothInnerDomain
end GaussianTilt.MomentMapRegularity
