import GaussianTilt.MomentMapClassicalDirichletIntrinsicFlatSystem
import GaussianTilt.MomentMapClassicalDirichletIntrinsicLipschitz

/-! # Genuine lower-order chart and density moduli for Hessian recovery -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 500000
open Set Filter Matrix
open scoped Topology ContDiff BigOperators NNReal
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin GaussianTilt.HolderSpace
variable {n : ℕ}

namespace BoundaryChartPatch
variable {w : CoordinateSpace n → ℝ} (p : BoundaryChartPatch w)

lemma coefficient_rep_lipschitz (a : Fin n) {β : CoordinateSpace n → ℝ}
    (hβ : ContDiff ℝ ∞ β)
    (he : ∀ x ∈ Metric.closedBall p.center p.radius, β =ᶠ[𝓝 x] boundaryChartCoefficient w p.index a) :
    LipschitzOnWith ⟨(n:ℝ)*p.bound₁,mul_nonneg (Nat.cast_nonneg _) p.bound₁_nonneg⟩ β
      (Metric.closedBall p.center p.radius) := by
  apply (convex_closedBall p.center p.radius).lipschitzOnWith_of_nnnorm_fderiv_le
    (fun x _ => hβ.differentiable (by simp) x)
  intro x hx
  apply norm_fderiv_le_of_coordinate_bound p.bound₁_nonneg
  intro k
  rw [coordinateDerivative_congr_nhds (he x hx)]
  exact p.derivative_bound x hx a k

lemma derivative_rep_lipschitz (a k : Fin n) {β : CoordinateSpace n → ℝ}
    (hβ : ContDiff ℝ ∞ β)
    (he : ∀ x ∈ Metric.closedBall p.center p.radius, β =ᶠ[𝓝 x] boundaryChartCoefficient w p.index a) :
    LipschitzOnWith ⟨(n:ℝ)*p.bound₂,mul_nonneg (Nat.cast_nonneg _) p.bound₂_nonneg⟩ (coordinateDerivative k β)
      (Metric.closedBall p.center p.radius) := by
  apply (convex_closedBall p.center p.radius).lipschitzOnWith_of_nnnorm_fderiv_le
    (fun x _ => (smooth_coordinateDerivative hβ k).differentiable (by simp) x)
  intro x hx
  apply norm_fderiv_le_of_coordinate_bound p.bound₂_nonneg
  intro l
  change |coordinateHessian β x k l| ≤ p.bound₂
  rw [coordinateHessian_congr_nhds (he x hx)]
  exact p.hessian_bound x hx a k l

end BoundaryChartPatch

lemma dirichletContinuationDensity_uniform_lipschitz
    {S : Set (CoordinateSpace n)} (hS : IsCompact S) (hc : Convex ℝ S)
    {w : CoordinateSpace n → ℝ} (hw : ContDiff ℝ ∞ w) :
    ∃ J : ℝ≥0, ∀ t ∈ Icc (0:ℝ) 1, LipschitzOnWith J (dirichletContinuationDensity w t) S := by
  let g := fun x => (coordinateHessian w x).det
  have hg : ContDiff ℝ ∞ g := contDiff_matrix_det (smooth_coordinateHessian hw)
  obtain ⟨C,hC⟩ := hS.exists_bound_of_continuousOn (hg.continuous_fderiv (by simp)).continuousOn
  let J : ℝ≥0 := ⟨max C 0,le_max_right _ _⟩
  have hgl : LipschitzOnWith J g S := by
    apply hc.lipschitzOnWith_of_nnnorm_fderiv_le (fun x _ => hg.differentiable (by simp) x)
    intro x hx
    exact (hC x hx).trans (le_max_left _ _)
  refine ⟨J,?_⟩
  intro t ht
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  change |dirichletContinuationDensity w t x-dirichletContinuationDensity w t y| ≤ (J:ℝ)*dist x y
  have he : dirichletContinuationDensity w t x-dirichletContinuationDensity w t y = (1-t)*(g x-g y) := by
    unfold dirichletContinuationDensity g
    ring
  rw [he,abs_mul,abs_of_nonneg (sub_nonneg.mpr ht.2)]
  exact (mul_le_mul_of_nonneg_right (show 1-t ≤ 1 by linarith [ht.1]) (abs_nonneg _)).trans
    (by simpa only [one_mul,Real.dist_eq] using hgl.dist_le_mul x hx y hy)

lemma lipschitzOn_euclidean_holder_small
    {S : Set (CoordinateSpace n)} {f : CoordinateSpace n → ℝ} {J : ℝ≥0}
    (hJ : LipschitzOnWith J f S) {α : ℝ} (hα1 : α ≤ 1)
    {x y : CoordinateSpace n} (hx : x ∈ S) (hy : y ∈ S)
    (hd : ‖(coordinateEquiv n).symm x-(coordinateEquiv n).symm y‖ ≤ 1) :
    |f x-f y| ≤ (J:ℝ)*‖(coordinateEquiv n).symm x-(coordinateEquiv n).symm y‖^α := by
  have h := hJ.dist_le_mul x hx y hy
  change |f x-f y| ≤ (J:ℝ)*dist x y at h
  exact h.trans (mul_le_mul_of_nonneg_left
    ((coordinate_dist_le_euclidean_dist x y).trans (Real.self_le_rpow_of_le_one (norm_nonneg _) hd hα1)) J.coe_nonneg)

end GaussianTilt.MomentMapRegularity
