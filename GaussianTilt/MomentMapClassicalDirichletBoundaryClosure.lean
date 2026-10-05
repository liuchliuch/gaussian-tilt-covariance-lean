import GaussianTilt.MomentMapClassicalDirichletContinuationFirstOrder

/-! # Actual extension of the classical equation and convexity to the boundary -/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}
namespace SmoothInnerDomain
variable {S A : Set (E n)} (d : SmoothInnerDomain S A)

lemma coordinate_body_closure_interior :
    closure (interior {x | d.coordinateDefining x ≤ 0}) = {x | d.coordinateDefining x ≤ 0} := by
  rw [d.coordinate_body_interior,d.coordinate_domain_eq,d.coordinate_body_eq]
  have h := (coordinateEquiv n).toHomeomorph.image_closure d.domain
  change (coordinateEquiv n) '' closure d.domain = closure ((coordinateEquiv n) '' d.domain) at h
  rw [← h,d.closure_domain]

/-- Continuity extends the literal determinant equation to the full body. -/
lemma coordinate_equation_on_body {u : CoordinateSpace n → ℝ} (hu : ContDiff ℝ ∞ u)
    {t : ℝ}
    (hMA : ∀ x ∈ interior {y | d.coordinateDefining y ≤ 0},
      (coordinateHessian u x).det = dirichletContinuationDensity d.coordinateDefining t x) :
    ∀ x ∈ {y | d.coordinateDefining y ≤ 0},
      (coordinateHessian u x).det = dirichletContinuationDensity d.coordinateDefining t x := by
  have hcu : Continuous (fun x => (coordinateHessian u x).det) :=
    (contDiff_matrix_det (smooth_coordinateHessian hu)).continuous
  have hcw : Continuous (dirichletContinuationDensity d.coordinateDefining t) :=
    ((contDiff_dirichletContinuationDensity d.coordinateDefining_smooth).continuous.comp
      (continuous_const.prodMk continuous_id))
  have hcl : closure (interior {y | d.coordinateDefining y ≤ 0}) ⊆
      {x | (coordinateHessian u x).det = dirichletContinuationDensity d.coordinateDefining t x} :=
    closure_minimal hMA (isClosed_eq hcu hcw)
  rwa [d.coordinate_body_closure_interior] at hcl

/-- Positive interior Hessians have genuinely positive semidefinite boundary
limits. This derives boundary convexity instead of assuming it. -/
lemma coordinate_hessian_posSemidef_on_body {u : CoordinateSpace n → ℝ} (hu : ContDiff ℝ ∞ u)
    (hH : ∀ x ∈ interior {y | d.coordinateDefining y ≤ 0}, (coordinateHessian u x).PosDef) :
    ∀ x ∈ {y | d.coordinateDefining y ≤ 0}, (coordinateHessian u x).PosSemidef := by
  intro x hx
  refine ⟨?_, fun v => ?_⟩
  · simpa only [Matrix.IsHermitian,Matrix.IsSymm,Matrix.conjTranspose_eq_transpose_of_trivial] using
      coordinateHessian_isSymm_at (contDiff_infty.mp hu 2).contDiffAt
  · have hq : Continuous (fun y => v ⬝ᵥ (coordinateHessian u y *ᵥ v)) := by
      unfold dotProduct Matrix.mulVec
      apply continuous_finset_sum
      intro i _
      apply continuous_const.mul
      apply continuous_finset_sum
      intro j _
      exact ((smooth_coordinateHessian hu i j).continuous.mul continuous_const)
    have h := le_on_closure (fun y hy => (hH y hy).posSemidef.2 v)
      continuousOn_const hq.continuousOn
      (show x ∈ closure (interior {y | d.coordinateDefining y ≤ 0}) by
        rwa [d.coordinate_body_closure_interior])
    simpa only [star_trivial] using h

end SmoothInnerDomain
end GaussianTilt.MomentMapRegularity
