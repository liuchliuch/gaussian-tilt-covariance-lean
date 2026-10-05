import GaussianTilt.MomentMapClassicalDirichletBoundaryBounds
import GaussianTilt.MomentMapClassicalDirichletGeometryCoordinates
import GaussianTilt.MomentMapRegularityConstantDensityCalculus

/-! # Actual boundary chart coefficients and uniform derivative bounds -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

def boundaryChartCoefficient (w : CoordinateSpace n → ℝ) (j a : Fin n)
    (x : CoordinateSpace n) : ℝ := coordinateDerivative a w x / coordinateDerivative j w x

lemma contDiffAt_boundaryChartCoefficient {w : CoordinateSpace n → ℝ}
    (hw : ContDiff ℝ ∞ w) {j : Fin n} {x : CoordinateSpace n}
    (hj : coordinateDerivative j w x ≠ 0) (a : Fin n) :
    ContDiffAt ℝ ∞ (boundaryChartCoefficient w j a) x := by
  exact (contDiffAt_coordinateDerivative hw.contDiffAt (m:=∞) (by simp) a).div
    (contDiffAt_coordinateDerivative hw.contDiffAt (m:=∞) (by simp) j) hj

/-- The denominator stays quantitatively away from zero on a genuine
compact patch, and all actual chart derivatives through order two are
uniformly bounded there. -/
theorem exists_boundary_chart_bounds {w : CoordinateSpace n → ℝ}
    (hw : ContDiff ℝ ∞ w) {x : CoordinateSpace n} {j : Fin n}
    (hj : coordinateDerivative j w x ≠ 0) :
    ∃ r c M₀ M₁ M₂ : ℝ, 0 < r ∧ 0 < c ∧ 0 ≤ M₀ ∧ 0 ≤ M₁ ∧ 0 ≤ M₂ ∧
      (∀ y ∈ Metric.closedBall x r, c ≤ |coordinateDerivative j w y|) ∧
      (∀ y ∈ Metric.closedBall x r, ∀ a, ContDiffAt ℝ ∞ (boundaryChartCoefficient w j a) y) ∧
      (∀ y ∈ Metric.closedBall x r, ∀ a, |boundaryChartCoefficient w j a y| ≤ M₀) ∧
      (∀ y ∈ Metric.closedBall x r, ∀ a i, |coordinateDerivative i (boundaryChartCoefficient w j a) y| ≤ M₁) ∧
      (∀ y ∈ Metric.closedBall x r, ∀ a i l, |coordinateHessian (boundaryChartCoefficient w j a) y i l| ≤ M₂) := by
  let c := |coordinateDerivative j w x|/2
  have hc : 0 < c := half_pos (abs_pos.mpr hj)
  have hdj : Continuous (coordinateDerivative j w) :=
    (contDiff_coordinateDerivative hw (m:=0) (by simp) j).continuous
  have hneighborhood : {y | c < |coordinateDerivative j w y|} ∈ 𝓝 x :=
    (isOpen_lt continuous_const hdj.abs).mem_nhds (by dsimp [c]; exact half_lt_self (abs_pos.mpr hj))
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hneighborhood
  let r := δ/2
  have hr : 0 < r := half_pos hδ
  have hpatch (y : CoordinateSpace n) (hy : y ∈ Metric.closedBall x r) :
      c < |coordinateDerivative j w y| := hball (lt_of_le_of_lt hy (half_lt_self hδ))
  have hjp (y : CoordinateSpace n) (hy : y ∈ Metric.closedBall x r) :
      coordinateDerivative j w y ≠ 0 := abs_pos.mp (hc.trans (hpatch y hy))
  have hsmooth (y : CoordinateSpace n) (hy : y ∈ Metric.closedBall x r) (a : Fin n) :=
    contDiffAt_boundaryChartCoefficient hw (hjp y hy) a
  have hc0 : ContinuousOn (fun y => fun a => boundaryChartCoefficient w j a y)
      (Metric.closedBall x r) := continuousOn_pi.mpr (fun a y hy =>
    (hsmooth y hy a).continuousAt.continuousWithinAt)
  have hc1 : ContinuousOn (fun y => fun a i => coordinateDerivative i (boundaryChartCoefficient w j a) y)
      (Metric.closedBall x r) := continuousOn_pi.mpr (fun a => continuousOn_pi.mpr (fun i y hy =>
    (contDiffAt_coordinateDerivative (hsmooth y hy a) (m:=0) (by simp) i).continuousAt.continuousWithinAt))
  have hc2 : ContinuousOn (fun y => fun a i l => coordinateHessian (boundaryChartCoefficient w j a) y i l)
      (Metric.closedBall x r) := continuousOn_pi.mpr (fun a => continuousOn_pi.mpr (fun i =>
    continuousOn_pi.mpr (fun l y hy =>
      (contDiffAt_coordinateDerivative (contDiffAt_coordinateDerivative (contDiffAt_infty.mp (hsmooth y hy a) 2)
        (m:=1) (by norm_num) i) (m:=0) (by norm_num) l).continuousAt.continuousWithinAt)))
  obtain ⟨M₀,hM₀⟩ := (isCompact_closedBall x r).exists_bound_of_continuousOn hc0
  obtain ⟨M₁,hM₁⟩ := (isCompact_closedBall x r).exists_bound_of_continuousOn hc1
  obtain ⟨M₂,hM₂⟩ := (isCompact_closedBall x r).exists_bound_of_continuousOn hc2
  refine ⟨r,c,max M₀ 0,max M₁ 0,max M₂ 0,hr,hc,le_max_right _ _,le_max_right _ _,le_max_right _ _,
    fun y hy => (hpatch y hy).le,hsmooth,?_,?_,?_⟩
  · intro y hy a
    exact (norm_le_pi_norm (fun a => boundaryChartCoefficient w j a y) a).trans
      ((hM₀ y hy).trans (le_max_left _ _))
  · intro y hy a i
    exact ((norm_le_pi_norm (fun i => coordinateDerivative i (boundaryChartCoefficient w j a) y) i).trans
      (norm_le_pi_norm (fun a i => coordinateDerivative i (boundaryChartCoefficient w j a) y) a)).trans
      ((hM₁ y hy).trans (le_max_left _ _))
  · intro y hy a i l
    exact (((norm_le_pi_norm (fun l => coordinateHessian (boundaryChartCoefficient w j a) y i l) l).trans
      (norm_le_pi_norm (fun i l => coordinateHessian (boundaryChartCoefficient w j a) y i l) i)).trans
      (norm_le_pi_norm (fun a i l => coordinateHessian (boundaryChartCoefficient w j a) y i l) a)).trans
      ((hM₂ y hy).trans (le_max_left _ _))

/-- The actual tangential derivative field vanishes on the boundary. -/
theorem boundary_tangential_field_eq_zero {u w : CoordinateSpace n → ℝ}
    {x : CoordinateSpace n} {j : Fin n} (hu : DifferentiableAt ℝ u x)
    (hw : ContDiffAt ℝ 2 w x) (hj : coordinateDerivative j w x ≠ 0)
    (hzero : ∀ᶠ y in 𝓝 x, w y = w x → u y = u x) (a : Fin n) :
    coordinateDerivative a u x - boundaryChartCoefficient w j a x * coordinateDerivative j u x = 0 := by
  let e := (coordinateDerivative j w x)⁻¹ • (Pi.single j 1 : CoordinateSpace n)
  have he : fderiv ℝ w x e = 1 := by
    simp only [e, map_smul, smul_eq_mul]
    change (coordinateDerivative j w x)⁻¹ * coordinateDerivative j w x = 1
    exact inv_mul_cancel₀ hj
  have hfirst := fderiv_eq_smul_of_level_constant hu hw he hzero
  have hcoord (i : Fin n) : coordinateDerivative i u x =
      (fderiv ℝ u x e)*coordinateDerivative i w x := by
    exact congrArg (fun D : CoordinateSpace n →L[ℝ] ℝ => D (Pi.single i 1)) hfirst
  rw [hcoord a,hcoord j]
  unfold boundaryChartCoefficient
  field_simp
  <;> ring

end GaussianTilt.MomentMapRegularity
