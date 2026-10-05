import GaussianTilt.MomentMapLinearDirichletQuantitativeChartBounds

/-!
# Flattened height supplies a genuine original-domain interior ball

The ball is constructed from the actual defining-function derivative bound
and the exact inverse-chart level identity, rather than postulated as a
chart comparability assumption.
-/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

/-- The concrete compact chart needed by the intrinsic boundary estimates.
The same constants control both chart directions and the physical interior
ball whose radius is proportional to the positive flattened height. -/
theorem exists_quantitative_regularLevelFlattening_chart {w : KernelSpace n → ℝ}
    (hw : ContDiff ℝ ∞ w) (a : KernelSpace n) (j : Fin n)
    (hj : fderiv ℝ w a (EuclideanSpace.basisFun (Fin n) ℝ j) ≠ 0)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ s c C : ℝ, 0 < s ∧ s ≤ 1 ∧ 0 < c ∧ c ≤ 1 ∧ 1 ≤ C ∧
      (∀ z ∈ Metric.closedBall (0 : KernelSpace n) (2*s),
        z ∈ (regularLevelFlatteningChart hw a j hj).target ∧
        ContDiffAt ℝ ∞ (regularLevelFlatteningChart hw a j hj).symm z ∧
        dist ((regularLevelFlatteningChart hw a j hj).symm z) a < ρ/2 ∧
        w ((regularLevelFlatteningChart hw a j hj).symm z)=w a-z j ∧
        ThreeDerivativeBound (regularLevelFlatteningChart hw a j hj).symm z C) ∧
      (∀ x ∈ Metric.closedBall a ρ,
        ThreeDerivativeBound (flatteningMap w a j) x C ∧ ThreeDerivativeBound w x C) ∧
      (∀ z ∈ Metric.closedBall (0 : KernelSpace n) s, 0 < z j →
        0 < c*z j ∧ c*z j ≤ 1 ∧
        Metric.closedBall ((regularLevelFlatteningChart hw a j hj).symm z) (c*z j) ⊆
          {x | w x < w a} ∩ Metric.closedBall a ρ) ∧
      (∀ z ∈ Metric.closedBall (0 : KernelSpace n) (2*s),
        ∀ z' ∈ Metric.closedBall (0 : KernelSpace n) (2*s),
        dist ((regularLevelFlatteningChart hw a j hj).symm z)
          ((regularLevelFlatteningChart hw a j hj).symm z') ≤ C*dist z z') ∧
      (∀ x ∈ Metric.closedBall a ρ, ∀ y ∈ Metric.closedBall a ρ,
        dist (flatteningMap w a j x) (flatteningMap w a j y) ≤ C*dist x y) := by
  obtain ⟨s,C,hs,hs1,hC,hInv,hForward⟩ := exists_quantitative_regularLevelFlattening_bounds hw a j hj hρ
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  let c := min 1 (min (ρ/2) (1/(2*C)))
  have hc : 0 < c := by dsimp only [c]; positivity
  have hc1 : c ≤ 1 := min_le_left _ _
  have hcρ : c ≤ ρ/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hcC : c ≤ 1/(2*C) := (min_le_right _ _).trans (min_le_right _ _)
  have hCc : C*c ≤ 1/2 := by
    have hh := (le_div_iff₀ (show 0 < 2*C by positivity)).mp hcC
    nlinarith
  refine ⟨s,c,C,hs,hs1,hc,hc1,hC,hInv,hForward,?_,?_,?_⟩
  · intro z hz hzj
    have hz2 : z ∈ Metric.closedBall (0:KernelSpace n) (2*s) :=
      Metric.closedBall_subset_closedBall (by linarith) hz
    have hzi := hInv z hz2
    have hzn : ‖z‖ ≤ s := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz
    have hheight : z j ≤ 1 := by
      have hh : |z j| ≤ ‖z‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le z j
      exact (le_abs_self _).trans (hh.trans (hzn.trans hs1))
    have hrC : c*z j ≤ c := by nlinarith
    have hrρ : c*z j ≤ ρ/2 := hrC.trans hcρ
    have hxρ : (regularLevelFlatteningChart hw a j hj).symm z ∈ Metric.closedBall a ρ := by
      change dist _ a ≤ ρ
      linarith [hzi.2.2.1]
    refine ⟨mul_pos hc hzj,hrC.trans hc1,?_⟩
    intro y hy
    have hyρ : y ∈ Metric.closedBall a ρ := by
      have hh := dist_triangle y ((regularLevelFlatteningChart hw a j hj).symm z) a
      change dist y ((regularLevelFlatteningChart hw a j hj).symm z) ≤ c*z j at hy
      change dist y a ≤ ρ
      linarith [hzi.2.2.1]
    have hLip := (convex_closedBall a ρ).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun x _ => (hw.differentiable (by simp) x).hasFDerivAt.hasFDerivWithinAt)
      (fun x hx => (hForward x hx).2.1) hxρ hyρ
    change |w y-w ((regularLevelFlatteningChart hw a j hj).symm z)| ≤
      C*dist y ((regularLevelFlatteningChart hw a j hj).symm z) at hLip
    have hm := mul_le_mul_of_nonneg_left hy hCpos.le
    have hhalf := mul_le_mul_of_nonneg_right hCc hzj.le
    have hwlevel := hzi.2.2.2.1
    refine ⟨?_,hyρ⟩
    change w y < w a
    have hdiff := (abs_le.mp hLip).2
    nlinarith
  · intro z hz z' hz'
    have hDer (x : KernelSpace n) (hx : x ∈ Metric.closedBall (0:KernelSpace n) (2*s)) :
        HasFDerivWithinAt (regularLevelFlatteningChart hw a j hj).symm
          (fderiv ℝ (regularLevelFlatteningChart hw a j hj).symm x)
          (Metric.closedBall (0:KernelSpace n) (2*s)) x :=
      ((hInv x hx).2.1.differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt
    have hh := (convex_closedBall (0:KernelSpace n) (2*s)).norm_image_sub_le_of_norm_hasFDerivWithin_le hDer
      (fun x hx => (hInv x hx).2.2.2.2.1) hz' hz
    simpa only [dist_eq_norm] using hh
  · intro x hx y hy
    have hΨ := contDiff_flatteningMap hw a j
    have hh := (convex_closedBall a ρ).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun z _ => (hΨ.differentiable (by simp) z).hasFDerivAt.hasFDerivWithinAt)
      (fun z hz => (hForward z hz).1.1) hy hx
    simpa only [dist_eq_norm] using hh

end GaussianTilt.MomentMapLinearDirichlet
