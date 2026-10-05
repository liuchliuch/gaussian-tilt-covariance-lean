import GaussianTilt.MomentMapLinearDirichletBarrierAssembly
import GaussianTilt.MomentMapRegularityConstantDensityCalabiBall
import GaussianTilt.MomentMapClassicalDirichletOperator

/-! # Actual half-ball geometry and both quadratic boundary barriers -/
noncomputable section
open Matrix Set Filter
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapRegularity
variable {n : ℕ}

def coordinateHalfBall (j : Fin n) (R : ℝ) : Set (CoordinateSpace n) :=
  {x | ‖(coordinateEquiv n).symm x‖ < R ∧ 0 < x j}

lemma isOpen_coordinateHalfBall (j : Fin n) (R : ℝ) : IsOpen (coordinateHalfBall j R) :=
  (isOpen_lt (coordinateEquiv n).symm.continuous.norm continuous_const).inter
    (isOpen_lt continuous_const (continuous_apply j))

lemma coordinate_abs_le_euclidean_norm (x : CoordinateSpace n) (i : Fin n) :
    |x i| ≤ ‖(coordinateEquiv n).symm x‖ :=
  PiLp.norm_apply_le ((coordinateEquiv n).symm x) i

lemma coordinateHalfBall_strip (j i : Fin n) {R : ℝ} {x : CoordinateSpace n}
    (hx : x ∈ coordinateHalfBall j R) : |x i| ≤ R :=
  (coordinate_abs_le_euclidean_norm x i).trans hx.1.le

lemma isBounded_coordinateHalfBall (j : Fin n) (R : ℝ) : Bornology.IsBounded (coordinateHalfBall j R) := by
  apply (isCompact_closedBall (0 : CoordinateSpace n) (max R 0)).isBounded.subset
  intro x hx
  simp only [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (le_max_right _ _)).mpr
  intro i
  exact (coordinateHalfBall_strip j i hx).trans (le_max_left _ _)

lemma coordinateHalfBall_frontier {j : Fin n} {R : ℝ} {x : CoordinateSpace n}
    (hx : x ∈ frontier (coordinateHalfBall j R)) :
    ‖(coordinateEquiv n).symm x‖ ≤ R ∧ 0 ≤ x j ∧
      (‖(coordinateEquiv n).symm x‖ = R ∨ x j = 0) := by
  have hc : IsClosed {x : CoordinateSpace n | ‖(coordinateEquiv n).symm x‖ ≤ R ∧ 0 ≤ x j} :=
    (isClosed_le (coordinateEquiv n).symm.continuous.norm continuous_const).inter
      (isClosed_le continuous_const (continuous_apply j))
  have hsub : closure (coordinateHalfBall j R) ⊆
      {x : CoordinateSpace n | ‖(coordinateEquiv n).symm x‖ ≤ R ∧ 0 ≤ x j} :=
    closure_minimal (fun _ h => ⟨h.1.le, h.2.le⟩) hc
  have hb := hsub (frontier_subset_closure hx)
  have hnot : x ∉ coordinateHalfBall j R := by
    have hn : x ∉ interior (coordinateHalfBall j R) := hx.2
    rwa [(isOpen_coordinateHalfBall j R).interior_eq] at hn
  refine ⟨hb.1, hb.2, ?_⟩
  by_cases hr : ‖(coordinateEquiv n).symm x‖ < R
  · right
    have hn : ¬0 < x j := fun hh => hnot ⟨hr, hh⟩
    exact le_antisymm (le_of_not_gt hn) hb.2
  · left
    exact le_antisymm hb.1 (le_of_not_gt hr)

def halfBallRadialBarrier (F R : ℝ) (x : CoordinateSpace n) : ℝ := F * calabiBallCutoff 0 R x

def halfBallNormalBarrier (j : Fin n) (F R : ℝ) (x : CoordinateSpace n) : ℝ := F * (2 * R * x j - (x j) ^ 2)

lemma halfBallRadialBarrier_smooth (F R : ℝ) : ContDiff ℝ ∞ (halfBallRadialBarrier (n := n) F R) :=
  contDiff_const.mul (contDiff_calabiBallCutoff 0 R)

lemma halfBallNormalBarrier_smooth (j : Fin n) (F R : ℝ) : ContDiff ℝ ∞ (halfBallNormalBarrier j F R) := by
  unfold halfBallNormalBarrier
  fun_prop

lemma laplacian_eq_linearized_one (u : CoordinateSpace n → ℝ) (x : CoordinateSpace n) :
    euclideanLaplacian u x = linearizedMA (1 : Matrix (Fin n) (Fin n) ℝ) u x := by
  simp only [linearizedMA, Matrix.one_mul, Matrix.trace, Matrix.diag_apply,
    euclideanLaplacian, coordinateHessian]

lemma halfBallRadialBarrier_laplacian (F R : ℝ) (x : CoordinateSpace n) :
    euclideanLaplacian (halfBallRadialBarrier (n := n) F R) x = -2 * (n : ℝ) * F := by
  unfold halfBallRadialBarrier
  rw [euclideanLaplacian_const_mul F (contDiff_calabiBallCutoff 0 R),
    laplacian_eq_linearized_one, linearizedMA_calabiBallCutoff]
  simp only [Matrix.trace_one, Fintype.card_fin]
  ring

lemma halfBallNormalBarrier_laplacian (j : Fin n) (F R : ℝ) (x : CoordinateSpace n) :
    euclideanLaplacian (halfBallNormalBarrier j F R) x = -2 * F := by
  have he : halfBallNormalBarrier j F R = fun y : CoordinateSpace n => (2 * F * R) * y j - (2 * F) * ((y j) ^ 2 / 2) := by
    funext y
    unfold halfBallNormalBarrier
    ring
  rw [he, laplacian_eq_linearized_one]
  have h1 : ContDiffAt ℝ 2 (fun y : CoordinateSpace n => (2 * F * R) * y j) x := by fun_prop
  have h2 : ContDiffAt ℝ 2 (fun y : CoordinateSpace n => (2 * F) * ((y j) ^ 2 / 2)) x := by fun_prop
  have hsub : linearizedMA (1 : Matrix (Fin n) (Fin n) ℝ)
      (fun y : CoordinateSpace n => (2 * F * R) * y j - (2 * F) * ((y j) ^ 2 / 2)) x =
      linearizedMA 1 (fun y : CoordinateSpace n => (2 * F * R) * y j) x -
        linearizedMA 1 (fun y : CoordinateSpace n => (2 * F) * ((y j) ^ 2 / 2)) x := by
    simp only [linearizedMA, coordinateHessian_sub_at h1 h2, Matrix.mul_sub, Matrix.trace_sub]
  have hcoord : linearizedMA (1 : Matrix (Fin n) (Fin n) ℝ) (fun y : CoordinateSpace n => y j) x = 0 := by
    simp only [linearizedMA, coordinateHessian_coordinate, Matrix.mul_zero, Matrix.trace_zero]
  rw [hsub, linearizedMA_const_mul_at _ (by fun_prop : ContDiffAt ℝ 2 (fun y : CoordinateSpace n => y j) x),
    hcoord, linearizedMA_const_mul_at _ (by fun_prop : ContDiffAt ℝ 2 (fun y : CoordinateSpace n => (y j)^2 / 2) x),
    linearizedMA_coordinate_half_sq]
  simp

lemma halfBallRadialBarrier_bounds {j : Fin n} {F R : ℝ} (hF : 0 ≤ F) (hR : 0 < R)
    {x : CoordinateSpace n} (hx : x ∈ coordinateHalfBall j R) :
    0 ≤ halfBallRadialBarrier F R x ∧ halfBallRadialBarrier F R x ≤ F * R ^ 2 := by
  rw [halfBallRadialBarrier, calabiBallCutoff_eq_norm]
  simp only [map_zero, sub_zero]
  have hn := norm_nonneg ((coordinateEquiv n).symm x)
  constructor
  · apply mul_nonneg hF
    nlinarith [hx.1]
  · exact mul_le_mul_of_nonneg_left (sub_le_self _ (sq_nonneg _)) hF

lemma halfBallNormalBarrier_bounds {j : Fin n} {F R : ℝ} (hF : 0 ≤ F) (hR : 0 < R)
    {x : CoordinateSpace n} (hx : x ∈ coordinateHalfBall j R) :
    0 ≤ halfBallNormalBarrier j F R x ∧ halfBallNormalBarrier j F R x ≤ 2 * F * R * x j := by
  have hxR : x j ≤ R := (le_abs_self _).trans (coordinateHalfBall_strip j j hx)
  unfold halfBallNormalBarrier
  constructor
  · apply mul_nonneg hF
    nlinarith [mul_nonneg hx.2.le (show 0 ≤ 2 * R - x j by linarith)]
  · nlinarith [mul_nonneg hF (sq_nonneg (x j))]

end GaussianTilt.MomentMapLinearDirichlet
