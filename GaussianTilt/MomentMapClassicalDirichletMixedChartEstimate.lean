import GaussianTilt.MomentMapClassicalDirichletMixedHessian
import GaussianTilt.MomentMapClassicalDirichletBoundaryAtlas

/-!
# Mixed boundary estimates on the constructed chart atlas

The actual PDE, first derivative bounds, and defining-function chart data
supply every hypothesis of the quadratic-patch estimate.
-/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

lemma boundaryPatchQuadratic_sublevel_subset_closedBall {z y : CoordinateSpace n}
    {r : ℝ} (hr : 0 ≤ r) (hy : boundaryPatchQuadratic z y ≤ r^2/2) :
    y ∈ Metric.closedBall z r := by
  apply (dist_pi_le_iff hr).mpr
  intro i
  have hterm : (y i-z i)^2/2 ≤ boundaryPatchQuadratic z y := by
    unfold boundaryPatchQuadratic
    exact Finset.single_le_sum (fun j _ => div_nonneg (sq_nonneg (y j-z j)) (by norm_num)) (Finset.mem_univ i)
  rw [Real.dist_eq]
  have hs : |y i-z i|^2 ≤ r^2 := by rw [sq_abs]; linarith
  exact (sq_le_sq₀ (abs_nonneg _) hr).mp hs

namespace BoundaryChartPatch
variable {w : CoordinateSpace n → ℝ} (p : BoundaryChartPatch w)

/-- The quadratic patch centered at any point of the half-chart stays
inside the actual denominator-controlled full chart. -/
lemma quadratic_patch_inside {z y : CoordinateSpace n}
    (hz : z ∈ Metric.ball p.center (p.radius/2))
    (hy : boundaryPatchQuadratic z y ≤ p.radius^2/8) :
    y ∈ Metric.closedBall p.center p.radius := by
  have hyz : y ∈ Metric.closedBall z (p.radius/2) :=
    boundaryPatchQuadratic_sublevel_subset_closedBall (half_pos p.radius_pos).le
      (by convert hy using 1 <;> ring)
  change dist y p.center ≤ p.radius
  have ht := dist_triangle y z p.center
  change dist y z ≤ p.radius/2 at hyz
  change dist z p.center < p.radius/2 at hz
  linarith

/-- All forcing and artificial-boundary constants are constructed from
actual first derivatives and fixed chart derivatives. -/
theorem mixed_hessian_estimate [NeZero n]
    (hw : ContDiff ℝ ∞ w) (hS : IsCompact {y | w y ≤ 0})
    {κ G K D W : ℝ} (hκ : 0 < κ) (hG : 0 ≤ G) (hK : 0 ≤ K) (hW : 0 ≤ W)
    (hHw : ∀ y ∈ {y | w y ≤ 0},
      (coordinateHessian w y - κ • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef)
    {u F : CoordinateSpace n → ℝ} (hu : ContDiff ℝ ∞ u)
    (hH : ∀ y ∈ interior {y | w y ≤ 0}, (coordinateHessian u y).PosDef)
    (hMA : ∀ y ∈ interior {y | w y ≤ 0}, (coordinateHessian u y).det = Real.exp (F y))
    (hzero : ∀ y, w y = 0 → u y = 0)
    (hGu : ∀ y ∈ {y | w y ≤ 0}, ∀ i, |coordinateDerivative i u y| ≤ G)
    (hKF : ∀ y ∈ interior {y | w y ≤ 0}, ∀ i, |coordinateDerivative i F y| ≤ K)
    (hD : ∀ y ∈ interior {y | w y ≤ 0}, (coordinateHessian u y).det ≤ D)
    (hWw : ∀ y ∈ {y | w y ≤ 0}, ∀ i, |coordinateDerivative i w y| ≤ W)
    {z : CoordinateSpace n} (hz0 : w z = 0) (hz : z ∈ Metric.ball p.center (p.radius/2))
    (a : Fin n) :
    |coordinateHessian u z a p.index - boundaryChartCoefficient w p.index a z *
        coordinateHessian u z p.index p.index| ≤
      ((((1+p.bound₀)*G)/(p.radius^2/8) +
        ((K+p.bound₀*K+2*p.bound₁)*max 1 D+G*(n:ℝ)^2*p.bound₂))/κ)*W + p.bound₁*G := by
  let β := boundaryChartCoefficient w p.index a
  let r := p.radius^2/8
  let M := (K+p.bound₀*K+2*p.bound₁)*max 1 D+G*(n:ℝ)^2*p.bound₂
  let C := (1+p.bound₀)*G
  let P := {y | w y ≤ 0} ∩ {y | boundaryPatchQuadratic z y ≤ r}
  have hr : 0 < r := div_pos (sq_pos_of_pos p.radius_pos) (by norm_num)
  have hM : 0 ≤ M := by
    have h0 := p.bound₀_nonneg
    have h1 := p.bound₁_nonneg
    have h2 := p.bound₂_nonneg
    have hDpos : 0 ≤ max 1 D := zero_le_one.trans (le_max_left _ _)
    dsimp [M]
    positivity
  have hC : 0 ≤ C := mul_nonneg (by linarith [p.bound₀_nonneg]) hG
  have hzP : z ∈ P := ⟨hz0.le, by simpa using hr.le⟩
  have hpatch (y : CoordinateSpace n) (hy : y ∈ P) :
      y ∈ Metric.closedBall p.center p.radius := p.quadratic_patch_inside hz hy.2
  have hzchart := hpatch z hzP
  have hβs (y : CoordinateSpace n) (hy : y ∈ P) : ContDiffAt ℝ ∞ β y := p.smooth y (hpatch y hy) a
  have hTzero (y : CoordinateSpace n) (hy : y ∈ P) (hy0 : w y = 0) :
      coordinateDerivative a u y - β y * coordinateDerivative p.index u y = 0 := by
    apply p.tangent_field_vanishes hw (hpatch y hy) (hu.differentiable (by simp) y)
    apply Eventually.of_forall
    intro v hv
    rw [hzero v (hv.trans hy0), hzero y hy0]
  have hbound (y : CoordinateSpace n) (hy : y ∈ P) :
      |coordinateDerivative a u y - β y * coordinateDerivative p.index u y| ≤ C := by
    calc
      _ ≤ |coordinateDerivative a u y| + |β y * coordinateDerivative p.index u y| := abs_sub _ _
      _ ≤ G + p.bound₀*G := by
        rw [abs_mul]
        exact add_le_add (hGu y hy.1 a) (mul_le_mul (p.value_bound y (hpatch y hy) a)
          (hGu y hy.1 p.index) (abs_nonneg _) p.bound₀_nonneg)
      _ = C := by dsimp [C]; ring
  have hTc : ContinuousOn (fun y => coordinateDerivative a u y - β y * coordinateDerivative p.index u y) P := by
    intro y hy
    exact ((smooth_coordinateDerivative hu a).continuous.continuousAt.sub
      ((hβs y hy).continuousAt.mul (smooth_coordinateDerivative hu p.index).continuous.continuousAt)).continuousWithinAt
  have hTs (y : CoordinateSpace n) (hy : y ∈ interior P) :
      ContDiffAt ℝ 2 (fun y => coordinateDerivative a u y - β y * coordinateDerivative p.index u y) y :=
    (contDiff_infty.mp (smooth_coordinateDerivative hu a) 2).contDiffAt.sub
      ((contDiffAt_infty.mp (hβs y (interior_subset hy)) 2).mul
        (contDiff_infty.mp (smooth_coordinateDerivative hu p.index) 2).contDiffAt)
  have hiS : interior P ⊆ interior {y | w y ≤ 0} := interior_mono inter_subset_left
  have hLT (y : CoordinateSpace n) (hy : y ∈ interior P) :
      |linearizedMA (coordinateHessian u y)⁻¹
        (fun y => coordinateDerivative a u y - β y * coordinateDerivative p.index u y) y| ≤
        M * (coordinateHessian u y)⁻¹.trace := by
    have hyP := interior_subset hy
    have hym := hiS hy
    have hnear : ∀ᶠ v in 𝓝 y, (coordinateHessian u v).det = Real.exp (F v) := by
      filter_upwards [isOpen_interior.mem_nhds hym] with v hv
      exact hMA v hv
    exact tangential_derivative_forcing_trace_bound hu (contDiffAt_infty.mp (hβs y hyP) 2)
      (hH y hym) hnear a p.index hG p.bound₀_nonneg p.bound₁_nonneg p.bound₂_nonneg hK
      (hGu y hyP.1 p.index) (p.value_bound y (hpatch y hyP) a)
      (p.derivative_bound y (hpatch y hyP) a p.index)
      (p.hessian_bound y (hpatch y hyP) a) (hKF y hym a) (hKF y hym p.index) (hD y hym)
  have hb := adapted_mixed_hessian_bound_of_patch hw.continuous hS a p.index hz0
    (hw.differentiable (by simp) z) (p.derivative_ne_zero hzchart)
    (contDiff_infty.mp hu 2).contDiffAt ((hβs z hzP).differentiableAt (by simp))
    hr hC hM hκ p.bound₁_nonneg (p.derivative_bound z hzchart a p.index)
    (hGu z hzP.1 p.index) (hTzero z hzP hz0) hTc
    (fun y hy hq => hTzero y ⟨hS.isClosed.closure_eq ▸ hy.1,hq⟩
      (frontier_le_subset_eq hw.continuous continuous_const hy))
    (fun y hy hq => hbound y ⟨hy,hq.le⟩) hTs
    (fun y _ => (contDiff_infty.mp hw 2).contDiffAt)
    (fun y hy => (hH y (hiS hy)).inv) hLT
    (fun y hy => hHw y (interior_subset hy).1)
  apply hb.trans
  apply add_le_add_right
  exact mul_le_mul_of_nonneg_left (hWw z hzP.1 p.index)
    (div_nonneg (add_nonneg (div_nonneg hC hr.le) hM) hκ.le)

end BoundaryChartPatch
end GaussianTilt.MomentMapRegularity
