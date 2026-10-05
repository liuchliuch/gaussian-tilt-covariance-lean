import GaussianTilt.MomentMapLinearDirichletQuantitativeCoefficient

/-! # Direct coefficient interface for the already chosen compact chart -/
noncomputable section
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxSize 2048
open Matrix Set Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapRegularity GaussianTilt.Letwin
variable {n : ℕ}

/-- Scaling the raw unit ball gives the actual physical interior ball.
This consumes the ball inclusion constructed by the quantitative chart. -/
theorem scaled_raw_chart_height_ball {w : KernelSpace n → ℝ} (hw : ContDiff ℝ ∞ w)
    (a : KernelSpace n) (j : Fin n)
    (hj : fderiv ℝ w a (EuclideanSpace.basisFun (Fin n) ℝ j) ≠ 0)
    {s c : ℝ} (hs : 0 < s) {U : Set (KernelSpace n)}
    (hBall : ∀ z ∈ Metric.closedBall (0:KernelSpace n) s, 0 < z j →
      0 < c*z j ∧ c*z j ≤ 1 ∧
      Metric.closedBall ((regularLevelFlatteningChart hw a j hj).symm z) (c*z j) ⊆ U)
    {y : CoordinateSpace n} (hy : ‖(coordinateEquiv n).symm y‖ ≤ 1) (hyj : 0 < y j) :
    0 < c*s*y j ∧ c*s*y j ≤ 1 ∧
      Metric.closedBall ((coordinateEquiv n).symm (scaledRawInverseChart hw a j hj s y)) (c*s*y j) ⊆ U := by
  have hz : s • (coordinateEquiv n).symm y ∈ Metric.closedBall (0:KernelSpace n) s := by
    simp only [Metric.mem_closedBall,dist_zero_right,norm_smul,Real.norm_of_nonneg hs.le]
    nlinarith
  have hzj : (s • (coordinateEquiv n).symm y) j=s*y j := rfl
  have hh := hBall _ hz (by rw [hzj]; exact mul_pos hs hyj)
  simpa only [hzj,← mul_assoc,scaledRawInverseChart,ContinuousLinearEquiv.symm_apply_apply] using hh

/-- The same fixed chart scale and constants are reused verbatim. No new
choice of chart is made in the coefficient transfer. -/
theorem scaled_raw_chart_coefficient_bounds {w : KernelSpace n → ℝ}
    (hw : ContDiff ℝ ∞ w) (a : KernelSpace n) (j : Fin n)
    (hj : fderiv ℝ w a (EuclideanSpace.basisFun (Fin n) ℝ j) ≠ 0)
    (hn : 0 < n) {s c C Cx Cj ρ lam Λ K : ℝ}
    (hs : 0 < s) (hc : 0 < c) (hC : 1 ≤ C) (hCx : 1 ≤ Cx) (hCj : 1 ≤ Cj) (hρ : 0 < ρ)
    (hlam : 0 ≤ lam) (hΛ : 0 ≤ Λ) (hK : 0 ≤ K)
    (hInv : ∀ z ∈ Metric.closedBall (0:KernelSpace n) (2*s),
      z ∈ (regularLevelFlatteningChart hw a j hj).target ∧
      ContDiffAt ℝ ∞ (regularLevelFlatteningChart hw a j hj).symm z ∧
      dist ((regularLevelFlatteningChart hw a j hj).symm z) a < ρ/2 ∧
      w ((regularLevelFlatteningChart hw a j hj).symm z)=w a-z j ∧
      ThreeDerivativeBound (regularLevelFlatteningChart hw a j hj).symm z C)
    (hForward : ∀ x ∈ Metric.closedBall a ρ,
      ThreeDerivativeBound (flatteningMap w a j) x C ∧ ThreeDerivativeBound w x C)
    (hRawSmooth : ∀ y, ‖(coordinateEquiv n).symm y‖ < 2 →
      ContDiffAt ℝ ∞ (scaledRawInverseChart hw a j hj s) y ∧
      ∀ i k, ContDiffAt ℝ ∞ (fun z => scaledRawChartJacobian hw a j hj s z i k) y)
    (hRawBound : ∀ y, ‖(coordinateEquiv n).symm y‖ ≤ 1 →
      ThreeDerivativeBound (scaledRawInverseChart hw a j hj s) y Cx ∧
      (∀ i k, |scaledRawChartJacobian hw a j hj s y i k| ≤ Cj) ∧
      ∀ k i l, |matrixCoordinateDerivative (scaledRawChartJacobian hw a j hj s) k y i l| ≤ Cj)
    {y : CoordinateSpace n} (hy : ‖(coordinateEquiv n).symm y‖ ≤ 1) (hyj : 0 < y j)
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hA : (A (scaledRawInverseChart hw a j hj s y)).PosDef)
    (hAd : ∀ i k, DifferentiableAt ℝ (fun x => A x i k) (scaledRawInverseChart hw a j hj s y))
    (hEll : ∀ v : CoordinateSpace n,
      lam*‖(coordinateEquiv n).symm v‖^2 ≤ v ⬝ᵥ (A (scaledRawInverseChart hw a j hj s y)*ᵥv) ∧
      v ⬝ᵥ (A (scaledRawInverseChart hw a j hj s y)*ᵥv) ≤ Λ*‖(coordinateEquiv n).symm v‖^2)
    (hDA : ∀ k i l, (c*s*y j)*|matrixCoordinateDerivative A k (scaledRawInverseChart hw a j hj s y) i l| ≤ K) :
    (scaledRawChartCoefficient hw a j hj s A y).PosDef ∧
    (∀ v : CoordinateSpace n,
      (lam/((n:ℝ)^2*C^2))*‖(coordinateEquiv n).symm v‖^2 ≤
        v ⬝ᵥ (scaledRawChartCoefficient hw a j hj s A y*ᵥv) ∧
      v ⬝ᵥ (scaledRawChartCoefficient hw a j hj s A y*ᵥv) ≤
        (Λ*((n:ℝ)^2*C^2))*‖(coordinateEquiv n).symm v‖^2) ∧
    (∀ k i l, y j*|matrixCoordinateDerivative (scaledRawChartCoefficient hw a j hj s A) k y i l| ≤
      (n:ℝ)^2*Cj^2*(2*Λ+(n:ℝ)*K*Cx/(c*s))) := by
  have hz : s • (coordinateEquiv n).symm y ∈ Metric.closedBall (0:KernelSpace n) (2*s) := by
    simp only [Metric.mem_closedBall,dist_zero_right,norm_smul,Real.norm_of_nonneg hs.le]
    nlinarith
  have hi := hInv _ hz
  have hx : (regularLevelFlatteningChart hw a j hj).symm (s • (coordinateEquiv n).symm y) ∈ Metric.closedBall a ρ := by
    change dist _ a ≤ ρ
    linarith [hi.2.2.1]
  have hys := hRawSmooth y (by linarith)
  have hyb := hRawBound y hy
  have hyj1 : y j ≤ 1 := by
    have hh := PiLp.norm_apply_le ((coordinateEquiv n).symm y) j
    change |y j| ≤ ‖(coordinateEquiv n).symm y‖ at hh
    exact (le_abs_self _).trans (hh.trans hy)
  exact scaled_raw_chart_coefficient_bounds_at hw a j hj hn hs hc (by linarith)
    (by linarith) (by linarith) hlam hΛ hK hyj hyj1 hi.1
    (hi.2.1.differentiableAt (by simp)) hi.2.2.2.2.1 (hForward _ hx).1.1
    (hys.1.differentiableAt (by simp)) hyb.1.1 (fun i k => (hys.2 i k).differentiableAt (by simp))
    hyb.2.1 hyb.2.2 hA hAd hEll hDA

end GaussianTilt.MomentMapLinearDirichlet
