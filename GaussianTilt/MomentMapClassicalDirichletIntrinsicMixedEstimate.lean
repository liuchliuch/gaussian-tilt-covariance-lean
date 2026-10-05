import GaussianTilt.MomentMapClassicalDirichletIntrinsicMixedCalculus
import GaussianTilt.MomentMapClassicalDirichletMixedChartEstimate

/-! # Actual mixed boundary estimates for intrinsic Dirichlet jets -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 500000
open Set Filter Matrix
open scoped Topology ContDiff BigOperators
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin GaussianTilt.HolderSpace
variable {n : ℕ}
namespace SmoothInnerDomain
variable {S A : Set (E n)} (d : SmoothInnerDomain S A)

/-- The full mixed boundary estimate with only interior smoothness and
actual within-domain boundary jets. No extension across the boundary is used. -/
theorem intrinsic_mixed_hessian_on_chart [NeZero n] {α a₀ b₀ : ℝ} (hα : 0 < α)
    (p : BoundaryChartPatch d.coordinateDefining)
    (j : zeroBoundary (CoordinateSpace n) ℝ d.coordinate_body_convex α)
    (hs : ContDiffOn ℝ ∞ (intrinsicValue d.coordinate_body_convex α j.1) (interior {y | d.coordinateDefining y ≤ 0}))
    {F : CoordinateSpace n → ℝ}
    (hp : ∀ y ∈ interior {z | d.coordinateDefining z ≤ 0}, (intrinsicHessian d.coordinate_body_convex α j.1 y).PosDef)
    (hMA : ∀ y ∈ interior {z | d.coordinateDefining z ≤ 0},
      (intrinsicHessian d.coordinate_body_convex α j.1 y).det = Real.exp (F y))
    (hbar : ∀ y ∈ {z | d.coordinateDefining z ≤ 0},
      b₀*d.coordinateDefining y ≤ intrinsicValue d.coordinate_body_convex α j.1 y ∧
      intrinsicValue d.coordinate_body_convex α j.1 y ≤ a₀*d.coordinateDefining y)
    {G K D W : ℝ} (hG : 0 ≤ G) (hK : 0 ≤ K) (hW : 0 ≤ W)
    (hGu : ∀ y ∈ {z | d.coordinateDefining z ≤ 0}, ∀ i, |intrinsicDerivative d.coordinate_body_convex α j.1 i y| ≤ G)
    (hKF : ∀ y ∈ interior {z | d.coordinateDefining z ≤ 0}, ∀ i, |coordinateDerivative i F y| ≤ K)
    (hdet : ∀ y ∈ interior {z | d.coordinateDefining z ≤ 0}, (intrinsicHessian d.coordinate_body_convex α j.1 y).det ≤ D)
    (hWw : ∀ y ∈ {z | d.coordinateDefining z ≤ 0}, ∀ i, |coordinateDerivative i d.coordinateDefining y| ≤ W)
    {z : CoordinateSpace n} (hz0 : d.coordinateDefining z = 0)
    (hz : z ∈ Metric.ball p.center (p.radius/2)) (a : Fin n) :
    |intrinsicHessian d.coordinate_body_convex α j.1 z a p.index-
      boundaryChartCoefficient d.coordinateDefining p.index a z*intrinsicHessian d.coordinate_body_convex α j.1 z p.index p.index| ≤
      ((((1+p.bound₀)*G)/(p.radius^2/8)+
        ((K+p.bound₀*K+2*p.bound₁)*max 1 D+G*(n:ℝ)^2*p.bound₂))/d.modulus)*W+p.bound₁*G := by
  let β := boundaryChartCoefficient d.coordinateDefining p.index a
  let T := intrinsicTangentField d.coordinate_body_convex α j.1 β a p.index
  let H := intrinsicHessian d.coordinate_body_convex α j.1
  let r := p.radius^2/8
  let P := {y | d.coordinateDefining y ≤ 0} ∩ {y | boundaryPatchQuadratic z y ≤ r}
  let M := (K+p.bound₀*K+2*p.bound₁)*max 1 D+G*(n:ℝ)^2*p.bound₂
  let C := (1+p.bound₀)*G
  let B := (C/r+M)/d.modulus
  have hr : 0 < r := div_pos (sq_pos_of_pos p.radius_pos) (by norm_num)
  have hM : 0 ≤ M := by
    have h0 := p.bound₀_nonneg
    have h1 := p.bound₁_nonneg
    have h2 := p.bound₂_nonneg
    have hm : 0 ≤ max 1 D := zero_le_one.trans (le_max_left _ _)
    dsimp [M]
    positivity
  have hC : 0 ≤ C := mul_nonneg (by linarith [p.bound₀_nonneg]) hG
  have hB : 0 ≤ B := div_nonneg (add_nonneg (div_nonneg hC hr.le) hM) d.modulus_pos.le
  have hzS : d.coordinateDefining z ≤ 0 := hz0.le
  have hzP : z ∈ P := ⟨hzS,by simpa using hr.le⟩
  have hpatch (y : CoordinateSpace n) (hy : y ∈ P) : y ∈ Metric.closedBall p.center p.radius :=
    p.quadratic_patch_inside hz hy.2
  have hβs (y : CoordinateSpace n) (hy : y ∈ P) : ContDiffAt ℝ ∞ β y := p.smooth y (hpatch y hy) a
  have hq := contDiff_boundaryPatchQuadratic z (k := 2)
  have hP : IsCompact P := d.coordinate_body_compact.inter_right (isClosed_le hq.continuous continuous_const)
  have hiS : interior P ⊆ interior {y | d.coordinateDefining y ≤ 0} := interior_mono inter_subset_left
  have hTc : ContinuousOn T P := by
    apply (continuousOn_intrinsicDerivative d.coordinate_body_convex α j.1 a).mono inter_subset_left |>.sub
    apply ContinuousOn.mul _ ((continuousOn_intrinsicDerivative d.coordinate_body_convex α j.1 p.index).mono inter_subset_left)
    exact fun y hy => (hβs y hy).continuousAt.continuousWithinAt
  have hTs (y : CoordinateSpace n) (hy : y ∈ interior P) : ContDiffAt ℝ 2 T y :=
    (contDiffAt_infty.mp (contDiffAt_intrinsicDerivative d.coordinate_body_convex hα j.1 hs (hiS hy) a) 2).sub
      ((contDiffAt_infty.mp (hβs y (interior_subset hy)) 2).mul
        (contDiffAt_infty.mp (contDiffAt_intrinsicDerivative d.coordinate_body_convex hα j.1 hs (hiS hy) p.index) 2))
  have hTbound (y : CoordinateSpace n) (hy : y ∈ P) : |T y| ≤ C := by
    have hh := abs_sub (intrinsicDerivative d.coordinate_body_convex α j.1 a y)
      (β y*intrinsicDerivative d.coordinate_body_convex α j.1 p.index y)
    have hb : |β y*intrinsicDerivative d.coordinate_body_convex α j.1 p.index y| ≤ p.bound₀*G := by
      rw [abs_mul]
      exact mul_le_mul (p.value_bound y (hpatch y hy) a) (hGu y hy.1 p.index) (abs_nonneg _) p.bound₀_nonneg
    dsimp [T,intrinsicTangentField,C]
    nlinarith [hGu y hy.1 a]
  have hTzero (y : CoordinateSpace n) (hy : y ∈ P) (hy0 : d.coordinateDefining y = 0) : T y = 0 :=
    d.intrinsic_tangent_field_zero hα j p (hpatch y hy) hy0 hbar a
  have hLT (y : CoordinateSpace n) (hy : y ∈ interior P) : |linearizedMA (H y)⁻¹ T y| ≤ M*(H y)⁻¹.trace :=
    intrinsic_tangent_forcing_trace_bound d.coordinate_body_convex hα j.1 hs hMA (hiS hy)
      (contDiffAt_infty.mp (hβs y (interior_subset hy)) 2) (hp y (hiS hy)) a p.index hG
      p.bound₀_nonneg p.bound₁_nonneg p.bound₂_nonneg hK
      (hGu y (interior_subset hy).1 p.index) (p.value_bound y (hpatch y (interior_subset hy)) a)
      (p.derivative_bound y (hpatch y (interior_subset hy)) a p.index)
      (p.hessian_bound y (hpatch y (interior_subset hy)) a)
      (hKF y (hiS hy) a) (hKF y (hiS hy) p.index) (hdet y (hiS hy))
  have hbound : ∀ y ∈ P, |T y| ≤ (C/r)*boundaryPatchQuadratic z y-B*d.coordinateDefining y := by
    apply mixed_derivative_patch_barrier hP hTc d.coordinateDefining_smooth.continuous.continuousOn hq.continuous.continuousOn
      hTs (fun _ _ => (contDiff_infty.mp d.coordinateDefining_smooth 2).contDiffAt)
      (fun _ _ => hq.contDiffAt) (fun y hy => (hp y (hiS hy)).inv) hM (div_nonneg hC hr.le) d.modulus_pos hLT
      (fun y hy => linearizedMA_lower_of_hessian_lower (hp y (hiS hy)).inv.posSemidef
        (d.coordinate_hessian_sub_modulus_posSemidef y))
      (fun y _ => (linearizedMA_boundaryPatchQuadratic _ _ _).le)
      (mixed_patch_boundary_bound d.coordinate_body_compact.isClosed hr hC
        (fun y hy hqy => hTzero y ⟨d.coordinate_body_compact.isClosed.frontier_subset hy,hqy⟩
          (d.coordinate_zero_boundary y hy)) (fun y hy hqy => hTbound y ⟨hy,hqy.le⟩))
    intro y hy
    exact (hP.isClosed.frontier_subset hy).1
  let Dₜ := intrinsicTangentDifferential d.coordinate_body_convex α j.1 β a p.index z
  let e := coordinateTransverse d.coordinateDefining z p.index
  have hj := p.derivative_ne_zero (hpatch z hzP)
  have he : fderiv ℝ d.coordinateDefining z e = 1 := fderiv_coordinateTransverse_self hj
  have hnorm := within_mixed_boundary_slope_bound
    (intrinsicTangentField_hasFDerivWithinAt d.coordinate_body_convex hα j.1 hzS
      ((hβs z hzP).differentiableAt (by simp)) a p.index)
    (d.coordinateDefining_smooth.differentiable (by simp) z) (hq.differentiable (by norm_num) z)
    (hTzero z hzP hz0) hz0 (boundaryPatchQuadratic_self z) (fderiv_boundaryPatchQuadratic_self z e)
    (show P ⊆ {y | d.coordinateDefining y ≤ 0} from inter_subset_left)
    (eventually_in_defining_patch (d.coordinateDefining_smooth.differentiable (by simp) z)
      hq.continuous.continuousAt hz0 (by rw [he]; norm_num) (by simpa using hr)) hbound
  rw [he,mul_one] at hnorm
  have hcoord : |Dₜ (Pi.single p.index 1)| ≤ B*W := by
    have heq : |Dₜ (Pi.single p.index 1)| = |Dₜ e| * |coordinateDerivative p.index d.coordinateDefining z| := by
      simp only [e,coordinateTransverse,map_smul,smul_eq_mul,abs_mul,abs_inv]
      field_simp
    rw [heq]
    exact mul_le_mul hnorm (hWw z hzS p.index) (abs_nonneg _) hB
  have herror : |coordinateDerivative p.index β z*intrinsicDerivative d.coordinate_body_convex α j.1 p.index z| ≤ p.bound₁*G := by
    rw [abs_mul]
    exact mul_le_mul (p.derivative_bound z (hpatch z hzP) a p.index) (hGu z hzS p.index)
      (abs_nonneg _) p.bound₁_nonneg
  have heq := intrinsicTangentDifferential_apply_coordinate d.coordinate_body_convex α j.1 β a p.index p.index z
  have habs := abs_add_le (Dₜ (Pi.single p.index 1))
    (coordinateDerivative p.index β z*intrinsicDerivative d.coordinate_body_convex α j.1 p.index z)
  have hxval : intrinsicHessian d.coordinate_body_convex α j.1 z a p.index-
      β z*intrinsicHessian d.coordinate_body_convex α j.1 z p.index p.index =
      Dₜ (Pi.single p.index 1)+coordinateDerivative p.index β z*intrinsicDerivative d.coordinate_body_convex α j.1 p.index z := by
    dsimp [Dₜ]
    rw [heq]
    ring
  change |intrinsicHessian d.coordinate_body_convex α j.1 z a p.index-
    β z*intrinsicHessian d.coordinate_body_convex α j.1 z p.index p.index| ≤ B*W+p.bound₁*G
  rw [hxval]
  exact habs.trans (add_le_add hcoord herror)

end SmoothInnerDomain
end GaussianTilt.MomentMapRegularity
