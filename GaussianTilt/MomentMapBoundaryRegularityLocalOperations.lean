import GaussianTilt.MomentMapBoundaryRegularityLocalSystem
import GaussianTilt.MomentMapBoundaryRegularityFlatSystem

/-! # Actual local equation covariance, without smooth extension across the boundary -/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

lemma LocalFlatEllipticSystem.contDiffAt_u {j : Fin n} {u f : CoordinateSpace n → ℝ}
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {lam Λ K M : ℝ}
    (h : LocalFlatEllipticSystem j u f A lam Λ K M) {y : CoordinateSpace n}
    (hy : y ∈ flatHalfBall j) : ContDiffAt ℝ ∞ u y :=
  h.smooth_interior.contDiffAt ((isOpen_flatHalfBall j).mem_nhds hy)

lemma LocalFlatEllipticSystem.contDiffAt_f {j : Fin n} {u f : CoordinateSpace n → ℝ}
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {lam Λ K M : ℝ}
    (h : LocalFlatEllipticSystem j u f A lam Λ K M) {y : CoordinateSpace n}
    (hy : y ∈ flatHalfBall j) : ContDiffAt ℝ ∞ f y :=
  h.forcing_smooth.contDiffAt ((isOpen_flatHalfBall j).mem_nhds hy)

lemma LocalFlatEllipticSystem.mono_forcing {j : Fin n} {u f : CoordinateSpace n → ℝ}
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {lam Λ K M M' : ℝ}
    (h : LocalFlatEllipticSystem j u f A lam Λ K M) (hMM : M ≤ M') :
    LocalFlatEllipticSystem j u f A lam Λ K M' :=
  { h with
    forcing_bound := fun y hy => (h.forcing_bound y hy).trans hMM
    forcing_derivative_bound := fun y hy k => (h.forcing_derivative_bound y hy k).trans hMM }

lemma LocalFlatEllipticSystem.affine_shift_scale {j : Fin n} {u f : CoordinateSpace n → ℝ}
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {lam Λ K M : ℝ}
    (h : LocalFlatEllipticSystem j u f A lam Λ K M) (c p : ℝ) :
    LocalFlatEllipticSystem j (fun y => c*(u y-p*y j)) (fun y => c*f y) A lam Λ K (|c| * M) := by
  have hcoord : ContDiff ℝ ∞ (fun y : CoordinateSpace n => y j) := by fun_prop
  refine ⟨continuousOn_const.mul (h.continuous_boundary.sub (continuousOn_const.mul hcoord.continuous.continuousOn)),
    contDiffOn_const.mul (h.smooth_interior.sub (contDiffOn_const.mul hcoord.contDiffOn)),
    contDiffOn_const.mul h.forcing_smooth,h.coefficient_smooth,h.positive,h.elliptic,h.coefficient_bound,?_,?_,?_⟩
  · intro y hy
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (h.forcing_bound y hy) (abs_nonneg _)
  · intro y hy k
    rw [coordinateDerivative_const_mul_at ((h.contDiffAt_f hy).differentiableAt (by simp)),abs_mul]
    have hh := mul_le_mul_of_nonneg_left (h.forcing_derivative_bound y hy k) (abs_nonneg c)
    nlinarith
  · intro y hy
    have hu : ContDiffAt ℝ 2 u y := contDiffAt_infty.mp (h.contDiffAt_u hy) 2
    have hl : ContDiffAt ℝ 2 (fun z : CoordinateSpace n => z j) y :=
      (contDiff_infty.mp hcoord 2).contDiffAt
    have hsub : ContDiffAt ℝ 2 (fun z => u z-p*z j) y := hu.sub (contDiffAt_const.mul hl)
    rw [linearizedMA_const_mul_at _ hsub,linearizedMA_sub_at _ hu (contDiffAt_const.mul hl),
      linearizedMA_const_mul_at _ hl]
    have hz : linearizedMA (A y) (fun z => z j) y=0 := by
      simp only [linearizedMA,coordinateHessian_coordinate,Matrix.mul_zero,Matrix.trace_zero]
    rw [hz,mul_zero,sub_zero,h.equation y hy]

lemma coordinateDerivative_dilation_at {v : CoordinateSpace n → ℝ} {r : ℝ}
    {x : CoordinateSpace n} (hv : DifferentiableAt ℝ v (r • x)) (i : Fin n) :
    coordinateDerivative i (fun y => v (r • y)) x = r*coordinateDerivative i v (r • x) := by
  have hd : HasFDerivAt (fun y : CoordinateSpace n => r • y)
      (r • ContinuousLinearMap.id ℝ (CoordinateSpace n)) x := (hasFDerivAt_id x).const_smul r
  have hc := (hv.hasFDerivAt.comp x hd).fderiv
  simp only [Function.comp_def] at hc
  unfold coordinateDerivative
  rw [hc]
  simp

lemma coordinateHessian_dilation_on {v : CoordinateSpace n → ℝ} {U : Set (CoordinateSpace n)}
    (hU : IsOpen U) (hv : ContDiffOn ℝ ∞ v U) {r : ℝ} {x : CoordinateSpace n} (hx : r • x ∈ U) :
    coordinateHessian (fun y => v (r • y)) x=r^2 • coordinateHessian v (r • x) := by
  obtain ⟨w,hw,he⟩ := exists_global_smooth_eq_near_compact_coordinate hU hv (isCompact_singleton)
    (show {r • x} ⊆ U from singleton_subset_iff.mpr hx)
  have heq := he (r • x) (mem_singleton _)
  have hp : (fun y => w (r • y)) =ᶠ[𝓝 x] (fun y => v (r • y)) :=
    (show ContinuousAt (fun y : CoordinateSpace n => r • y) x by fun_prop).tendsto.eventually heq
  rw [← coordinateHessian_congr_nhds hp,← coordinateHessian_congr_nhds heq]
  simpa only [ellipticRescalePoint,zero_add] using coordinateHessian_ellipticRescale hw 0 r x

lemma LocalFlatEllipticSystem.rescale {j : Fin n} {u f : CoordinateSpace n → ℝ}
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {lam Λ K M r : ℝ}
    (h : LocalFlatEllipticSystem j u f A lam Λ K M) (hr : 0 < r) (hr1 : r ≤ 1) :
    LocalFlatEllipticSystem j (flatRescaledSolution u r) (flatRescaledForcing f r)
      (fun y => A (r • y)) lam Λ K (r*M) := by
  have hscale : ContDiff ℝ ∞ (fun y : CoordinateSpace n => r • y) := contDiff_const.smul contDiff_id
  have hs (y : CoordinateSpace n) (hy : y ∈ flatHalfBall j) : r • y ∈ flatHalfBall j := by
    constructor
    · rw [norm_coordinate_dilation,abs_of_pos hr]
      nlinarith [mul_lt_mul_of_pos_left hy.1 hr]
    · change 0 < r*y j
      exact mul_pos hr hy.2
  have hc (y : CoordinateSpace n) (hy : y ∈ flatClosedHalfBall j) : r • y ∈ flatClosedHalfBall j := by
    constructor
    · rw [norm_coordinate_dilation,abs_of_pos hr]
      nlinarith [mul_le_mul_of_nonneg_left hy.1 hr.le]
    · change 0 ≤ r*y j
      exact mul_nonneg hr.le hy.2
  refine ⟨continuousOn_const.mul (h.continuous_boundary.comp hscale.continuous.continuousOn hc),
    contDiffOn_const.mul (h.smooth_interior.comp hscale.contDiffOn hs),
    contDiffOn_const.mul (h.forcing_smooth.comp hscale.contDiffOn hs),
    fun a b => (h.coefficient_smooth a b).comp hscale.contDiffOn hs,
    fun y hy => h.positive _ (hs y hy),fun y hy => h.elliptic _ (hs y hy),?_,?_,?_,?_⟩
  · intro y hy k a b
    have hAd := (h.coefficient_smooth a b).contDiffAt ((isOpen_flatHalfBall j).mem_nhds (hs y hy))
    change y j*|coordinateDerivative k (fun z => A (r • z) a b) y| ≤ K
    rw [coordinateDerivative_dilation_at (hAd.differentiableAt (by simp)),abs_mul,abs_of_pos hr]
    have hh := h.coefficient_bound (r • y) (hs y hy) k a b
    change (r*y j)*|coordinateDerivative k (fun z => A z a b) (r • y)| ≤ K at hh
    nlinarith
  · intro y hy
    change |r*f (r • y)| ≤ r*M
    rw [abs_mul,abs_of_pos hr]
    exact mul_le_mul_of_nonneg_left (h.forcing_bound _ (hs y hy)) hr.le
  · intro y hy k
    have hfd := (h.contDiffAt_f (hs y hy)).differentiableAt (by simp)
    have hfdp : DifferentiableAt ℝ (fun z => f (r • z)) y := hfd.comp y (hscale.differentiable (by simp) y)
    change y j*|coordinateDerivative k (fun z => r*f (r • z)) y| ≤ r*M
    rw [coordinateDerivative_const_mul_at hfdp,coordinateDerivative_dilation_at hfd,
      abs_mul,abs_mul,abs_of_pos hr]
    have hh := mul_le_mul_of_nonneg_left (h.forcing_derivative_bound _ (hs y hy) k) hr.le
    change r*((r*y j)*|coordinateDerivative k f (r • y)|) ≤ r*M at hh
    nlinarith
  · intro y hy
    have hud := h.contDiffAt_u (hs y hy)
    have hup : ContDiffAt ℝ 2 (fun z => u (r • z)) y :=
      (contDiffAt_infty.mp hud 2).comp y (contDiff_infty.mp hscale 2).contDiffAt
    change linearizedMA (A (r • y)) (fun z => r⁻¹*u (r • z)) y=r*f (r • y)
    rw [linearizedMA_const_mul_at _ hup]
    have hl : linearizedMA (A (r • y)) (fun z => u (r • z)) y=r^2*linearizedMA (A (r • y)) u (r • y) := by
      simp only [linearizedMA,coordinateHessian_dilation_on (isOpen_flatHalfBall j) h.smooth_interior (hs y hy),
        Matrix.mul_smul,Matrix.trace_smul,smul_eq_mul]
    rw [hl,h.equation _ (hs y hy)]
    field_simp

end GaussianTilt.MomentMapRegularity
