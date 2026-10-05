import GaussianTilt.MomentMapRegularityReferenceThirdNorm
import GaussianTilt.MomentMapRegularityReferenceNormalized
import GaussianTilt.MomentMapClassicalDirichletGeometryCoordinates
import GaussianTilt.MomentMapSchauderHessianInterpolation

/-! # Actual uniformly controlled quadratic approximations of the references -/
noncomputable section
open Set Filter MeasureTheory Matrix
open scoped Topology ContDiff Gradient BigOperators
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin GaussianTilt.MomentMapSchauder
variable {n : ℕ}
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxSize 1000

lemma coordinatePullback_fderiv_apply {u : E n → ℝ} (hu : Differentiable ℝ u)
    (x h : E n) : fderiv ℝ (coordinatePullback u) (coordinateEquiv n x) (coordinateEquiv n h) =
      fderiv ℝ u x h := by
  change fderiv ℝ (u ∘ (coordinateEquiv n).symm) (coordinateEquiv n x) (coordinateEquiv n h) = _
  rw [fderiv_comp _ (hu _) (coordinateEquiv n).symm.differentiableAt,
    (coordinateEquiv n).symm.fderiv]
  simp

lemma coordinateEquiv_norm_le (h : E n) : ‖coordinateEquiv n h‖ ≤ ‖h‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  exact PiLp.norm_apply_le h i

/-- Coordinate Calabi bounds imply a true Euclidean cubic Taylor remainder. -/
lemma euclidean_taylor_of_coordinateThird_bound {u : E n → ℝ} (hu : ContDiff ℝ 3 u)
    {K : Set (E n)} (hK : Convex ℝ K) {B : ℝ} (hB : 0 ≤ B)
    (hthird : ∀ y ∈ K, ∀ i j k,
      |coordinateThirdDerivative (coordinatePullback u) (coordinateEquiv n y) i j k| ≤ B)
    {x h : E n} (hx : x ∈ K) (hxh : x+h ∈ K) :
    |u (x+h)-u x-fderiv ℝ u x h-(1/2 : ℝ)*fderiv ℝ (fderiv ℝ u) x h h| ≤
      ((n : ℝ)^3*B/2)*‖h‖^3 := by
  let e := coordinateEquiv n
  have hraw : ContDiff ℝ 3 (coordinatePullback u) := contDiff_coordinatePullback hu
  have hb : ∀ y ∈ e '' K, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (coordinatePullback u))) y‖ ≤ (n : ℝ)^3*B := by
    rintro y ⟨z,hz,rfl⟩
    exact thirdFrechet_norm_le_coordinate_bound hraw.contDiffAt hB (hthird z hz)
  have hh := local_taylor_quadratic_remainder_of_third_bound (hK.linear_image e.toLinearMap)
    (fun y _ => hraw.contDiffAt) (by positivity : 0 ≤ (n : ℝ)^3*B) hb
    (show e x ∈ e '' K from ⟨x,hx,rfl⟩)
    (show e x+e h ∈ e '' K from ⟨x+h,hxh,by simp⟩)
  rw [coordinatePullback_fderiv_apply (hu.differentiable (by norm_num)),
    secondFDeriv_coordinatePullback (hu.of_le (by norm_num))] at hh
  simp only [coordinatePullback,Function.comp_apply,map_add,e.symm_apply_apply] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (coordinateEquiv_norm_le h) 3) (by positivity))

def referenceTaylorConstant (n : ℕ) (r R : ℝ) : ℝ := (n : ℝ)^3 * max (referenceThirdBound n r R) 0 / 2

lemma referenceTaylorConstant_nonneg (n : ℕ) (r R : ℝ) : 0 ≤ referenceTaylorConstant n r R := by
  unfold referenceTaylorConstant
  positivity

/-- Every actual smooth constant-density reference on a body between two
balls has real symmetric quadratic jets, with a uniform cubic remainder on
the smaller ball. The cutoff extension and C³ estimate are derived inside
the proof; no Taylor or derivative bound is assumed. -/
theorem smooth_reference_quadratic_approximation [NeZero n]
    {u : E n → ℝ} (huc : Continuous u) {S : Set (E n)} (hS : IsCompact S)
    (hu : ContDiffOn ℝ ∞ u (interior S)) (hc : ConvexOn ℝ S u)
    (hb : ∀ y ∈ frontier S, u y = 0)
    (huid : ∀ A, IsCompact A → A ⊆ interior S → volume (subgradientImageOn S u A) = volume A)
    (hH : ∀ y ∈ interior S, (coordinateHessian (coordinatePullback u) (coordinateEquiv n y)).PosDef)
    (hMA : ∀ y ∈ interior S, (coordinateHessian (coordinatePullback u) (coordinateEquiv n y)).det = 1)
    {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hSR : S ⊆ Metric.closedBall 0 R)
    (hrS : Metric.closedBall (0 : E n) r ⊆ interior S) :
    ∀ x ∈ Metric.closedBall (0 : E n) (r/4), ∃ p : E n, ∃ H : E n →L[ℝ] E n,
      (∀ v w, inner ℝ (H v) w = inner ℝ v (H w)) ∧
      ∀ h : E n, ‖h‖ ≤ r/4 →
        |u (x+h)-quadraticJet (u x) p 0 H h| ≤ referenceTaylorConstant n r R * ‖h‖^3 := by
  let K := Metric.closedBall (0 : E n) (r/2)
  have hKS : K ⊆ interior S :=
    (Metric.closedBall_subset_closedBall (half_le_self hr.le)).trans hrS
  obtain ⟨v,hv,hveq⟩ := exists_global_smooth_eq_near_compact isOpen_interior hu (isCompact_closedBall _ _) hKS
  have he (x : E n) (hx : x ∈ K) : v x = u x := (hveq x hx).self_of_nhds
  have hthird := (smooth_reference_derivative_bounds_on_half_ball huc hS hu hc hb huid hH hMA hr hR hSR hrS).2
  have hvthird : ∀ x ∈ K, ∀ i j k,
      |coordinateThirdDerivative (coordinatePullback v) (coordinateEquiv n x) i j k| ≤ max (referenceThirdBound n r R) 0 := by
    intro x hx i j k
    have ht : Tendsto (coordinateEquiv n).symm (𝓝 (coordinateEquiv n x)) (𝓝 x) := by
      simpa only [ContinuousAt,(coordinateEquiv n).symm_apply_apply] using
        (coordinateEquiv n).symm.continuous.continuousAt (x:=coordinateEquiv n x)
    have hraw : coordinatePullback v =ᶠ[𝓝 (coordinateEquiv n x)] coordinatePullback u := (hveq x hx).comp_tendsto ht
    rw [coordinateThirdDerivative_congr_nhds hraw]
    exact (hthird x hx i j k).trans (le_max_left _ _)
  intro x hx
  have hxnorm : ‖x‖ ≤ r/4 := by simpa using hx
  have hxK : x ∈ K := Metric.closedBall_subset_closedBall (by linarith) hx
  refine ⟨gradient v x,frechetHessian v x,frechetHessian_symmetric (contDiff_infty.mp hv 2) x,?_⟩
  intro h hh
  have hxh : x+h ∈ K := by
    rw [Metric.mem_closedBall,dist_zero_right]
    exact (norm_add_le x h).trans (by linarith)
  have ht := euclidean_taylor_of_coordinateThird_bound (contDiff_infty.mp hv 3) (convex_closedBall _ _)
    (le_max_right _ _) hvthird hxK hxh
  rw [he (x+h) hxh,he x hxK] at ht
  convert ht using 1
  unfold quadraticJet
  simp only [sub_zero,inner_gradient_eq_fderiv,inner_frechetHessian]
  ring

end GaussianTilt.MomentMapRegularity
