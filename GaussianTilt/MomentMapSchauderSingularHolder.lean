import GaussianTilt.MomentMapSchauderSingularCancellation

/-!
# A proved Hölder estimate for actual compensated singular integrals

The proof splits into two small balls, a genuinely integrable far-field
kernel difference, and the displaced cancellation error. The constants are
actual finite radial integrals. No singular-integral Hölder theorem or
elliptic regularity estimate is supplied as a hypothesis.
-/
noncomputable section
open MeasureTheory Set Filter Module
open scoped ENNReal Topology
namespace GaussianTilt.MomentMapSchauder
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

def compensatedSingularIntegral (μ : Measure E) (K f : E → ℝ) (x : E) : ℝ :=
  ∫ z, K (x - z) * (f z - f x) ∂μ

def singularHolderConstant (μ : Measure E) (M L α : ℝ) : ℝ :=
  M * ((2 : ℝ) ^ α + (3 : ℝ) ^ α) *
      (∫ z in Metric.closedBall (0 : E) 1, ‖z‖ ^ (α - (finrank ℝ E : ℝ)) ∂μ) +
    L * (2 : ℝ) ^ (α - 1) *
      (∫ z in (Metric.closedBall (0 : E) 1)ᶜ, ‖z‖ ^ (α - (finrank ℝ E : ℝ) - 1) ∂μ) +
    M * (2 : ℝ) ^ finrank ℝ E * μ.real (Metric.ball (0 : E) 1)

set_option maxHeartbeats 1000000 in
/-- Genuine Calderón--Zygmund Hölder estimate for a compensated kernel.
Kernel size, separated-point smoothness, and actual tail cancellation are
the hypotheses. Compact radial cutoffs of the Newtonian Hessian satisfy them.
The two displayed integrability assumptions are ordinary Bochner
integrability, not an analytic estimate or an assumed principal value. -/
theorem compensatedSingularIntegral_holder_bound {K f : E → ℝ} {M L H α : ℝ}
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hH : 0 ≤ H)
    (hα : 0 < α) (hα1 : α < 1) (hαn : α < (finrank ℝ E : ℝ))
    (hK : ∀ z ≠ 0, |K z| ≤ M * ‖z‖ ^ (-(finrank ℝ E : ℝ)))
    (hKdiff : ∀ a b : E, a ≠ 0 → ‖a - b‖ ≤ ‖a‖ / 2 →
      |K a - K b| ≤ L * ‖a - b‖ * ‖a‖ ^ (-(finrank ℝ E : ℝ) - 1))
    (hf : ∀ x y, |f x - f y| ≤ H * ‖x - y‖ ^ α)
    (hcomp : ∀ x, Integrable (fun z => K (x - z) * (f z - f x)) μ)
    (htail : ∀ r : ℝ, 0 < r → IntegrableOn K (Metric.closedBall (0 : E) r)ᶜ μ)
    (hcancel : ∀ r : ℝ, 0 < r → ∫ z in (Metric.closedBall (0 : E) r)ᶜ, K z ∂μ = 0)
    (x y : E) :
    |compensatedSingularIntegral μ K f x - compensatedSingularIntegral μ K f y| ≤
      singularHolderConstant μ M L α * H * ‖x - y‖ ^ α := by
  by_cases hxy : x = y
  · subst y
    simp only [sub_self, abs_zero, norm_zero, Real.zero_rpow hα.ne', mul_zero, le_refl]
  let d : ℝ := ‖x - y‖
  have hd : 0 < d := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  let S : Set E := Metric.closedBall x (2 * d)
  let Fx : E → ℝ := fun z => K (x - z) * (f z - f x)
  let Fy : E → ℝ := fun z => K (y - z) * (f z - f y)
  let Fd : E → ℝ := fun z => (K (x - z) - K (y - z)) * (f z - f x)
  let G : E → ℝ := fun z => K (y - z) * (f y - f x)
  have hsub : Sᶜ ⊆ (Metric.closedBall y d)ᶜ := outside_doubleBall_subset_outside_displacedBall x y
  have hiKy : IntegrableOn (fun z => K (y - z)) Sᶜ μ :=
    IntegrableOn.mono_set ((integrableOn_center_sub_outside_closedBall_iff (μ := μ) K y d).mpr
      (htail d hd)) hsub
  have hiG : IntegrableOn G Sᶜ μ := hiKy.mul_const _
  have hiFx : IntegrableOn Fx Sᶜ μ := (hcomp x).integrableOn
  have hiFy : IntegrableOn Fy Sᶜ μ := (hcomp y).integrableOn
  have hefun : (fun z => Fx z - Fy z - G z) = Fd := by
    funext z
    dsimp [Fx, Fy, Fd, G]
    ring
  have hiFd : IntegrableOn Fd Sᶜ μ := by
    have hh := (hiFx.sub hiFy).sub hiG
    change Integrable (fun z => Fx z - Fy z - G z) (μ.restrict Sᶜ) at hh
    rwa [hefun] at hh
  have hfar : (∫ z in Sᶜ, Fx z ∂μ) - (∫ z in Sᶜ, Fy z ∂μ) =
      (∫ z in Sᶜ, Fd z ∂μ) + (f y - f x) * ∫ z in Sᶜ, K (y - z) ∂μ := by
    rw [← integral_sub hiFx hiFy]
    have hh : (fun z => Fx z - Fy z) = (fun z => Fd z + G z) := by
      funext z
      dsimp [Fx, Fy, Fd, G]
      ring
    rw [hh, integral_add hiFd hiG]
    dsimp only [G]
    rw [integral_mul_const, mul_comm]
  have hsplitx := integral_add_compl (s := S) measurableSet_closedBall (hcomp x)
  have hsplity := integral_add_compl (s := S) measurableSet_closedBall (hcomp y)
  have hsplit : compensatedSingularIntegral μ K f x - compensatedSingularIntegral μ K f y =
      (∫ z in S, Fx z ∂μ) - (∫ z in S, Fy z ∂μ) + (∫ z in Sᶜ, Fd z ∂μ) +
        (f y - f x) * ∫ z in Sᶜ, K (y - z) ∂μ := by
    change (∫ z, Fx z ∂μ) - (∫ z, Fy z ∂μ) = _
    change (∫ z in S, Fx z ∂μ) + (∫ z in Sᶜ, Fx z ∂μ) = _ at hsplitx
    change (∫ z in S, Fy z ∂μ) + (∫ z in Sᶜ, Fy z ∂μ) = _ at hsplity
    linarith
  let I : ℝ := ∫ z in Metric.closedBall (0 : E) 1, ‖z‖ ^ (α - (finrank ℝ E : ℝ)) ∂μ
  let J : ℝ := ∫ z in (Metric.closedBall (0 : E) 1)ᶜ, ‖z‖ ^ (α - (finrank ℝ E : ℝ) - 1) ∂μ
  let B : ℝ := M * (2 : ℝ) ^ finrank ℝ E * μ.real (Metric.ball (0 : E) 1)
  have hNx : |∫ z in S, Fx z ∂μ| ≤ (M * H) * ((2 * d) ^ α * I) :=
    compensated_kernel_near_bound hM hH hα hαn hK hf x (by positivity)
  have hNy : |∫ z in S, Fy z ∂μ| ≤ (M * H) * ((3 * d) ^ α * I) := by
    apply compensated_kernel_near_subset_bound hM hH hα hαn hK hf y (by positivity)
    apply Metric.closedBall_subset_closedBall'
    change 2 * d + dist x y ≤ 3 * d
    rw [dist_eq_norm]
    change 2 * d + d ≤ 3 * d
    linarith
  have hF : |∫ z in Sᶜ, Fd z ∂μ| ≤ (L * H * d) * ((2 * d) ^ (α - 1) * J) :=
    kernel_difference_far_bound hL hH hα1 hKdiff hf x y (by positivity) le_rfl
  have hB : |(f y - f x) * ∫ z in Sᶜ, K (y - z) ∂μ| ≤ H * d ^ α * B := by
    rw [abs_mul]
    apply mul_le_mul _ (displaced_kernel_tail_bound hM hK htail hcancel hxy)
      (abs_nonneg _) (by positivity)
    simpa only [d, norm_sub_rev] using hf y x
  have hdpow : d * d ^ (α - 1) = d ^ α := by
    calc
      _ = d ^ (1 : ℝ) * d ^ (α - 1) := by rw [Real.rpow_one]
      _ = d ^ (1 + (α - 1)) := (Real.rpow_add hd _ _).symm
      _ = _ := by congr 1; ring
  have hFscale : (L * H * d) * ((2 * d) ^ (α - 1) * J) =
      (L * H * (2 : ℝ) ^ (α - 1) * J) * d ^ α := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hd.le]
    calc
      _ = (L * H * (2 : ℝ) ^ (α - 1) * J) * (d * d ^ (α - 1)) := by ring
      _ = _ := by rw [hdpow]
  rw [hsplit]
  calc
    _ ≤ |∫ z in S, Fx z ∂μ| + |∫ z in S, Fy z ∂μ| + |∫ z in Sᶜ, Fd z ∂μ| +
        |(f y - f x) * ∫ z in Sᶜ, K (y - z) ∂μ| := by
      apply (abs_add_le _ _).trans
      apply add_le_add_right
      apply (abs_add_le _ _).trans
      exact add_le_add_right (abs_sub _ _) _
    _ ≤ (M * H) * ((2 * d) ^ α * I) + (M * H) * ((3 * d) ^ α * I) +
        (L * H * d) * ((2 * d) ^ (α - 1) * J) + H * d ^ α * B :=
      add_le_add (add_le_add (add_le_add hNx hNy) hF) hB
    _ = _ := by
      rw [hFscale, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hd.le,
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hd.le]
      dsimp [singularHolderConstant, I, J, B, d]
      ring

end GaussianTilt.MomentMapSchauder
