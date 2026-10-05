import GaussianTilt.MomentMapRegularTargets

/-!
# Local coercivity for the moment-measure variational construction

For a target density bounded below on a ball, the integral of a nonnegative
convex dual potential controls its value at the center. The proof uses the
actual ball-reflection change of variables and midpoint convexity. Uniform
bounds on inner balls then give explicit equi-Lipschitz bounds, supplying the
local compactness input to the direct method.

These are proved variational estimates, not a postulated moment-map theorem.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
namespace GaussianTilt.MomentMapCoercivity
variable {n : ℕ}
abbrev E (n : ℕ) := Reference.Space n

def reflection (x y : E n) : E n := (2 : ℝ) • x - y

lemma reflection_dist (x y : E n) : dist (reflection x y) x = dist y x := by
  simp only [reflection, dist_eq_norm]
  rw [show (2 : ℝ) • x - y - x = -(y - x) by module, norm_neg]

lemma reflection_preimage_ball (x : E n) (r : ℝ) :
    reflection x ⁻¹' Metric.ball x r = Metric.ball x r := by
  ext y
  simp only [mem_preimage, Metric.mem_ball, reflection_dist]

lemma reflection_measurePreserving (x : E n) : MeasurePreserving (reflection x) := by
  convert (measurePreserving_add_left (volume : Measure (E n)) ((2 : ℝ) • x)).comp
    (Measure.measurePreserving_neg volume) using 1

lemma reflection_measurableEmbedding (x : E n) : MeasurableEmbedding (reflection x) := by
  have he : reflection x = (Homeomorph.neg (E n)).trans (Homeomorph.addLeft ((2 : ℝ) • x)) := by
    funext y
    rfl
  rw [he]
  exact Homeomorph.measurableEmbedding _

theorem integral_reflection_ball (x : E n) (r : ℝ) (u : E n → ℝ) :
    (∫ y in Metric.ball x r, u (reflection x y)) = ∫ y in Metric.ball x r, u y := by
  have h := (reflection_measurePreserving x).restrict_preimage
    (s := Metric.ball x r) Metric.isOpen_ball.measurableSet
  rw [reflection_preimage_ball] at h
  exact h.integral_comp (reflection_measurableEmbedding x) u

/-- The symmetric-ball Jensen estimate, including its boundary justification
from compact integrability of the continuous convex potential. -/
theorem convex_ball_mean_lower_bound {u : E n → ℝ} (hu : Continuous u)
    (hc : ConvexOn ℝ univ u) (x : E n) (r : ℝ) :
    (volume (Metric.ball x r)).toReal * u x ≤ ∫ y in Metric.ball x r, u y := by
  letI : IsFiniteMeasure (volume.restrict (Metric.ball x r)) := ⟨by
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact (measure_mono Metric.ball_subset_closedBall).trans_lt (isCompact_closedBall x r).measure_lt_top⟩
  have hi : IntegrableOn u (Metric.ball x r) :=
    (hu.continuousOn.integrableOn_compact (isCompact_closedBall x r)).mono_set Metric.ball_subset_closedBall
  have hri : IntegrableOn (fun y => u (reflection x y)) (Metric.ball x r) := by
    have h := (reflection_measurePreserving x).restrict_preimage
      (s := Metric.ball x r) Metric.isOpen_ball.measurableSet
    rw [reflection_preimage_ball] at h
    exact (h.integrable_comp_emb (reflection_measurableEmbedding x)).mpr hi
  have hmid (y : E n) : 2 * u x ≤ u y + u (reflection x y) := by
    have h := hc.2 (mem_univ y) (mem_univ (reflection x y))
      (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num)
    have he : (1 / 2 : ℝ) • y + (1 / 2 : ℝ) • reflection x y = x := by
      unfold reflection
      module
    rw [he] at h
    simp only [smul_eq_mul] at h
    linarith
  have h := integral_mono_ae (μ := volume.restrict (Metric.ball x r))
    (integrable_const (2 * u x)) (hi.add hri) (ae_of_all _ hmid)
  simp only [Pi.add_apply] at h
  rw [integral_add hi hri, integral_reflection_ball, integral_const,
    smul_eq_mul, measureReal_restrict_apply_univ, measureReal_def] at h
  linarith

/-- Local lower density bounds give the pointwise control needed for
compactness of a normalized variational sequence. -/
theorem convex_value_le_weighted_integral {u q : E n → ℝ}
    (hu : Continuous u) (hc : ConvexOn ℝ univ u) (hu0 : ∀ y, 0 ≤ u y)
    (hq0 : ∀ y, 0 ≤ q y) (hi : Integrable (fun y => q y * u y))
    {x : E n} {r c : ℝ} (hc0 : 0 < c) (hr : 0 < r)
    (hqlower : ∀ y ∈ Metric.ball x r, c ≤ q y) :
    u x ≤ (∫ y, q y * u y) / (c * (volume (Metric.ball x r)).toReal) := by
  have hbpos : 0 < volume (Metric.ball x r) :=
    Metric.isOpen_ball.measure_pos volume ⟨x, Metric.mem_ball_self hr⟩
  have hbfin : volume (Metric.ball x r) ≠ ⊤ :=
    ne_top_of_le_ne_top (isCompact_closedBall x r).measure_ne_top
      (measure_mono Metric.ball_subset_closedBall)
  have hb : 0 < (volume (Metric.ball x r)).toReal := ENNReal.toReal_pos hbpos.ne' hbfin
  apply (le_div_iff₀ (mul_pos hc0 hb)).mpr
  have hui : IntegrableOn u (Metric.ball x r) :=
    (hu.continuousOn.integrableOn_compact (isCompact_closedBall x r)).mono_set Metric.ball_subset_closedBall
  have hcomp : c * (∫ y in Metric.ball x r, u y) ≤
      ∫ y in Metric.ball x r, q y * u y := by
    rw [← integral_const_mul]
    apply integral_mono_ae (hui.const_mul c) hi.integrableOn
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with y hy
    exact mul_le_mul_of_nonneg_right (hqlower y hy) (hu0 y)
  have hwhole : (∫ y in Metric.ball x r, q y * u y) ≤ ∫ y, q y * u y :=
    setIntegral_le_integral hi (ae_of_all _ (fun y => mul_nonneg (hq0 y) (hu0 y)))
  have hmean := mul_le_mul_of_nonneg_left (convex_ball_mean_lower_bound hu hc x r) hc0.le
  nlinarith

/-- A uniform weighted-integral bound gives a uniform bound throughout an
inner ball. Constants depend only on the target density and the two balls. -/
theorem convex_inner_ball_bound {u q : E n → ℝ}
    (hu : Continuous u) (hc : ConvexOn ℝ univ u) (hu0 : ∀ y, 0 ≤ u y)
    (hq0 : ∀ y, 0 ≤ q y) (hi : Integrable (fun y => q y * u y))
    {r c M : ℝ} (hc0 : 0 < c) (hr : 0 < r)
    (hqlower : ∀ y ∈ Metric.ball (0 : E n) (3 * r), c ≤ q y)
    (hM : (∫ y, q y * u y) ≤ M) :
    ∀ x ∈ Metric.ball (0 : E n) (2 * r),
      |u x| ≤ M / (c * (volume (Metric.ball (0 : E n) r)).toReal) := by
  intro x hx
  have hbpos : 0 < volume (Metric.ball (0 : E n) r) :=
    Metric.isOpen_ball.measure_pos volume ⟨0, Metric.mem_ball_self hr⟩
  have hq : ∀ y ∈ Metric.ball x r, c ≤ q y := by
    intro y hy
    apply hqlower
    simp only [Metric.mem_ball, dist_zero_right] at hx ⊢
    have hd : ‖y - x‖ < r := by simpa only [Metric.mem_ball, dist_eq_norm] using hy
    calc
      ‖y‖ = ‖(y - x) + x‖ := by congr 1; abel
      _ ≤ ‖y - x‖ + ‖x‖ := norm_add_le _ _
      _ < 3 * r := by linarith
  rw [abs_of_nonneg (hu0 x)]
  have hv := convex_value_le_weighted_integral hu hc hu0 hq0 hi hc0 hr hq
  rw [Measure.addHaar_ball_center volume x r] at hv
  exact hv.trans (div_le_div_of_nonneg_right hM (by positivity))

/-- Explicit local equi-Lipschitz control from the target-weighted integral.
This is the local compactness estimate used in the direct variational method. -/
theorem convex_inner_ball_lipschitz {u q : E n → ℝ}
    (hu : Continuous u) (hc : ConvexOn ℝ univ u) (hu0 : ∀ y, 0 ≤ u y)
    (hq0 : ∀ y, 0 ≤ q y) (hi : Integrable (fun y => q y * u y))
    {r c M : ℝ} (hc0 : 0 < c) (hr : 0 < r)
    (hqlower : ∀ y ∈ Metric.ball (0 : E n) (3 * r), c ≤ q y)
    (hM : (∫ y, q y * u y) ≤ M) :
    LipschitzOnWith
      (2 * (M / (c * (volume (Metric.ball (0 : E n) r)).toReal)) / r).toNNReal
      u (Metric.ball (0 : E n) r) := by
  have huc : ConvexOn ℝ (Metric.ball (0 : E n) (2 * r)) u :=
    hc.subset (subset_univ _) (convex_ball _ _)
  have h := huc.lipschitzOnWith_of_abs_le hr
    (convex_inner_ball_bound hu hc hu0 hq0 hi hc0 hr hqlower hM)
  simpa only [show 2 * r - r = r by ring] using h

end GaussianTilt.MomentMapCoercivity
