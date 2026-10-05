import GaussianTilt.MomentMapRegularityGeometry
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Convolution

/-! # Smooth strongly convex defining functions

We mollify the actual Minkowski gauge of a convex body and add a small
quadratic. This constructs smooth strongly convex defining functions with
quantitative approximation estimates; no Monge--Ampère solvability is used.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal Convolution ContDiff
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

lemma convexOn_gauge_univ {S : Set (E n)} (hc : Convex ℝ S) (h0 : S ∈ 𝓝 0) :
    ConvexOn ℝ univ (gauge S) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simpa only [gauge_smul_of_nonneg ha, gauge_smul_of_nonneg hb] using
    gauge_add_le hc (absorbent_nhds_zero h0) (a • x) (b • y)

/-- A normalized compactly supported smooth kernel of radius `ε`. -/
def definingBump (ε : ℝ) (hε : 0 < ε) : ContDiffBump (0 : E n) where
  rIn := ε / 2
  rOut := ε
  rIn_pos := half_pos hε
  rIn_lt_rOut := half_lt_self hε

/-- Actual scalar convolution with the normalized bump. -/
def smoothConvexAverage (f : E n → ℝ) (ε : ℝ) (hε : 0 < ε) (x : E n) : ℝ :=
  ∫ y, (definingBump ε hε).normed volume y * f (x - y)

lemma integrable_smoothConvexAverage {f : E n → ℝ} (hf : Continuous f)
    {ε : ℝ} (hε : 0 < ε) (x : E n) :
    Integrable (fun y => (definingBump ε hε).normed volume y * f (x-y)) := by
  exact ((definingBump ε hε).continuous_normed.mul
    (hf.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      (definingBump ε hε).hasCompactSupport_normed.mul_right

lemma contDiff_smoothConvexAverage {f : E n → ℝ} (hf : Continuous f)
    {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ ∞ (smoothConvexAverage f ε hε) := by
  exact (definingBump ε hε).hasCompactSupport_normed.contDiff_convolution_left
    (ContinuousLinearMap.mul ℝ ℝ) (definingBump ε hε).contDiff_normed hf.locallyIntegrable

lemma convexOn_smoothConvexAverage {f : E n → ℝ} (hf : Continuous f)
    (hc : ConvexOn ℝ univ f) {ε : ℝ} (hε : 0 < ε) :
    ConvexOn ℝ univ (smoothConvexAverage f ε hε) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ z _ a b ha hb hab
  have hxy (y : E n) : a • x + b • z - y = a • (x-y) + b • (z-y) := by
    have hb' : b = 1 - a := by linarith
    rw [hb']
    module
  have hint := integral_mono (integrable_smoothConvexAverage hf hε (a • x+b • z))
    (((integrable_smoothConvexAverage hf hε x).const_mul a).add
      ((integrable_smoothConvexAverage hf hε z).const_mul b)) (fun y => by
        rw [hxy]
        have h := mul_le_mul_of_nonneg_left
          (hc.2 (mem_univ (x-y)) (mem_univ (z-y)) ha hb hab)
          ((definingBump ε hε).nonneg_normed (μ := volume) y)
        simpa only [smul_eq_mul, mul_add, mul_left_comm] using h)
  simp only [Pi.add_apply] at hint
  simpa only [smoothConvexAverage, integral_add
    ((integrable_smoothConvexAverage hf hε x).const_mul a)
    ((integrable_smoothConvexAverage hf hε z).const_mul b), integral_const_mul, smul_eq_mul] using hint

lemma smoothConvexAverage_error {f : E n → ℝ} {L : ℝ≥0} (hL : LipschitzWith L f)
    {ε : ℝ} (hε : 0 < ε) (x : E n) :
    |smoothConvexAverage f ε hε x - f x| ≤ L * ε := by
  let k := (definingBump (n:=n) ε hε).normed volume
  have hki : Integrable k := (definingBump ε hε).integrable_normed
  have hkn : ∀ y, 0 ≤ k y := (definingBump ε hε).nonneg_normed
  have hsub : smoothConvexAverage f ε hε x - f x =
      ∫ y, k y * (f (x-y)-f x) := by
    simp only [mul_sub]
    rw [integral_sub (integrable_smoothConvexAverage hL.continuous hε x)
      (hki.mul_const (f x)), integral_mul_const]
    simp [k, smoothConvexAverage, ContDiffBump.integral_normed]
  rw [hsub, ← Real.norm_eq_abs]
  have hbound (y : E n) : ‖k y * (f (x-y)-f x)‖ ≤ k y * (L * ε) := by
    by_cases hy : k y = 0
    · simp [hy]
    have hyb : y ∈ Metric.ball (0 : E n) ε := by
      have hm : y ∈ Function.support k := hy
      simpa only [k, ContDiffBump.support_normed_eq, definingBump] using hm
    have hyn : ‖y‖ ≤ ε := (by simpa using hyb : ‖y‖ < ε).le
    rw [norm_mul, Real.norm_eq_abs (k y), abs_of_nonneg (hkn y)]
    apply mul_le_mul_of_nonneg_left _ (hkn y)
    have hd := hL.dist_le_mul (x-y) x
    simp only [Real.dist_eq, dist_eq_norm, sub_sub_cancel_left, norm_neg] at hd
    exact hd.trans (mul_le_mul_of_nonneg_left hyn L.coe_nonneg)
  exact (norm_integral_le_of_norm_le (hki.mul_const _) (ae_of_all _ hbound)).trans_eq (by
    rw [integral_mul_const]
    simp [k, ContDiffBump.integral_normed])

/-- The concrete smooth strongly convex gauge approximation. -/
def smoothGaugeDefining (S : Set (E n)) (ε : ℝ) (hε : 0 < ε) (x : E n) : ℝ :=
  smoothConvexAverage (gauge S) ε hε x + ε * ‖x‖ ^ 2

lemma contDiff_smoothGaugeDefining {S : Set (E n)} (hc : Convex ℝ S)
    (h0 : S ∈ 𝓝 0) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ∞ (smoothGaugeDefining S ε hε) :=
  (contDiff_smoothConvexAverage (continuous_gauge hc h0) hε).add
    (contDiff_const.mul (contDiff_norm_sq ℝ))

lemma stronglyConvex_smoothGaugeDefining {S : Set (E n)} (hc : Convex ℝ S)
    (h0 : S ∈ 𝓝 0) {ε : ℝ} (hε : 0 < ε) :
    StrongConvexOn univ (2 * ε) (smoothGaugeDefining S ε hε) := by
  rw [strongConvexOn_iff_convex]
  convert convexOn_smoothConvexAverage (continuous_gauge hc h0) (convexOn_gauge_univ hc h0) hε using 1
  ext x
  simp [smoothGaugeDefining]

lemma smoothGaugeDefining_error {S : Set (E n)} {L : ℝ≥0}
    (hL : LipschitzWith L (gauge S)) {ε : ℝ} (hε : 0 < ε) (x : E n) :
    |smoothGaugeDefining S ε hε x - gauge S x| ≤ ε * (L + ‖x‖^2) := by
  have h := smoothConvexAverage_error hL hε x
  calc
    _ = |(smoothConvexAverage (gauge S) ε hε x-gauge S x) + ε*‖x‖^2| := by
      congr 1
      simp [smoothGaugeDefining]
      ring
    _ ≤ |smoothConvexAverage (gauge S) ε hε x-gauge S x| + |ε*‖x‖^2| := abs_add_le _ _
    _ ≤ L*ε + ε*‖x‖^2 := add_le_add h (by rw [abs_of_nonneg (mul_nonneg hε.le (sq_nonneg _))])
    _ = _ := by ring

lemma smoothConvexAverage_nonneg {f : E n → ℝ} (hf : ∀ x, 0 ≤ f x)
    {ε : ℝ} (hε : 0 < ε) (x : E n) : 0 ≤ smoothConvexAverage f ε hε x := by
  exact integral_nonneg (fun y => mul_nonneg
    ((definingBump ε hε).nonneg_normed (μ := volume) y) (hf _))

lemma smoothGaugeDefining_lower {S : Set (E n)} {L : ℝ≥0}
    (hL : LipschitzWith L (gauge S)) {ε : ℝ} (hε : 0 < ε) (x : E n) :
    gauge S x - L * ε ≤ smoothGaugeDefining S ε hε x := by
  have h := (abs_le.mp (smoothConvexAverage_error hL hε x)).1
  have hq : 0 ≤ ε * ‖x‖^2 := mul_nonneg hε.le (sq_nonneg _)
  dsimp [smoothGaugeDefining]
  linarith

lemma smoothGaugeDefining_quadratic_lower {S : Set (E n)}
    {ε : ℝ} (hε : 0 < ε) (x : E n) :
    ε * ‖x‖^2 ≤ smoothGaugeDefining S ε hε x := by
  have h := smoothConvexAverage_nonneg (f := gauge S) (fun x => gauge_nonneg x) hε x
  dsimp [smoothGaugeDefining]
  linarith

end GaussianTilt.MomentMapRegularity
