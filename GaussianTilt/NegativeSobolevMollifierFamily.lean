import GaussianTilt.NegativeSobolevMollifierLimit

/-! # Explicit normalized compact smooth mollifiers -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ContDiff Topology ENNReal Convolution
namespace GaussianTilt.Letwin

/-- A concrete bump with outer radius 1/(k+1) and half that inner radius. -/
def canonicalMollifierBump (n k : ℕ) : ContDiffBump (0 : CoordinateSpace n) :=
  ⟨(((k : ℝ)+1)⁻¹)/2, ((k : ℝ)+1)⁻¹, by positivity,
    half_lt_self (by positivity)⟩

/-- The normalized actual C∞ convolution kernel. -/
def canonicalMollifier (n k : ℕ) : CoordinateSpace n → ℝ :=
  (canonicalMollifierBump n k).normed volume

lemma canonicalMollifier_smooth (n k : ℕ) : ContDiff ℝ ∞ (canonicalMollifier n k) :=
  (canonicalMollifierBump n k).contDiff_normed

lemma canonicalMollifier_compact (n k : ℕ) : HasCompactSupport (canonicalMollifier n k) :=
  (canonicalMollifierBump n k).hasCompactSupport_normed

lemma canonicalMollifier_nonneg (n k : ℕ) (x : CoordinateSpace n) :
    0 ≤ canonicalMollifier n k x := (canonicalMollifierBump n k).nonneg_normed x

lemma canonicalMollifier_integral (n k : ℕ) : (∫ x, canonicalMollifier n k x) = 1 :=
  (canonicalMollifierBump n k).integral_normed

lemma canonicalMollifier_support (n k : ℕ) :
    Function.support (canonicalMollifier n k) = Metric.ball 0 ((k : ℝ)+1)⁻¹ :=
  (canonicalMollifierBump n k).support_normed_eq

lemma canonicalMollifier_support_le_one (n k : ℕ) :
    Function.support (canonicalMollifier n k) ⊆ Metric.closedBall 0 1 := by
  rw [canonicalMollifier_support]
  exact Metric.ball_subset_closedBall.trans
    (Metric.closedBall_subset_closedBall (inv_le_one_of_one_le₀ (by have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)))

lemma canonicalMollifier_support_tendsto (n : ℕ) :
    Tendsto (fun k => Function.support (canonicalMollifier n k)) atTop (𝓝 0).smallSets := by
  apply ContDiffBump.tendsto_support_normed_smallSets
  change Tendsto (fun k : ℕ => ((k : ℝ)+1)⁻¹) atTop (𝓝 0)
  exact tendsto_inv_atTop_zero.comp
    (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)

/-- Explicit actual mollification, with no mollifier-existence assumption. -/
def mollify {n : ℕ} (k : ℕ) (f : CoordinateSpace n → ℝ) : CoordinateSpace n → ℝ :=
  scalarConvolution (canonicalMollifier n k) f

/-- Every actual L² function is approximated in L² by this fixed smooth
mollifier family. -/
theorem integral_mollify_sub_sq_tendsto {n : ℕ} {f : CoordinateSpace n → ℝ}
    (hf : MemLp f 2 volume) :
    Tendsto (fun k => ∫ x, (mollify k f x-f x)^2) atTop (𝓝 0) :=
  integral_mollifier_sub_sq_tendsto (fun k => (canonicalMollifier_smooth n k).continuous)
    (canonicalMollifier_compact n) (canonicalMollifier_nonneg n) (canonicalMollifier_integral n)
    (canonicalMollifier_support_le_one n) (canonicalMollifier_support_tendsto n) hf

lemma mollify_memLp {n : ℕ} {f : CoordinateSpace n → ℝ} (hf : MemLp f 2 volume) (k : ℕ) :
    MemLp (mollify k f) 2 volume :=
  scalarConvolution_memLp (canonicalMollifier_smooth n k).continuous (canonicalMollifier_compact n k)
    (canonicalMollifier_nonneg n k) (canonicalMollifier_integral n k) hf

lemma mollify_smooth_of_locallyIntegrable {n : ℕ} {f : CoordinateSpace n → ℝ}
    (hf : LocallyIntegrable f volume) (k : ℕ) : ContDiff ℝ ∞ (mollify k f) :=
  (canonicalMollifier_compact n k).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (canonicalMollifier_smooth n k) hf

lemma mollify_smooth {n : ℕ} {f : CoordinateSpace n → ℝ} (hf : MemLp f 2 volume) (k : ℕ) :
    ContDiff ℝ ∞ (mollify k f) :=
  (canonicalMollifier_compact n k).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (canonicalMollifier_smooth n k) (hf.locallyIntegrable (by norm_num))

lemma mollify_compact {n : ℕ} {f : CoordinateSpace n → ℝ} (hf : HasCompactSupport f) (k : ℕ) :
    HasCompactSupport (mollify k f) :=
  (canonicalMollifier_compact n k).convolution (ContinuousLinearMap.lsmul ℝ ℝ) hf

end GaussianTilt.Letwin
