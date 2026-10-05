import GaussianTilt.MomentMapLinearDirichletFlatIterationConstants

/-!
# Actual normalized flat residuals and Hölder forcing scaling

The amplitude r⁻²⁻ᵅ exactly preserves the forcing Hölder constant. The
polynomial residual is cut off in the upper half-space before rescaling,
so its genuine L² and weak-equation properties survive each iteration.
-/
noncomputable section
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 1000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

def flatNormalizationFactor (r α : ℝ) : ℝ := r^(-(2+α))

def normalizedFlatSource (r α : ℝ) (f : KernelSpace n → ℝ) (x : KernelSpace n) : ℝ :=
  flatNormalizationFactor r α * r^2 * f (r • x)

def normalizedFlatResidual (j : Fin n) (r α : ℝ) (u P : KernelSpace n → ℝ) (x : KernelSpace n) : ℝ :=
  flatNormalizationFactor r α * flatResidual j (fun y => u (r • y)) (fun y => P (r • y)) x

lemma flatNormalizationFactor_pos {r : ℝ} (hr : 0 < r) (α : ℝ) :
    0 < flatNormalizationFactor r α := Real.rpow_pos_of_pos hr _

lemma flatNormalizationFactor_cancel {r : ℝ} (hr : 0 < r) (α : ℝ) :
    flatNormalizationFactor r α * r^(2+α) = 1 := by
  rw [flatNormalizationFactor, ← Real.rpow_add hr, neg_add_cancel, Real.rpow_zero]

lemma flatNormalizationFactor_holder_cancel {r : ℝ} (hr : 0 < r) (α : ℝ) :
    flatNormalizationFactor r α * r^2 * r^α = 1 := by
  rw [flatNormalizationFactor, ← Real.rpow_natCast r 2, ← Real.rpow_add hr, ← Real.rpow_add hr]
  norm_num [show -(2+α)+(2 : ℝ)+α = 0 by ring]

lemma normalizedFlatSource_continuous {f : KernelSpace n → ℝ} (hf : Continuous f) (r α : ℝ) :
    Continuous (normalizedFlatSource r α f) :=
  continuous_const.mul (hf.comp (continuous_const.smul continuous_id))

lemma normalizedFlatSource_compact {f : KernelSpace n → ℝ} (hf : HasCompactSupport f)
    {r : ℝ} (hr : 0 < r) (α : ℝ) : HasCompactSupport (normalizedFlatSource r α f) :=
  (hf.comp_homeomorph (Homeomorph.smulOfNeZero r hr.ne')).mul_left

lemma normalizedFlatSource_zero {f : KernelSpace n → ℝ} (hf : f 0 = 0) (r α : ℝ) :
    normalizedFlatSource r α f 0 = 0 := by simp [normalizedFlatSource, hf]

/-- The forcing exponent and constant survive the actual Poisson scaling. -/
lemma normalizedFlatSource_holder {f : KernelSpace n → ℝ} {r α H : ℝ}
    (hr : 0 < r) (hH : 0 ≤ H)
    (hf : ∀ x y, |f x-f y| ≤ H*‖x-y‖^α) :
    ∀ x y, |normalizedFlatSource r α f x - normalizedFlatSource r α f y| ≤ H*‖x-y‖^α := by
  intro x y
  let c := flatNormalizationFactor r α * r^2
  have hc : 0 ≤ c := mul_nonneg (flatNormalizationFactor_pos hr α).le (sq_nonneg _)
  have he : normalizedFlatSource r α f x - normalizedFlatSource r α f y =
      c*(f (r • x)-f (r • y)) := by dsimp [normalizedFlatSource,c]; ring
  rw [he, abs_mul, abs_of_nonneg hc]
  have hb := mul_le_mul_of_nonneg_left (hf (r • x) (r • y)) hc
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hr,
    Real.mul_rpow hr.le (norm_nonneg _)] at hb
  apply hb.trans_eq
  have hcanc := flatNormalizationFactor_holder_cancel hr α
  dsimp [c]
  calc
    flatNormalizationFactor r α*r^2*(H*(r^α*‖x-y‖^α)) =
        (flatNormalizationFactor r α*r^2*r^α)*(H*‖x-y‖^α) := by ring
    _ = _ := by rw [hcanc, one_mul]

lemma holder_force_bound_of_zero {f : KernelSpace n → ℝ} {α H : ℝ}
    (hα : 0 ≤ α) (hH : 0 ≤ H) (hf0 : f 0 = 0)
    (hf : ∀ x y, |f x-f y| ≤ H*‖x-y‖^α) :
    ∀ x ∈ Metric.ball (0 : KernelSpace n) 2, |f x| ≤ H*2^α := by
  intro x hx
  have hb := hf x 0
  rw [hf0, sub_zero, sub_zero] at hb
  apply hb.trans
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _)
    (show ‖x‖ ≤ 2 by exact (show ‖x‖ < 2 by simpa using hx).le) hα) hH

/-- Every actual normalized harmonic-polynomial residual remains valid
flat weak Poisson data; no PDE scaling is assumed. -/
theorem FlatWeakPoisson.normalizedResidual {j : Fin n} {u f P : KernelSpace n → ℝ}
    (h : FlatWeakPoisson j u f) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (α : ℝ)
    (hP : ContDiff ℝ ∞ P) (hP0 : ∀ x, x j = 0 → P x = 0)
    (hPlap : ∀ x, kernelLaplacian P x = 0) :
    FlatWeakPoisson j (normalizedFlatResidual j r α u P) (normalizedFlatSource r α f) := by
  have hs : FlatWeakPoisson j (fun x => u (r • x)) (fun x => r^2*f (r • x)) := by
    simpa only [one_mul] using h.rescale hr hr1 1
  have hPr : ContDiff ℝ ∞ (fun x : KernelSpace n => P (r • x)) := hP.comp (contDiff_const.smul contDiff_id)
  have hPr0 (x : KernelSpace n) (hx : x j = 0) : P (r • x) = 0 := hP0 _ (by simp [hx])
  have hPrlap (x : KernelSpace n) : kernelLaplacian (fun y => P (r • y)) x = 0 := by
    rw [kernelLaplacian_comp_smul_C2 (contDiff_infty.mp hP 2), hPlap, mul_zero]
  have ht := (hs.subtractHarmonic hPr hPr0 hPrlap).amplitude (flatNormalizationFactor r α)
  convert ht using 1 <;> funext x <;> simp only [normalizedFlatResidual, normalizedFlatSource] <;> ring

lemma normalizedFlatResidual_eq {j : Fin n} {u P : KernelSpace n → ℝ} {r α : ℝ}
    {x : KernelSpace n} (hx : x ∈ flatUpperBall j 2) :
    normalizedFlatResidual j r α u P x = flatNormalizationFactor r α * (u (r • x)-P (r • x)) := by
  rw [normalizedFlatResidual, flatResidual_eq j _ _ hx]

end GaussianTilt.MomentMapLinearDirichlet
