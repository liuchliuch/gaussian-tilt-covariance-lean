import GaussianTilt.MomentMapDanskinExtended

/-! # Dominated differentiation of genuine variational partitions

A uniform parameter-Lipschitz bound on the potential yields an explicit
integrable Lipschitz bound on its exponential density. Pointwise Danskin
derivatives may hold only almost everywhere at the parameter zero.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal
set_option maxHeartbeats 800000

namespace GaussianTilt.MomentMapCoercivity

lemma abs_exp_sub_exp_le_of_le {a b C : ℝ} (ha : a ≤ C) (hb : b ≤ C) :
    |Real.exp a - Real.exp b| ≤ Real.exp C * |a - b| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := Real.exp) (fun x _ ↦ (Real.hasDerivAt_exp x).differentiableAt)
    (C := Real.exp C) (fun x hx ↦ by
      rw [Real.deriv_exp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr hx) (convex_Iic C) hb ha
  simpa only [Real.norm_eq_abs] using h

lemma exp_neg_potential_lipschitz {φ : ℝ → ℝ} {M : ℝ≥0} (hφ : LipschitzWith M φ) :
    LipschitzOnWith (Real.nnabs ((M : ℝ) * Real.exp M * Real.exp (-φ 0)))
      (fun t ↦ Real.exp (-φ t)) (Metric.ball 0 1) := by
  have hupper (t : ℝ) (ht : t ∈ Metric.ball (0 : ℝ) 1) : -φ t ≤ (M : ℝ) - φ 0 := by
    have h := hφ.norm_sub_le t 0
    simp only [Real.norm_eq_abs, sub_zero] at h
    have ht' : |t| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using ht
    have hm := mul_le_mul_of_nonneg_left ht'.le M.coe_nonneg
    have hh := (neg_abs_le (φ t - φ 0))
    nlinarith
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs t ht
  rw [Real.dist_eq, Real.dist_eq, Real.coe_nnabs,
    abs_of_nonneg (by positivity : 0 ≤ (M : ℝ) * Real.exp M * Real.exp (-φ 0))]
  have he := abs_exp_sub_exp_le_of_le (hupper s hs) (hupper t ht)
  have h := hφ.norm_sub_le s t
  simp only [Real.norm_eq_abs] at h
  have hd : |-φ s - -φ t| = |φ s - φ t| := by rw [neg_sub_neg, abs_sub_comm]
  rw [hd] at he
  calc
    _ ≤ Real.exp ((M : ℝ) - φ 0) * |φ s - φ t| := he
    _ ≤ Real.exp ((M : ℝ) - φ 0) * ((M : ℝ) * |s - t|) :=
      mul_le_mul_of_nonneg_left h (Real.exp_nonneg _)
    _ = _ := by rw [sub_eq_add_neg, Real.exp_add]; ring

/-- Derivative of the actual partition, under hypotheses directly supplied
by the compact-envelope Lipschitz and almost-everywhere Danskin theorems. -/
theorem partition_hasDerivAt_of_lipschitz {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {Φ : ℝ → Ω → ℝ} {d : Ω → ℝ} {M : ℝ≥0}
    (hΦ : ∀ t, AEStronglyMeasurable (Φ t) μ)
    (hi : Integrable (fun x ↦ Real.exp (-Φ 0 x)) μ)
    (hd : AEStronglyMeasurable d μ)
    (hLip : ∀ᵐ x ∂μ, LipschitzWith M (fun t ↦ Φ t x))
    (hderiv : ∀ᵐ x ∂μ, HasDerivAt (fun t ↦ Φ t x) (d x) 0) :
    Integrable (fun x ↦ -d x * Real.exp (-Φ 0 x)) μ ∧
      HasDerivAt (fun t ↦ ∫ x, Real.exp (-Φ t x) ∂μ)
        (∫ x, -d x * Real.exp (-Φ 0 x) ∂μ) 0 := by
  have hmeas (t : ℝ) : AEStronglyMeasurable (fun x ↦ Real.exp (-Φ t x)) μ :=
    Real.continuous_exp.comp_aestronglyMeasurable (hΦ t).neg
  have hdiff : ∀ᵐ x ∂μ, HasDerivAt (fun t ↦ Real.exp (-Φ t x))
      (-d x * Real.exp (-Φ 0 x)) 0 := by
    filter_upwards [hderiv] with x hx
    have h := (Real.hasDerivAt_exp (-Φ 0 x)).comp 0 hx.neg
    exact (mul_comm (Real.exp (-Φ 0 x)) (-d x)) ▸ h
  exact hasDerivAt_integral_of_dominated_loc_of_lip (μ := μ) (𝕜 := ℝ) (x₀ := 0)
    (F := fun t x ↦ Real.exp (-Φ t x))
    (F' := fun x ↦ -d x * Real.exp (-Φ 0 x)) (ε := 1)
    (bound := fun x ↦ (M : ℝ) * Real.exp M * Real.exp (-Φ 0 x)) (by norm_num)
    (Eventually.of_forall hmeas) hi (hd.neg.mul (hmeas 0))
    (hLip.mono (fun x hx ↦ exp_neg_potential_lipschitz (φ := fun t ↦ Φ t x) (M := M) hx))
    (hi.const_mul ((M : ℝ) * Real.exp M)) hdiff

theorem logPartition_hasDerivAt_of_lipschitz {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {Φ : ℝ → Ω → ℝ} {d : Ω → ℝ} {M : ℝ≥0}
    (hΦ : ∀ t, AEStronglyMeasurable (Φ t) μ)
    (hi : Integrable (fun x ↦ Real.exp (-Φ 0 x)) μ)
    (hZ : 0 < ∫ x, Real.exp (-Φ 0 x) ∂μ)
    (hd : AEStronglyMeasurable d μ)
    (hLip : ∀ᵐ x ∂μ, LipschitzWith M (fun t ↦ Φ t x))
    (hderiv : ∀ᵐ x ∂μ, HasDerivAt (fun t ↦ Φ t x) (d x) 0) :
    HasDerivAt (fun t ↦ Real.log (∫ x, Real.exp (-Φ t x) ∂μ))
      ((∫ x, -d x * Real.exp (-Φ 0 x) ∂μ) / (∫ x, Real.exp (-Φ 0 x) ∂μ)) 0 :=
  (partition_hasDerivAt_of_lipschitz μ hΦ hi hd hLip hderiv).2.log hZ.ne'

end GaussianTilt.MomentMapCoercivity
