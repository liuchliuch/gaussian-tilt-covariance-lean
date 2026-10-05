import GaussianTilt.BrascampLieb

/-!
# Brascamp–Lieb for hard interval cutoffs

This module allows a measurable density which is zero outside a finite
interval and whose convex negative log-potential may diverge at the endpoints.
No endpoint continuity, derivative, score, or functional inequality is assumed.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Interval Topology
namespace GaussianTilt.BrascampLieb

lemma finite_density_variance_le_inv {f : ℝ → ℝ} {a b κ : ℝ} (hab : a < b) (hκ : 0 < κ)
    (hpos : ∀ x ∈ Icc a b, 0 < f x) (hlog : ContinuousOn (fun x ↦ -Real.log (f x)) (Icc a b))
    (hc : ConvexOn ℝ (Icc a b) (fun x ↦ -Real.log (f x) - κ / 2 * x ^ 2)) :
    (∫ x in a..b, x ^ 2 * f x) / (∫ x in a..b, f x) -
      ((∫ x in a..b, x * f x) / (∫ x in a..b, f x)) ^ 2 ≤ κ⁻¹ := by
  let W : ℝ → ℝ := fun x ↦ -Real.log (f (max a (min b x)))
  have hW : Continuous W := hlog.comp_continuous (by fun_prop)
    (fun x ↦ ⟨le_max_left _ _, max_le hab.le (min_le_left _ _)⟩)
  have hWeq : ∀ x ∈ Icc a b, W x = -Real.log (f x) := by
    intro x hx
    simp [W, min_eq_right hx.2, max_eq_right hx.1]
  have hweight : ∀ x ∈ Icc a b, weight W x = f x := by
    intro x hx
    simp only [weight, hWeq x hx, neg_neg, Real.exp_log (hpos x hx)]
  have hmom : ∀ k : ℕ, (∫ x in a..b, x ^ k * weight W x) = ∫ x in a..b, x ^ k * f x := by
    intro k
    apply intervalIntegral.integral_congr
    intro x hx
    simp only [hweight x (by simpa only [uIcc_of_le hab.le] using hx)]
  have hcW : ConvexOn ℝ (Icc a b) (fun x ↦ W x - κ / 2 * x ^ 2) :=
    hc.congr (fun x hx ↦ by rw [hWeq x hx])
  have h := variance_le_inv_of_continuous hab hκ hW hcW
  rw [variance_eq_moments hab hW] at h
  have h₀ := hmom 0
  have h₁ := hmom 1
  simp only [pow_zero, one_mul] at h₀
  simp only [pow_one] at h₁
  simpa only [mean, mass, hmom 2, h₀, h₁] using h

lemma tendsto_intervalIntegral_of_integrable {g : ℝ → ℝ} (hi : Integrable g)
    {a b : ℝ} {u v : ℕ → ℝ} (hu : Tendsto u atTop (𝓝 a)) (hv : Tendsto v atTop (𝓝 b)) :
    Tendsto (fun n ↦ ∫ x in u n..v n, g x) atTop (𝓝 (∫ x in a..b, g x)) := by
  have hF := intervalIntegral.continuous_primitive (fun _ _ ↦ hi.intervalIntegrable) 0
  have hlim := (hF.continuousAt.tendsto.comp hv).sub (hF.continuousAt.tendsto.comp hu)
  simpa only [Function.comp_apply, intervalIntegral.integral_interval_sub_left hi.intervalIntegrable hi.intervalIntegrable] using hlim

lemma integrable_pow_mul_compact_density {f : ℝ → ℝ} {a b : ℝ} (hi : Integrable f)
    (hs : ∀ x ∉ Icc a b, f x = 0) (k : ℕ) : Integrable (fun x ↦ x ^ k * f x) := by
  have hi' := hi.integrableOn.mul_continuousOn (show ContinuousOn (fun x : ℝ ↦ x ^ k) (Icc a b) by fun_prop) isCompact_Icc
  have h := hi'.integrable_of_forall_notMem_eq_zero (fun x hx ↦ by rw [hs x hx, zero_mul])
  simpa only [mul_comm] using h

lemma integral_interval_eq_full_of_compact_support {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hs : ∀ x ∉ Icc a b, g x = 0) : (∫ x in a..b, g x) = ∫ x, g x := by
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero hs

/-- Genuine one-dimensional nonsmooth Brascamp–Lieb for a compact-support
density with a possibly infinite endpoint potential. The only regularity
assumption is integrability; continuity on the positive interior follows
from convexity. -/
theorem compact_density_variance_le_inv {f : ℝ → ℝ} {a b κ : ℝ} (hab : a < b) (hκ : 0 < κ)
    (hi : Integrable f) (hnonneg : ∀ x, 0 ≤ f x)
    (hpos : ∀ x ∈ Ioo a b, 0 < f x) (hs : ∀ x ∉ Icc a b, f x = 0)
    (hc : ConvexOn ℝ (Ioo a b) (fun x ↦ -Real.log (f x) - κ / 2 * x ^ 2)) :
    (∫ x, x ^ 2 * f x) / (∫ x, f x) - ((∫ x, x * f x) / (∫ x, f x)) ^ 2 ≤ κ⁻¹ := by
  have hmass : 0 < ∫ x, f x := by
    apply (integral_pos_iff_support_of_nonneg hnonneg hi).2
    have hsub : Ioo a b ⊆ Function.support f := fun x hx ↦ (hpos x hx).ne'
    exact lt_of_lt_of_le (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)) (measure_mono hsub)
  have hlog : ContinuousOn (fun x ↦ -Real.log (f x)) (Ioo a b) := by
    have hR := ConvexOn.continuousOn isOpen_Ioo hc
    convert hR.add (show ContinuousOn (fun x : ℝ ↦ κ / 2 * x ^ 2) (Ioo a b) by fun_prop) using 1
    funext x
    ring
  have hba : 0 < b - a := sub_pos.mpr hab
  let ε : ℕ → ℝ := fun n ↦ ((b - a) / 4) * (1 / ((n : ℝ) + 1))
  have hεpos : ∀ n, 0 < ε n := by intro n; dsimp [ε]; positivity
  have hεle : ∀ n, ε n ≤ (b - a) / 4 := by
    intro n
    dsimp [ε]
    apply mul_le_of_le_one_right (by positivity)
    exact (div_le_one (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat
  have hu : Tendsto (fun n ↦ a + ε n) atTop (𝓝 a) := by simpa using tendsto_const_nhds.add hεlim
  have hv : Tendsto (fun n ↦ b - ε n) atTop (𝓝 b) := by simpa using tendsto_const_nhds.sub hεlim
  have hi₁ : Integrable (fun x ↦ x * f x) := by simpa using integrable_pow_mul_compact_density hi hs 1
  have hi₂ := integrable_pow_mul_compact_density hi hs 2
  have h₀ := tendsto_intervalIntegral_of_integrable hi hu hv
  have h₁ := tendsto_intervalIntegral_of_integrable hi₁ hu hv
  have h₂ := tendsto_intervalIntegral_of_integrable hi₂ hu hv
  have hz : ∀ k : ℕ, (∫ x in a..b, x ^ k * f x) = ∫ x, x ^ k * f x := by
    intro k
    exact integral_interval_eq_full_of_compact_support hab.le (fun x hx ↦ by rw [hs x hx, mul_zero])
  have hz₀ := hz 0
  have hz₁ := hz 1
  simp only [pow_zero, one_mul] at hz₀
  simp only [pow_one] at hz₁
  rw [hz₀] at h₀
  rw [hz₁] at h₁
  rw [hz 2] at h₂
  apply le_of_tendsto ((h₂.div h₀ hmass.ne').sub ((h₁.div h₀ hmass.ne').pow 2))
  filter_upwards [] with n
  have habn : a + ε n < b - ε n := by linarith [hεle n]
  have hsub : Icc (a + ε n) (b - ε n) ⊆ Ioo a b := by
    intro x hx
    exact ⟨by linarith [hx.1, hεpos n], by linarith [hx.2, hεpos n]⟩
  exact finite_density_variance_le_inv habn hκ (fun x hx ↦ hpos x (hsub hx))
    (hlog.mono hsub) (hc.subset hsub (convex_Icc _ _))

end GaussianTilt.BrascampLieb
