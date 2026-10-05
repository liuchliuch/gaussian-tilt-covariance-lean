import Mathlib

/-!
# The analytic exhaustion argument in Letwin Appendix A5

This file proves the Fatou/dominated-convergence step for explicitly supplied
cutoffs and a symmetric operator. It does not postulate the existence of the
moment-map cutoffs in Appendix A4. The operator, its cutoff values, their L¹
decay, and tested symmetry are explicit inputs to this general analytic lemma.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace GaussianTilt.Letwin

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Fatou's lemma turns bounded nonnegative cutoff integrals into genuine
integrability of the full function. Monotonicity of the cutoffs is unnecessary. -/
theorem integrable_of_nonneg_cutoff_integrals {q : Ω → ℝ} {χ : ℕ → Ω → ℝ}
    (hq : AEStronglyMeasurable q μ) (hq0 : 0 ≤ᵐ[μ] q)
    (hχ0 : ∀ n, 0 ≤ᵐ[μ] χ n)
    (hχlim : ∀ᵐ x ∂μ, Tendsto (fun n => χ n x) atTop (𝓝 1))
    (hint : ∀ n, Integrable (fun x => χ n x * q x) μ)
    (C : ℝ) (hbound : ∀ n, (∫ x, χ n x * q x ∂μ) ≤ C) : Integrable q μ := by
  have hlim : ∀ᵐ x ∂μ,
      liminf (fun n => ENNReal.ofReal (χ n x * q x)) atTop = ENNReal.ofReal (q x) := by
    filter_upwards [hχlim] with x hx
    have h : Tendsto (fun n => χ n x * q x) atTop (𝓝 (q x)) := by
      simpa using hx.mul_const (q x)
    exact (ENNReal.continuous_ofReal.continuousAt.tendsto.comp h).liminf_eq
  have hfat : (∫⁻ x, ENNReal.ofReal (q x) ∂μ) ≤
      liminf (fun n => ∫⁻ x, ENNReal.ofReal (χ n x * q x) ∂μ) atTop := by
    rw [← lintegral_congr_ae hlim]
    exact lintegral_liminf_le' (fun n => (hint n).aemeasurable.ennreal_ofReal)
  have hb : ∀ n, (∫⁻ x, ENNReal.ofReal (χ n x * q x) ∂μ) ≤ ENNReal.ofReal C := by
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hint n)]
    · exact ENNReal.ofReal_le_ofReal (hbound n)
    · filter_upwards [hq0, hχ0 n] with x hx hχx using mul_nonneg hχx hx
  refine ⟨hq, (hasFiniteIntegral_iff_ofReal hq0).mpr ?_⟩
  exact (hfat.trans (liminf_le_of_frequently_le (Frequently.of_forall hb))).trans_lt
    ENNReal.ofReal_lt_top

/-- Multiplication by [0,1]-valued cutoffs converging to one preserves the
integral of every L¹ function. -/
theorem tendsto_integral_cutoff {f : Ω → ℝ} {χ : ℕ → Ω → ℝ}
    (hf : Integrable f μ) (hχm : ∀ n, AEStronglyMeasurable (χ n) μ)
    (hχ0 : ∀ n, 0 ≤ᵐ[μ] χ n) (hχ1 : ∀ n, χ n ≤ᵐ[μ] 1)
    (hχlim : ∀ᵐ x ∂μ, Tendsto (fun n => χ n x) atTop (𝓝 1)) :
    Tendsto (fun n => ∫ x, χ n x * f x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
  · exact fun n => (hχm n).mul hf.aestronglyMeasurable
  · exact hf.norm
  · intro n
    filter_upwards [hχ0 n, hχ1 n] with x h0 h1
    change ‖χ n x * f x‖ ≤ ‖f x‖
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg h0]
    exact mul_le_of_le_one_left (norm_nonneg _) h1
  · filter_upwards [hχlim] with x hx
    simpa using hx.mul_const (f x)

/-- The full Fatou argument in Appendix A5. For a bounded subsolution, tested
symmetry and vanishing L¹ cutoff error imply both global integrability of the
operator and zero mean. Neither conclusion is an assumption. The geometric
construction of the cutoffs is a separate obligation. -/
theorem integrable_and_integral_eq_zero_of_cutoff_symmetry [IsFiniteMeasure μ]
    {f Lf : Ω → ℝ} {χ Lχ : ℕ → Ω → ℝ} (c B : ℝ)
    (hf : AEStronglyMeasurable f μ) (hLf : AEStronglyMeasurable Lf μ)
    (hfB : ∀ᵐ x ∂μ, ‖f x‖ ≤ B)
    (hsub : ∀ᵐ x ∂μ, 0 ≤ Lf x + c * f x)
    (hχm : ∀ n, AEStronglyMeasurable (χ n) μ)
    (hχ0 : ∀ n, 0 ≤ᵐ[μ] χ n) (hχ1 : ∀ n, χ n ≤ᵐ[μ] 1)
    (hχlim : ∀ᵐ x ∂μ, Tendsto (fun n => χ n x) atTop (𝓝 1))
    (hχLf : ∀ n, Integrable (fun x => χ n x * Lf x) μ)
    (hLχ : ∀ n, Integrable (Lχ n) μ)
    (hLχlim : Tendsto (fun n => ∫ x, ‖Lχ n x‖ ∂μ) atTop (𝓝 0))
    (hsym : ∀ n, (∫ x, χ n x * Lf x ∂μ) = ∫ x, f x * Lχ n x ∂μ) :
    Integrable Lf μ ∧ (∫ x, Lf x ∂μ) = 0 := by
  have hfi : Integrable f μ := Integrable.of_bound hf B hfB
  have hχfi : ∀ n, Integrable (fun x => χ n x * f x) μ := by
    intro n
    apply hfi.norm.mono' ((hχm n).mul hf)
    filter_upwards [hχ0 n, hχ1 n] with x h0 h1
    change ‖χ n x * f x‖ ≤ ‖f x‖
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg h0]
    exact mul_le_of_le_one_left (norm_nonneg _) h1
  have hboundary : Tendsto (fun n => ∫ x, f x * Lχ n x ∂μ) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_)
      (by simpa using hLχlim.const_mul B)
    calc
      ‖∫ x, f x * Lχ n x ∂μ‖ ≤ ∫ x, B * ‖Lχ n x‖ ∂μ := by
        apply norm_integral_le_of_norm_le ((hLχ n).norm.const_mul B)
        filter_upwards [hfB] with x hx
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
      _ = B * ∫ x, ‖Lχ n x‖ ∂μ := integral_const_mul _ _
  have hcutoffL : Tendsto (fun n => ∫ x, χ n x * Lf x ∂μ) atTop (𝓝 0) := by
    simpa only [hsym] using hboundary
  let q := fun x => Lf x + c * f x
  have hqi : ∀ n, Integrable (fun x => χ n x * q x) μ := by
    intro n
    convert (hχLf n).add ((hχfi n).const_mul c) using 1
    funext x
    dsimp [q]
    ring
  have hqeq (n : ℕ) : (∫ x, χ n x * q x ∂μ) =
      (∫ x, χ n x * Lf x ∂μ) + c * ∫ x, χ n x * f x ∂μ := by
    have heq : (fun x => χ n x * q x) =
        (fun x => χ n x * Lf x + c * (χ n x * f x)) := by
      funext x
      dsimp [q]
      ring
    rw [heq, integral_add (hχLf n) ((hχfi n).const_mul c), integral_const_mul]
  have hqlim : Tendsto (fun n => ∫ x, χ n x * q x ∂μ) atTop
      (𝓝 (c * ∫ x, f x ∂μ)) := by
    simp only [hqeq]
    simpa using hcutoffL.add ((tendsto_integral_cutoff hfi hχm hχ0 hχ1 hχlim).const_mul c)
  obtain ⟨C, hC⟩ := hqlim.bddAbove_range
  have hq : Integrable q μ := integrable_of_nonneg_cutoff_integrals
    (hLf.add (hf.const_mul c)) hsub hχ0 hχlim hqi C (fun n => hC ⟨n, rfl⟩)
  have hLi : Integrable Lf μ := by
    convert hq.sub (hfi.const_mul c) using 1
    funext x
    dsimp [q]
    ring
  exact ⟨hLi, tendsto_nhds_unique
    (tendsto_integral_cutoff hLi hχm hχ0 hχ1 hχlim) hcutoffL⟩

end GaussianTilt.Letwin
