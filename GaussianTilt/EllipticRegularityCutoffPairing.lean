import GaussianTilt.EllipticRegularityRoughEnergy

/-! # Cutoff-localized Cauchy–Schwarz for actual L² derivative coordinates -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ContDiff Topology ENNReal InnerProductSpace
namespace GaussianTilt.Letwin

/-- A gradient test supported where η=1 is controlled by the cutoff gradient
energy. This is actual L² Cauchy–Schwarz with proved bounded multiplication. -/
theorem cutoff_gradient_pairing_sq_le {n : ℕ}
    (μ : Measure (CoordinateSpace n)) [IsFiniteMeasureOnCompacts μ]
    (U : Fin n → Lp ℝ 2 μ) (i : Fin n) (ψ : smoothCompactCore n)
    {η : CoordinateSpace n → ℝ} (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηψ : ∀ x ∈ tsupport ψ.1, η x = 1) :
    (inner ℝ (U i) (smoothCompactToL2 μ ψ))^2 ≤
      (∫ x, η x^2 * (∑ j, (U j x)^2) ∂μ) * (∫ x, ψ.1 x^2 ∂μ) := by
  obtain ⟨B, hB⟩ := hηc.exists_bound_of_continuous hη.continuous
  have hz : MemLp (fun x => η x * U i x) 2 μ :=
    boundedMultiplier_memLp hη.continuous.aestronglyMeasurable (Eventually.of_forall hB) (U i)
  let z := hz.toLp (fun x => η x * U i x)
  have he : inner ℝ (U i) (smoothCompactToL2 μ ψ) = inner ℝ z (smoothCompactToL2 μ ψ) := by
    rw [L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [smoothCompactToL2_ae μ ψ, hz.coeFn_toLp] with x hψ hx
    change inner ℝ (U i x) (smoothCompactToL2 μ ψ x) = inner ℝ (hz.toLp _ x) (smoothCompactToL2 μ ψ x)
    rw [hψ, hx]
    simp only [RCLike.inner_apply, conj_trivial]
    by_cases hs : x ∈ tsupport ψ.1
    · rw [hηψ x hs, one_mul]
    · have h0 : ψ.1 x = 0 := Function.notMem_support.mp (fun ht => hs (subset_closure ht))
      simp [h0]
  have hnorm : ‖z‖^2 ≤ ∫ x, η x^2 * (∑ j, (U j x)^2) ∂μ := by
    rw [norm_toLp_sq_eq_integral hz]
    have ha : HasCompactSupport (fun x => η x^2) := by
      simpa only [pow_two] using hηc.mul_right (f' := η)
    have hi : Integrable (fun x => η x^2 * (∑ j, (U j x)^2)) μ :=
      integrable_continuous_compact_mul (hη.continuous.pow 2) ha
      (integrable_finset_sum _ fun j _ => (Lp.memLp (U j)).integrable_sq)
    apply integral_mono hz.integrable_sq hi
    intro x
    change (η x * U i x)^2 ≤ η x^2 * (∑ j, (U j x)^2)
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (fun j _ => sq_nonneg (U j x)) (Finset.mem_univ i)) (sq_nonneg _)
  have hc : (inner ℝ z (smoothCompactToL2 μ ψ))^2 ≤
      ‖z‖^2 * ‖smoothCompactToL2 μ ψ‖^2 := by
    simpa only [← pow_two, real_inner_self_eq_norm_sq] using
      real_inner_mul_inner_self_le z (smoothCompactToL2 μ ψ)
  have hψnorm : ‖smoothCompactToL2 μ ψ‖^2 = ∫ x, ψ.1 x^2 ∂μ :=
    norm_toLp_sq_eq_integral (smooth_compact_memLp ψ.2.1 ψ.2.2)
  rw [hψnorm] at hc
  rw [he]
  exact hc.trans (mul_le_mul_of_nonneg_right hnorm (integral_nonneg fun x => sq_nonneg _))

/-- A bounded cutoff gradient gives a direct bound in terms of the actual
L² value coordinate. -/
theorem integral_value_sq_gradient_le {n : ℕ}
    (μ : Measure (CoordinateSpace n)) (v : Lp ℝ 2 μ)
    {η : CoordinateSpace n → ℝ} (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    {B : ℝ} (hB : ∀ x, gradientSquare η x ≤ B) :
    (∫ x, (v x)^2 * gradientSquare η x ∂μ) ≤ B * ∫ x, (v x)^2 ∂μ := by
  have hi : Integrable (fun x => (v x)^2 * gradientSquare η x) μ := by
    simpa only [mul_comm] using integrable_continuous_compact_mul (continuous_gradientSquare hη)
      (gradientSquare_hasCompactSupport hηc) (Lp.memLp v).integrable_sq
  rw [← integral_const_mul]
  apply integral_mono hi ((Lp.memLp v).integrable_sq.const_mul B)
  intro x
  nlinarith [mul_le_mul_of_nonneg_left (hB x) (sq_nonneg (v x))]

lemma integral_cutoff_value_sq_le {n : ℕ} (μ : Measure (CoordinateSpace n))
    (v : Lp ℝ 2 μ) {χ h : CoordinateSpace n → ℝ}
    (hh : MemLp h 2 μ) (hval : v =ᵐ[μ] fun x => χ x * h x)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1) :
    (∫ x, (v x)^2 ∂μ) ≤ ∫ x, (h x)^2 ∂μ := by
  apply integral_mono_ae (Lp.memLp v).integrable_sq hh.integrable_sq
  filter_upwards [hval] with x hx
  rw [hx, mul_pow]
  have hs : χ x^2 ≤ 1 := by nlinarith [hχ0 x, hχ1 x]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hs (sq_nonneg (h x))

end GaussianTilt.Letwin
