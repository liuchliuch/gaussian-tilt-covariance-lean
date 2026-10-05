import GaussianTilt.PaourisNorm

/-!
# The small-direction step in the short proof of Paouris

This file proves the deterministic duality argument using the actual
Hahn–Banach theorem and a maximizer on the Euclidean sphere.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators InnerProductSpace

namespace GaussianTilt.Paouris

variable {n : ℕ}

/-- The Euclidean unit sphere is nonempty in positive dimension. -/
lemma unitSphere_nonempty (hn : 0 < n) :
    (Metric.sphere (0 : Reference.Space n) 1).Nonempty := by
  let i : Fin n := ⟨0, hn⟩
  refine ⟨EuclideanSpace.single i (1 : ℝ), ?_⟩
  simp

/-- Hahn–Banach supplies a linear functional supported by a real homogeneous
norm at a Euclidean unit vector. -/
lemma supporting_linearMap (q : AddGroupNorm (Reference.Space n))
    (hq : ∀ (a : ℝ) x, q (a • x) = |a| * q x)
    (x : Reference.Space n) (hx : ‖x‖ = 1) :
    ∃ l : Reference.Space n →ₗ[ℝ] ℝ, l x = q x ∧ ∀ y, |l y| ≤ q y := by
  let p : Submodule ℝ (Reference.Space n) := Submodule.span ℝ {x}
  let f : Reference.Space n →ₗ[ℝ] ℝ := q x • (innerSL ℝ x).toLinearMap
  have hdom : ∀ y : p, f y ≤ q y := by
    rintro ⟨y, hy⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    have hii : ⟪x, x⟫_ℝ = 1 := by simpa [hx] using inner_self_eq_norm_sq (𝕜 := ℝ) x
    simp only [f, LinearMap.smul_apply, ContinuousLinearMap.coe_coe,
      innerSL_apply, inner_smul_right, hii, mul_one, smul_eq_mul, hq]
    nlinarith [mul_le_mul_of_nonneg_right (le_abs_self a) (apply_nonneg q x)]
  obtain ⟨l, hlext, hle⟩ := exists_extension_of_le_sublinear (f.toPMap p) q
    (fun a ha y ↦ by rw [hq, abs_of_pos ha])
    (fun y z ↦ map_add_le_add q y z) hdom
  refine ⟨l, ?_, fun y ↦ abs_le.mpr ⟨?_, hle y⟩⟩
  · have h := hlext ⟨x, Submodule.mem_span_singleton_self x⟩
    have hii : ⟪x, x⟫_ℝ = 1 := by simpa [hx] using inner_self_eq_norm_sq (𝕜 := ℝ) x
    simpa [f, p, LinearMap.toPMap, hii] using h
  · have h := hle (-y)
    rw [map_neg, map_neg_eq_map] at h
    linarith

/-- The largest value of a homogeneous norm on the Euclidean unit sphere
bounds that norm on the whole space. -/
lemma norm_le_max_mul_euclidean (q : AddGroupNorm (Reference.Space n))
    (hq : ∀ (a : ℝ) x, q (a • x) = |a| * q x)
    {x : Reference.Space n} (hmax : IsMaxOn q (Metric.sphere 0 1) x)
    (y : Reference.Space n) : q y ≤ q x * ‖y‖ := by
  by_cases hy : y = 0
  · simp [hy]
  have hyn : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hu : ‖y‖⁻¹ • y ∈ Metric.sphere (0 : Reference.Space n) 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using norm_smul_inv_norm (𝕜 := ℝ) hy
  have h := hmax hu
  change q (‖y‖⁻¹ • y) ≤ q x at h
  rw [hq, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))] at h
  have hm := mul_le_mul_of_nonneg_right h hyn.le
  field_simp at hm
  nlinarith

/-- Deterministic duality lemma underlying Lemma 2.1 of the published short
proof (Lemma 3 in arXiv:1205.2515). The unit vector and comparison constant
are constructed, not assumed. -/
theorem exists_small_direction (q : AddGroupNorm (Reference.Space n))
    (hc : Continuous q) (hq : ∀ (a : ℝ) x, q (a • x) = |a| * q x) (hn : 0 < n) :
    ∃ z : Reference.Space n, ∃ r : ℝ, ‖z‖ = 1 ∧ 0 < r ∧
      ∀ y, |⟪z, y⟫_ℝ| ≤ r * q y ∧ r * q y ≤ ‖y‖ := by
  obtain ⟨x, hx, hmax⟩ := (isCompact_sphere (0 : Reference.Space n) 1).exists_isMaxOn
    (unitSphere_nonempty hn) hc.continuousOn
  have hxn : ‖x‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hx
  have hxne : x ≠ 0 := by intro h; simp [h] at hxn
  have hqpos : 0 < q x := map_pos_of_ne_zero q hxne
  obtain ⟨l, hlx, hlq⟩ := supporting_linearMap q hq x hxn
  have hlbound (y : Reference.Space n) : ‖l y‖ ≤ q x * ‖y‖ :=
    (hlq y).trans (norm_le_max_mul_euclidean q hq hmax y)
  let L : Reference.Space n →L[ℝ] ℝ := l.mkContinuous (q x) hlbound
  have hL : ‖L‖ = q x := by
    apply le_antisymm (L.opNorm_le_bound hqpos.le hlbound)
    have h := L.le_opNorm x
    change |l x| ≤ ‖L‖ * ‖x‖ at h
    rw [hlx, abs_of_pos hqpos, hxn, mul_one] at h
    exact h
  let u : Reference.Space n := (InnerProductSpace.toDual ℝ (Reference.Space n)).symm L
  have hun : ‖u‖ = q x := by
    change ‖(InnerProductSpace.toDual ℝ (Reference.Space n)).symm L‖ = q x
    rw [LinearIsometryEquiv.norm_map, hL]
  refine ⟨(q x)⁻¹ • u, (q x)⁻¹, ?_, inv_pos.mpr hqpos, fun y ↦ ⟨?_, ?_⟩⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hqpos), hun,
      inv_mul_cancel₀ hqpos.ne']
  · rw [real_inner_smul_left, abs_mul, abs_of_pos (inv_pos.mpr hqpos)]
    have hu : ⟪u, y⟫_ℝ = l y := InnerProductSpace.toDual_symm_apply
    rw [hu]
    exact mul_le_mul_of_nonneg_left (hlq y) (inv_nonneg.mpr hqpos.le)
  · have h := mul_le_mul_of_nonneg_left
      (norm_le_max_mul_euclidean q hq hmax y) (inv_nonneg.mpr hqpos.le)
    rwa [← mul_assoc, inv_mul_cancel₀ hqpos.ne', one_mul] at h

/-- A genuine continuous homogeneous norm dominates the Euclidean norm in
finite dimension. The constant is obtained from a positive sphere minimum. -/
lemma exists_euclidean_le_mul_norm (q : AddGroupNorm (Reference.Space n))
    (hc : Continuous q) (hq : ∀ (a : ℝ) x, q (a • x) = |a| * q x) (hn : 0 < n) :
    ∃ C : ℝ, 0 < C ∧ ∀ y, ‖y‖ ≤ C * q y := by
  obtain ⟨x, hx, hmin⟩ := (isCompact_sphere (0 : Reference.Space n) 1).exists_isMinOn
    (unitSphere_nonempty hn) hc.continuousOn
  have hxn : ‖x‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hx
  have hxne : x ≠ 0 := by intro h; simp [h] at hxn
  have hqpos : 0 < q x := map_pos_of_ne_zero q hxne
  refine ⟨(q x)⁻¹, inv_pos.mpr hqpos, fun y ↦ ?_⟩
  by_cases hy : y = 0
  · simp [hy]
  have hyn : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hu : ‖y‖⁻¹ • y ∈ Metric.sphere (0 : Reference.Space n) 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using norm_smul_inv_norm (𝕜 := ℝ) hy
  have h := hmin hu
  change q x ≤ q (‖y‖⁻¹ • y) at h
  rw [hq, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))] at h
  have hm := mul_le_mul_of_nonneg_right h hyn.le
  have hmul : q x * ‖y‖ ≤ q y := by
    convert hm using 1
    field_simp
  have hh := mul_le_mul_of_nonneg_left hmul (inv_nonneg.mpr hqpos.le)
  rwa [← mul_assoc, inv_mul_cancel₀ hqpos.ne', one_mul] at hh

/-- A dimension-th-moment comparison for any continuous homogeneous norm
produces an actual Euclidean unit direction with the corresponding strong
moment bound. This is the integral form of the small-direction lemma. -/
theorem exists_direction_moment_le (μ : Measure (Reference.Space n))
    (q : AddGroupNorm (Reference.Space n)) (hc : Continuous q)
    (hq : ∀ (a : ℝ) x, q (a • x) = |a| * q x) (hn : 0 < n)
    (hqi : Integrable q μ) (hqni : Integrable (fun x ↦ q x ^ n) μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hcomp : (∫ x, q x ^ n ∂μ) ^ (1 / (n : ℝ)) ≤ C * ∫ x, q x ∂μ) :
    Integrable (fun x ↦ ‖x‖) μ ∧
    ∃ z : Reference.Space n, ‖z‖ = 1 ∧
      Integrable (fun x ↦ |⟪z, x⟫_ℝ| ^ n) μ ∧
      (∫ x, |⟪z, x⟫_ℝ| ^ n ∂μ) ^ (1 / (n : ℝ)) ≤ C * ∫ x, ‖x‖ ∂μ := by
  obtain ⟨B, hB, hBq⟩ := exists_euclidean_le_mul_norm q hc hq hn
  have hnorm : Integrable (fun x ↦ ‖x‖) μ := by
    apply (hqi.const_mul B).mono' (by fun_prop)
    exact Filter.Eventually.of_forall fun x ↦ by simpa using hBq x
  refine ⟨hnorm, ?_⟩
  obtain ⟨z, r, hzn, hr, hz⟩ := exists_small_direction q hc hq hn
  have hip : Integrable (fun x ↦ |⟪z, x⟫_ℝ| ^ n) μ := by
    apply (hqni.const_mul (r ^ n)).mono' (by fun_prop)
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
    simpa only [mul_pow] using pow_le_pow_left₀ (abs_nonneg _) (hz x).1 n
  refine ⟨z, hzn, hip, ?_⟩
  have hmi : (∫ x, |⟪z, x⟫_ℝ| ^ n ∂μ) ≤ r ^ n * ∫ x, q x ^ n ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono hip (hqni.const_mul (r ^ n))
    intro x
    simpa only [mul_pow] using pow_le_pow_left₀ (abs_nonneg _) (hz x).1 n
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hroot := Real.rpow_le_rpow
    (integral_nonneg fun x ↦ pow_nonneg (abs_nonneg _) _) hmi
    (by positivity : (0 : ℝ) ≤ 1 / (n : ℝ))
  have hqn : 0 ≤ ∫ x, q x ^ n ∂μ := integral_nonneg fun x ↦ pow_nonneg (apply_nonneg q _) _
  rw [Real.mul_rpow (pow_nonneg hr.le _) hqn, ← Real.rpow_natCast,
    ← Real.rpow_mul hr.le, mul_one_div_cancel hnpos.ne', Real.rpow_one] at hroot
  have hmean : r * ∫ x, q x ∂μ ≤ ∫ x, ‖x‖ ∂μ := by
    rw [← integral_const_mul]
    exact integral_mono (hqi.const_mul r) hnorm (fun x ↦ (hz x).2)
  have hcomp' := mul_le_mul_of_nonneg_left hcomp hr.le
  have hmean' := mul_le_mul_of_nonneg_left hmean hC
  nlinarith

/-- The completed first (small-direction) step of the short Paouris proof for
an actual even logconcave probability measure. -/
theorem exists_direction_moment_le_500
    (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    {f : Reference.Space n → ℝ} (hf : Reference.logconcaveDensity f)
    (heven : Function.Even f)
    (hμ : μ = volume.withDensity (fun x ↦ ENNReal.ofReal (f x))) (hn : 0 < n) :
    Integrable (fun x ↦ ‖x‖) μ ∧
    ∃ z : Reference.Space n, ‖z‖ = 1 ∧
      Integrable (fun x ↦ |⟪z, x⟫_ℝ| ^ n) μ ∧
      (∫ x, |⟪z, x⟫_ℝ| ^ n ∂μ) ^ (1 / (n : ℝ)) ≤ 500 * ∫ x, ‖x‖ ∂μ := by
  obtain ⟨q, hc, hq, hqi, hqni, hm⟩ :=
    exists_norm_moment_comparison_probability μ hf heven hμ hn
  exact exists_direction_moment_le μ q hc hq hn hqi hqni (by norm_num) hm

end GaussianTilt.Paouris
