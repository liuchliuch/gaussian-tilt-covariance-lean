import GaussianTilt.PaourisImageMoments
import GaussianTilt.ScalarLogConcaveMomentsLayercake
import GaussianTilt.Energy

/-!
# Isotropic weak moments and the compact even Paouris bound

Scalar projections are actual pushforward probability densities. Their unit
variance is calculated from the independent reference covariance, allowing
the proved one-dimensional logconcave moment theorem to be applied.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators InnerProductSpace

namespace GaussianTilt.Paouris

variable {n : ℕ}

lemma compact_continuous_integrable (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hc : Reference.compactlySupported μ) {g : Reference.Space n → ℝ} (hg : Continuous g) :
    Integrable g μ := (compact_memLp_continuous μ hc hg 1).integrable le_rfl

lemma isotropic_coordinate_mean_zero (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hc : Reference.compactlySupported μ) (hi : Reference.isotropic μ) (i : Fin n) :
    (∫ x, x i ∂μ) = 0 := by
  obtain ⟨P, rfl⟩ := GaussianTilt.exists_compactProbability_of_compactlySupported μ hc
  exact P.isotropic_integral_coordinate hi i

lemma isotropic_coordinate_product_integral (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hc : Reference.compactlySupported μ) (hi : Reference.isotropic μ) (i j : Fin n) :
    (∫ x, x i * x j ∂μ) = if i = j then 1 else 0 := by
  have h := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ ↦ A i j) hi.2
  simpa only [Reference.covariance, isotropic_coordinate_mean_zero μ hc hi,
    zero_mul, sub_zero, Matrix.one_apply] using h

lemma inner_sq_coordinate_expansion (a x : Reference.Space n) :
    ⟪a, x⟫_ℝ ^ 2 = ∑ i : Fin n, ∑ j : Fin n, (a i * a j) * (x i * x j) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, RCLike.conj_to_real, pow_two,
    Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Exact second moment of every scalar projection under the original
reference isotropy condition. -/
theorem isotropic_inner_sq_integral (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hc : Reference.compactlySupported μ) (hi : Reference.isotropic μ) (a : Reference.Space n) :
    (∫ x, ⟪a, x⟫_ℝ ^ 2 ∂μ) = ‖a‖ ^ 2 := by
  have hf (i j : Fin n) : Integrable (fun x : Reference.Space n ↦ (a i * a j) * (x i * x j)) μ :=
    compact_continuous_integrable μ hc (by fun_prop)
  simp_rw [inner_sq_coordinate_expansion]
  rw [integral_finset_sum _ (fun i _ ↦ integrable_finset_sum _ (fun j _ ↦ hf i j))]
  simp_rw [integral_finset_sum _ (fun j _ ↦ hf _ j), integral_const_mul,
    isotropic_coordinate_product_integral μ hc hi]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hn := EuclideanSpace.norm_sq_eq a
  simp only [Real.norm_eq_abs, sq_abs] at hn
  simpa only [pow_two] using hn.symm

lemma isotropic_norm_sq_integral (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hc : Reference.compactlySupported μ) (hi : Reference.isotropic μ) :
    (∫ x : Reference.Space n, ‖x‖ ^ 2 ∂μ) = n := by
  obtain ⟨P, rfl⟩ := GaussianTilt.exists_compactProbability_of_compactlySupported μ hc
  simpa only [P.expectation_zero, GaussianTilt.energy] using P.isotropic_initial_energy hi

lemma isotropic_mean_norm_le_sqrt (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hc : Reference.compactlySupported μ) (hi : Reference.isotropic μ) :
    (∫ x : Reference.Space n, ‖x‖ ∂μ) ≤ Real.sqrt (n : ℝ) := by
  have h := (even_two.convexOn_pow (𝕜 := ℝ)).map_integral_le
    (μ := μ) (f := fun x : Reference.Space n ↦ ‖x‖)
    (by fun_prop) isClosed_univ (Filter.Eventually.of_forall fun _ ↦ mem_univ _)
    (compact_continuous_integrable μ hc continuous_norm)
    (compact_continuous_integrable μ hc (continuous_norm.pow 2))
  rw [isotropic_norm_sq_integral μ hc hi] at h
  exact (Real.le_sqrt (integral_nonneg (fun x ↦ norm_nonneg x)) (Nat.cast_nonneg n)).mpr h

lemma real_densityLaw_integral {g : ℝ → ℝ} (hg : Measurable g) (hgn : ∀ x, 0 ≤ g x) (φ : ℝ → ℝ) :
    (∫ x, φ x ∂volume.withDensity (fun x ↦ ENNReal.ofReal (g x))) = ∫ x, φ x * g x := by
  have h := integral_withDensity_eq_integral_toReal_smul (μ := volume) hg.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top) φ
  simpa only [ENNReal.toReal_ofReal (hgn _), smul_eq_mul, mul_comm] using h

/-- The scalar weak-moment estimate applied to actual unit projections of
an even compact isotropic logconcave law. -/
theorem even_isotropic_unit_moment_le
    (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hc : Reference.compactlySupported μ) (hi : Reference.isotropic μ)
    {f : Reference.Space n → ℝ} (hf : Reference.logconcaveDensity f)
    (heven : Function.Even f) (hμ : μ = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)))
    {R : ℝ} (hR : ∀ x, R < ‖x‖ → f x = 0)
    (a : Reference.Space n) (ha : ‖a‖ = 1) {p : ℝ} (hp : 2 ≤ p) :
    (∫ x, |⟪a, x⟫_ℝ| ^ p ∂μ) ^ (1 / p) ≤ 48 * p := by
  let L : Reference.Space n →L[ℝ] ℝ := innerSL ℝ a
  have hL : Function.Surjective L := by
    intro s
    refine ⟨s • a, ?_⟩
    change ⟪a, s • a⟫_ℝ = s
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq, ha]
    ring
  obtain ⟨g, S, hg, hgm, hgS, hmap, hge⟩ :=
    LogConcaveLinearImages.exists_compact_density_map_surjective L.toLinearMap hL
      ⟨hf.1, hf.2.2⟩ hf.2.1 hR
  let ν : Measure ℝ := μ.map L
  haveI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map L.measurable.aemeasurable
  have hν : ν = volume.withDensity (fun y ↦ ENNReal.ofReal (g y)) := by
    change μ.map L = _
    rw [hμ]
    exact hmap
  have hmass : ∫ y, g y = 1 := by
    have h := real_densityLaw_integral hgm hg.1 (fun _ ↦ 1)
    rw [← hν] at h
    simpa only [one_mul, integral_const, measureReal_univ_eq_one, smul_eq_mul, mul_one] using h.symm
  have hsecond : (∫ y, y ^ 2 * g y) = 1 := by
    rw [← real_densityLaw_integral hgm hg.1 (fun y ↦ y ^ 2), ← hν]
    rw [show ν = μ.map L from rfl, integral_map L.measurable.aemeasurable (by fun_prop)]
    change (∫ x, ⟪a, x⟫_ℝ ^ 2 ∂μ) = 1
    rw [isotropic_inner_sq_integral μ hc hi a, ha]
    norm_num
  have hsupport : ∃ A B : ℝ, ∀ y ∉ Icc A B, g y = 0 := by
    refine ⟨-max S 0, max S 0, fun y hy ↦ hgS y ?_⟩
    have hnot : ¬ |y| ≤ max S 0 := fun h ↦ hy (abs_le.mp h)
    have hlt : max S 0 < |y| := lt_of_not_ge hnot
    simpa only [Real.norm_eq_abs] using lt_of_le_of_lt (le_max_left S 0) hlt
  have h := ScalarLogConcaveMoments.even_logconcave_moment_le hg hgm hsupport (hge heven) hmass hsecond hp
  rw [← real_densityLaw_integral hgm hg.1 (fun y ↦ |y| ^ p), ← hν] at h
  have hpow : Continuous (fun y : ℝ ↦ |y| ^ p) :=
    (Real.continuous_rpow_const (show 0 ≤ p by linarith)).comp continuous_abs
  rw [show ν = μ.map L from rfl, integral_map L.measurable.aemeasurable hpow.aestronglyMeasurable] at h
  exact h

/-- A universal constant for the compact even isotropic moment bound. -/
def compactPaourisMomentConstant : ℝ := 48 * strongWeakConstant

lemma compactPaourisMomentConstant_pos : 0 < compactPaourisMomentConstant := by
  unfold compactPaourisMomentConstant strongWeakConstant
  exact mul_pos (by norm_num) (div_pos (by norm_num) scalarGaussianLowerConstant_pos)

/-- Paouris's positive-moment bound for compact even isotropic logconcave
probabilities, with every external analytic ingredient now proved. -/
theorem compact_even_isotropic_moment_le
    (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hc : Reference.compactlySupported μ) (hi : Reference.isotropic μ)
    {f : Reference.Space n → ℝ} (hf : Reference.logconcaveDensity f)
    (heven : Function.Even f) (hμ : μ = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)))
    {R : ℝ} (hR : ∀ x, R < ‖x‖ → f x = 0)
    {p : ℝ} (hp : 2 ≤ p) :
    (∫ x : Reference.Space n, ‖x‖ ^ p ∂μ) ^ (1 / p) ≤
      compactPaourisMomentConstant * (Real.sqrt (n : ℝ) + p) := by
  have hAC : μ ≪ volume := by rw [hμ]; exact withDensity_absolutelyContinuous _ _
  let L : ℝ≥0 := ⟨48 * p, by linarith⟩
  have h := compact_even_strong_weak μ hc hAC hf heven hμ hR hp (L := L)
    (fun a ha ↦ even_isotropic_unit_moment_le μ hc hi hf heven hμ hR a ha hp)
  have hm := isotropic_mean_norm_le_sqrt μ hc hi
  have hC : 0 < strongWeakConstant := by
    unfold strongWeakConstant
    exact div_pos (by norm_num) scalarGaussianLowerConstant_pos
  change _ ≤ strongWeakConstant * ((∫ x : Reference.Space n, ‖x‖ ∂μ) + 48 * p) at h
  unfold compactPaourisMomentConstant
  nlinarith [Real.sqrt_nonneg (n : ℝ)]

end GaussianTilt.Paouris
