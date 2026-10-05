import GaussianTilt.PaourisTail
import GaussianTilt.DifferenceLaw

/-!
# Symmetrization of the compact Paouris moment estimate

The normalized difference of two independent copies is constructed as an
actual pushforward law. Its isotropy and even compact logconcave density
are proved, and Jensen's inequality transfers its moments to the original law.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators InnerProductSpace

namespace GaussianTilt.Paouris

variable {n : ℕ}

lemma compact_product_ae (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    {K : Set (Reference.Space n)} (hK : IsCompact K) (hμK : μ Kᶜ = 0) :
    ∀ᵐ z ∂μ.prod μ, z ∈ K ×ˢ K := by
  have h : ∀ᵐ x ∂μ, x ∈ K := ae_iff.mpr hμK
  apply (Measure.ae_prod_iff_ae_ae (hK.measurableSet.prod hK.measurableSet)).mpr
  filter_upwards [h] with x hx
  exact h.mono fun y hy ↦ ⟨hx, hy⟩

lemma compact_product_continuous_integrable
    (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hc : Reference.compactlySupported μ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : Reference.Space n × Reference.Space n → E} (hg : Continuous g) :
    Integrable g (μ.prod μ) := by
  obtain ⟨K, hK, hμK⟩ := hc
  obtain ⟨C, hC⟩ := (hK.prod hK).exists_bound_of_continuousOn hg.continuousOn
  exact (MemLp.of_bound (p := 1) hg.aestronglyMeasurable C
    ((compact_product_ae μ hK hμK).mono fun z hz ↦ hC z hz)).integrable le_rfl

lemma compact_vector_integrable (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hc : Reference.compactlySupported μ) : Integrable (fun x ↦ x) μ := by
  obtain ⟨P, rfl⟩ := GaussianTilt.exists_compactProbability_of_compactlySupported μ hc
  exact P.integrable_id

/-- The variance-preserving difference map. -/
def normalizedDifference (z : Reference.Space n × Reference.Space n) : Reference.Space n :=
  (Real.sqrt 2)⁻¹ • (z.1 - z.2)

lemma normalizedDifference_continuous : Continuous (normalizedDifference (n := n)) := by
  unfold normalizedDifference
  fun_prop

/-- The actual normalized independent difference law. -/
def normalizedDifferenceLaw (μ : Measure (Reference.Space n)) : Measure (Reference.Space n) :=
  (μ.prod μ).map normalizedDifference

instance normalizedDifferenceLaw_probability (μ : Measure (Reference.Space n))
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (normalizedDifferenceLaw μ) :=
  Measure.isProbabilityMeasure_map normalizedDifference_continuous.measurable.aemeasurable

lemma normalizedDifferenceLaw_compact (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hc : Reference.compactlySupported μ) :
    Reference.compactlySupported (normalizedDifferenceLaw μ) := by
  obtain ⟨K, hK, hμK⟩ := hc
  let S := normalizedDifference '' (K ×ˢ K)
  have hS : IsCompact S := (hK.prod hK).image normalizedDifference_continuous
  refine ⟨S, hS, ?_⟩
  apply ae_iff.mp
  apply (ae_map_iff normalizedDifference_continuous.measurable.aemeasurable hS.measurableSet).mpr
  exact (compact_product_ae μ hK hμK).mono fun z hz ↦ mem_image_of_mem _ hz

lemma integral_normalizedDifferenceLaw (μ : Measure (Reference.Space n))
    {g : Reference.Space n → ℝ} (hg : Continuous g) :
    (∫ z, g z ∂normalizedDifferenceLaw μ) = ∫ z, g (normalizedDifference z) ∂μ.prod μ :=
  integral_map normalizedDifference_continuous.measurable.aemeasurable hg.aestronglyMeasurable

lemma normalizedDifferenceLaw_mean (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hc : Reference.compactlySupported μ) :
    Reference.mean (normalizedDifferenceLaw μ) = 0 := by
  unfold Reference.mean normalizedDifferenceLaw
  change (∫ x, id x ∂Measure.map normalizedDifference (μ.prod μ)) = 0
  rw [integral_map normalizedDifference_continuous.measurable.aemeasurable
    continuous_id.aestronglyMeasurable]
  simp only [id_eq]
  unfold normalizedDifference
  rw [integral_smul, integral_sub
    ((compact_vector_integrable μ hc).comp_fst μ)
    ((compact_vector_integrable μ hc).comp_snd μ),
    integral_fun_fst (fun x : Reference.Space n ↦ x),
    integral_fun_snd (fun x : Reference.Space n ↦ x)]
  simp

lemma normalizedDifferenceLaw_coordinate_mean (μ : Measure (Reference.Space n))
    [IsProbabilityMeasure μ] (hc : Reference.compactlySupported μ) (i : Fin n) :
    (∫ z, z i ∂normalizedDifferenceLaw μ) = 0 := by
  obtain ⟨P, hP⟩ := GaussianTilt.exists_compactProbability_of_compactlySupported
    (normalizedDifferenceLaw μ) (normalizedDifferenceLaw_compact μ hc)
  have h := P.integral_coordinate_eq_mean i
  rw [hP] at h
  change (∫ z, z i ∂normalizedDifferenceLaw μ) = (Reference.mean (normalizedDifferenceLaw μ)) i at h
  rw [normalizedDifferenceLaw_mean μ hc] at h
  exact h

/-- The covariance of the normalized difference is exactly the original
covariance when the original law is isotropic. -/
theorem normalizedDifferenceLaw_isotropic (μ : Measure (Reference.Space n))
    [IsProbabilityMeasure μ] (hc : Reference.compactlySupported μ)
    (hi : Reference.isotropic μ) : Reference.isotropic (normalizedDifferenceLaw μ) := by
  refine ⟨normalizedDifferenceLaw_mean μ hc, ?_⟩
  ext i j
  simp only [Reference.covariance, normalizedDifferenceLaw_coordinate_mean μ hc,
    zero_mul, sub_zero, Matrix.one_apply]
  rw [integral_normalizedDifferenceLaw μ (by fun_prop)]
  have hI (k l : Fin n) : Integrable (fun x : Reference.Space n ↦ x k * x l) μ :=
    compact_continuous_integrable μ hc (by fun_prop)
  have hC (k : Fin n) : Integrable (fun x : Reference.Space n ↦ x k) μ :=
    compact_continuous_integrable μ hc (by fun_prop)
  have heq : (fun z : Reference.Space n × Reference.Space n ↦
      normalizedDifference z i * normalizedDifference z j) =
      fun z ↦ ((Real.sqrt 2)⁻¹)^2 *
        (z.1 i * z.1 j - z.1 i * z.2 j - z.1 j * z.2 i + z.2 i * z.2 j) := by
    funext z
    simp only [normalizedDifference, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    ring
  have hsub₁ : Integrable (fun z : Reference.Space n × Reference.Space n ↦
      z.1 i * z.1 j - z.1 i * z.2 j) (μ.prod μ) :=
    ((hI i j).comp_fst μ).sub ((hC i).mul_prod (hC j))
  have hsub₂ : Integrable (fun z : Reference.Space n × Reference.Space n ↦
      z.1 i * z.1 j - z.1 i * z.2 j - z.1 j * z.2 i) (μ.prod μ) :=
    hsub₁.sub ((hC j).mul_prod (hC i))
  rw [heq, integral_const_mul, integral_add hsub₂ ((hI i j).comp_snd μ),
    integral_sub hsub₁ ((hC j).mul_prod (hC i)),
    integral_sub ((hI i j).comp_fst μ) ((hC i).mul_prod (hC j)),
    integral_fun_fst (fun x : Reference.Space n ↦ x i * x j),
    integral_fun_snd (fun x : Reference.Space n ↦ x i * x j),
    integral_prod_mul (fun x : Reference.Space n ↦ x i) (fun x : Reference.Space n ↦ x j),
    integral_prod_mul (fun x : Reference.Space n ↦ x j) (fun x : Reference.Space n ↦ x i)]
  simp only [measureReal_univ_eq_one, smul_eq_mul, one_mul,
    isotropic_coordinate_product_integral μ hc hi,
    isotropic_coordinate_mean_zero μ hc hi, zero_mul, sub_zero]
  have hs : ((Real.sqrt 2)⁻¹)^2 = (1 / 2 : ℝ) := by
    rw [inv_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  rw [hs]
  split_ifs <;> norm_num

/-- The normalized difference has a genuine pointwise even compact
logconcave density, obtained by convolution and linear density transport. -/
theorem normalizedDifferenceLaw_even_density
    (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hc : Reference.compactlySupported μ) (hl : Reference.logconcave μ) :
    ∃ f R, Reference.logconcaveDensity f ∧ Function.Even f ∧
      normalizedDifferenceLaw μ = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)) ∧
      (∀ x, R < ‖x‖ → f x = 0) := by
  obtain ⟨f, R, hf, hm, hs, hμ⟩ := LogConcaveLinearImages.exists_compact_density hc hl
  obtain ⟨hg, hgm, hge, hgs, _⟩ := DifferenceLaw.differenceDensity_properties hf hm hs
  let L : Reference.Space n →ₗ[ℝ] Reference.Space n := (Real.sqrt 2)⁻¹ • LinearMap.id
  have hL : Function.Surjective L := by
    intro y
    refine ⟨Real.sqrt 2 • y, ?_⟩
    simp [L, smul_smul, Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)]
  obtain ⟨g, S, hg', hgm', hgs', hmap, heven⟩ :=
    LogConcaveLinearImages.exists_compact_density_map_surjective L hL hg hgm hgs
  refine ⟨g, S, ⟨hg'.1, hgm', hg'.2⟩, heven hge, ?_, hgs'⟩
  rw [← hmap, ← DifferenceLaw.differenceLaw_density hf hm hs, ← hμ,
    Measure.map_map L.continuous_of_finiteDimensional.measurable (by fun_prop)]
  rfl

lemma convexOn_norm_rpow_univ {p : ℝ} (hp : 1 ≤ p) :
    ConvexOn ℝ univ (fun x : Reference.Space n ↦ ‖x‖ ^ p) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have hn := (convexOn_univ_norm (E := Reference.Space n)).2 hx hy ha hb hab
  apply (Real.rpow_le_rpow (norm_nonneg _) hn (by linarith)).trans
  exact (convexOn_rpow hp).2 (norm_nonneg x) (norm_nonneg y) ha hb hab

/-- Jensen's inequality for the second independent copy, then genuine Fubini,
compares original centered moments with normalized-difference moments. -/
theorem normalizedDifference_moment_comparison
    (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hc : Reference.compactlySupported μ) (hmean : Reference.mean μ = 0)
    {p : ℝ} (hp : 1 ≤ p) :
    (∫ x, ‖x‖ ^ p ∂μ) ^ (1 / p) ≤ Real.sqrt 2 *
      (∫ z, ‖z‖ ^ p ∂normalizedDifferenceLaw μ) ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  have hpc : Continuous (fun x : Reference.Space n ↦ ‖x‖ ^ p) :=
    (Real.continuous_rpow_const hp0.le).comp continuous_norm
  have hI : Integrable (fun z : Reference.Space n × Reference.Space n ↦
      ‖normalizedDifference z‖ ^ p) (μ.prod μ) :=
    compact_product_continuous_integrable μ hc (hpc.comp normalizedDifference_continuous)
  have hj (x : Reference.Space n) :
      ((Real.sqrt 2)⁻¹)^p * ‖x‖^p ≤ ∫ y, ‖normalizedDifference (x, y)‖^p ∂μ := by
    have hfi : Integrable (fun y : Reference.Space n ↦ normalizedDifference (x, y)) μ :=
      by simpa only [normalizedDifference, Pi.smul_apply, Pi.sub_apply] using
        ((integrable_const x).sub (compact_vector_integrable μ hc)).smul ((Real.sqrt 2)⁻¹)
    have hgi : Integrable (fun y : Reference.Space n ↦ ‖normalizedDifference (x, y)‖ ^ p) μ :=
      compact_continuous_integrable μ hc (hpc.comp (by unfold normalizedDifference; fun_prop))
    have h := (convexOn_norm_rpow_univ hp).map_integral_le hpc.continuousOn isClosed_univ
      (Eventually.of_forall fun _ ↦ mem_univ _) hfi hgi
    have hm : (∫ y, normalizedDifference (x, y) ∂μ) = (Real.sqrt 2)⁻¹ • x := by
      unfold normalizedDifference
      rw [integral_smul, integral_sub (integrable_const x) (compact_vector_integrable μ hc)]
      change (Real.sqrt 2)⁻¹ • ((∫ _ : Reference.Space n, x ∂μ) - Reference.mean μ) = _
      rw [hmean]
      simp
    rw [hm, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (Real.sqrt 2)⁻¹),
      Real.mul_rpow (by positivity) (norm_nonneg _)] at h
    exact h
  have hJ := integral_mono
    ((compact_continuous_integrable μ hc hpc).const_mul (((Real.sqrt 2)⁻¹)^p))
    hI.integral_prod_left hj
  rw [integral_const_mul, ← integral_prod _ hI,
    ← integral_normalizedDifferenceLaw μ hpc] at hJ
  have hroot := Real.rpow_le_rpow
    (mul_nonneg (Real.rpow_nonneg (by positivity) _) (integral_nonneg fun x ↦ by positivity))
    hJ (by positivity : 0 ≤ 1 / p)
  rw [Real.mul_rpow (Real.rpow_nonneg (by positivity) _) (integral_nonneg fun x ↦ by positivity),
    ← Real.rpow_mul (by positivity : 0 ≤ (Real.sqrt 2)⁻¹),
    mul_one_div_cancel hp0.ne', Real.rpow_one] at hroot
  have hs : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have h := mul_le_mul_of_nonneg_left hroot hs.le
  simpa only [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul] using h

/-- Universal moment factor after symmetrization. -/
def generalCompactPaourisMomentConstant : ℝ := 2 * compactPaourisMomentConstant

lemma generalCompactPaourisMomentConstant_pos : 0 < generalCompactPaourisMomentConstant :=
  mul_pos (by norm_num) compactPaourisMomentConstant_pos

/-- The strong Paouris moment bound for every actual compact isotropic
logconcave law, without a symmetry assumption or an assumed analytic estimate. -/
theorem compact_isotropic_moment_le
    (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hc : Reference.compactlySupported μ) (hl : Reference.logconcave μ)
    (hi : Reference.isotropic μ) {p : ℝ} (hp : 2 ≤ p) :
    (∫ x, ‖x‖ ^ p ∂μ) ^ (1 / p) ≤
      generalCompactPaourisMomentConstant * (Real.sqrt (n : ℝ) + p) := by
  obtain ⟨f, R, hf, he, hν, hs⟩ := normalizedDifferenceLaw_even_density μ hc hl
  have h := compact_even_isotropic_moment_le (normalizedDifferenceLaw μ)
    (normalizedDifferenceLaw_compact μ hc) (normalizedDifferenceLaw_isotropic μ hc hi)
    hf he hν hs hp
  have hsym := normalizedDifference_moment_comparison μ hc hi.1 (by linarith : 1 ≤ p)
  have hsqrt : Real.sqrt (2 : ℝ) ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  calc
    (∫ x, ‖x‖ ^ p ∂μ) ^ (1 / p)
        ≤ Real.sqrt 2 * ((∫ z, ‖z‖ ^ p ∂normalizedDifferenceLaw μ) ^ (1 / p)) := hsym
    _ ≤ Real.sqrt 2 * (compactPaourisMomentConstant * (Real.sqrt (n : ℝ) + p)) :=
      mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg _)
    _ ≤ 2 * (compactPaourisMomentConstant * (Real.sqrt (n : ℝ) + p)) :=
      mul_le_mul_of_nonneg_right hsqrt
        (mul_nonneg compactPaourisMomentConstant_pos.le (by positivity))
    _ = generalCompactPaourisMomentConstant * (Real.sqrt (n : ℝ) + p) := by
      unfold generalCompactPaourisMomentConstant
      ring

/-- Universal threshold factor for general compact logconcave laws. -/
def generalCompactPaourisTailConstant : ℝ :=
  3 * Real.exp 1 * generalCompactPaourisMomentConstant

lemma generalCompactPaourisTailConstant_pos : 0 < generalCompactPaourisTailConstant :=
  mul_pos (mul_pos (by norm_num) (Real.exp_pos _)) generalCompactPaourisMomentConstant_pos

/-- Paouris's norm tail for every compact isotropic logconcave probability law. -/
theorem compact_isotropic_norm_tail
    (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hc : Reference.compactlySupported μ) (hl : Reference.logconcave μ)
    (hi : Reference.isotropic μ) {t : ℝ} (ht : 1 ≤ t) :
    μ.real {x | generalCompactPaourisTailConstant * t * Real.sqrt (n : ℝ) ≤ ‖x‖} ≤
      Real.exp (-t * Real.sqrt (n : ℝ)) := by
  apply norm_tail_of_all_positive_moments μ generalCompactPaourisMomentConstant_pos _ ht
  intro p hp
  exact ⟨compact_continuous_integrable μ hc
      ((Real.continuous_rpow_const (by linarith : 0 ≤ p)).comp continuous_norm),
    compact_isotropic_moment_le μ hc hl hi hp⟩

end GaussianTilt.Paouris
