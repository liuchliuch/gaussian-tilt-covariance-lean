import GaussianTilt.Reference.PaperStatements

/-!
# Density-body moment construction in the short proof of Paouris

Starting only from the independent logconcave-density specification, this
module proves the density-body geometry, its continuous gauge, the complete
truncated-integral contraction and moment finiteness, the small-ball lower
first-moment bound, and the dimension-th moment comparison. The subsequent
Paouris modules turn the gauge into a norm and prove the Gaussian comparison
and moment-assembly steps.
-/

noncomputable section
open MeasureTheory Set
open scoped Topology

namespace GaussianTilt.Paouris

variable {n : ℕ} {f : Reference.Space n → ℝ}

/-- A density superlevel set, including its boundary. -/
def superlevel (f : Reference.Space n → ℝ) (c : ℝ) : Set (Reference.Space n) :=
  {x | c ≤ f x}

/-- Multiplicative logconcavity makes every nonnegative superlevel set convex. -/
theorem convex_superlevel (hf : Reference.logconcaveDensity f) {c : ℝ} (hc : 0 ≤ c) :
    Convex ℝ (superlevel f c) := by
  intro x hx y hy a b ha hb hab
  have hm := mul_le_mul (Real.rpow_le_rpow hc hx ha)
    (Real.rpow_le_rpow hc hy hb) (Real.rpow_nonneg hc b) (Real.rpow_nonneg (hf.1 x) a)
  have heq : c ^ a * c ^ b = c := by
    rw [← Real.rpow_add_of_nonneg hc ha hb, hab, Real.rpow_one]
  exact heq ▸ hm.trans (hf.2.2 x y a b ha hb hab)

/-- An even logconcave density is maximized at the origin. -/
theorem density_le_at_zero (hf : Reference.logconcaveDensity f)
    (heven : Function.Even f) (x : Reference.Space n) : f x ≤ f 0 := by
  have h := hf.2.2 x (-x) (1 / 2) (1 / 2) (by norm_num) (by norm_num) (by norm_num)
  rw [heven x, ← Real.rpow_add_of_nonneg (hf.1 x) (by norm_num) (by norm_num)] at h
  norm_num at h
  simpa using h

/-- The midpoint density dominates the geometric mean of the endpoint
and origin densities. This squared form avoids square-root regularity. -/
theorem midpoint_density_sq_ge (hf : Reference.logconcaveDensity f)
    (x : Reference.Space n) : f x * f 0 ≤ f ((1 / 2 : ℝ) • x) ^ 2 := by
  have h := hf.2.2 x 0 (1 / 2) (1 / 2) (by norm_num) (by norm_num) (by norm_num)
  simp only [smul_zero, add_zero, ← Real.sqrt_eq_rpow] at h
  have hs := pow_le_pow_left₀
    (mul_nonneg (Real.sqrt_nonneg (f x)) (Real.sqrt_nonneg (f 0))) h 2
  rwa [mul_pow, Real.sq_sqrt (hf.1 x), Real.sq_sqrt (hf.1 0)] at hs

/-- A low-density point acquires a controlled density gain when moved halfway
back to the center. -/
theorem density_half_ge_mul (hf : Reference.logconcaveDensity f)
    {a : ℝ} (ha : 0 ≤ a) (x : Reference.Space n)
    (hsmall : a ^ 2 * f x ≤ f 0) :
    a * f x ≤ f ((1 / 2 : ℝ) • x) := by
  have hm := mul_le_mul_of_nonneg_right hsmall (hf.1 x)
  have hs := midpoint_density_sq_ge hf x
  have hn : 0 ≤ a * f x := mul_nonneg ha (hf.1 x)
  have hn' := hf.1 ((1 / 2 : ℝ) • x)
  nlinarith

/-- The precise pointwise density comparison outside the `25⁻ⁿ` superlevel
set in the short proof of Paouris. The left side is the density of `2Y`. -/
theorem dilation_density_dominates_outside (hf : Reference.logconcaveDensity f)
    (x : Reference.Space n) (hx : x ∉ superlevel f (f 0 / (25 : ℝ) ^ n)) :
    (5 / 2 : ℝ) ^ n * f x ≤ f ((1 / 2 : ℝ) • x) / (2 : ℝ) ^ n := by
  have hsmall : ((5 : ℝ) ^ n) ^ 2 * f x ≤ f 0 := by
    have hlt : f x < f 0 / (25 : ℝ) ^ n := by simpa only [superlevel, mem_setOf_eq, not_le] using hx
    have hm := (lt_div_iff₀ (show 0 < (25 : ℝ) ^ n by positivity)).mp hlt
    have heq : ((5 : ℝ) ^ n) ^ 2 = (25 : ℝ) ^ n := by
      rw [← pow_mul, Nat.mul_comm, pow_mul]
      norm_num
    rw [heq]
    nlinarith
  have hh := density_half_ge_mul hf (show 0 ≤ (5 : ℝ) ^ n by positivity) x hsmall
  rw [div_pow]
  apply (le_div_iff₀ (show 0 < (2 : ℝ) ^ n by positivity)).mpr
  calc
    (5 ^ n / 2 ^ n * f x) * 2 ^ n = 5 ^ n * f x := by field_simp
    _ ≤ f ((1 / 2 : ℝ) • x) := hh

/-- The defining level set used in the short proof. -/
def densityBody (f : Reference.Space n → ℝ) : Set (Reference.Space n) :=
  superlevel f (f 0 / (25 : ℝ) ^ n)

lemma densityBody_measurable (hf : Reference.logconcaveDensity f) :
    MeasurableSet (densityBody f) :=
  measurableSet_le measurable_const hf.2.1

lemma densityBody_convex (hf : Reference.logconcaveDensity f) :
    Convex ℝ (densityBody f) :=
  convex_superlevel hf (div_nonneg (hf.1 0) (by positivity))

lemma densityBody_neg_mem (heven : Function.Even f) {x : Reference.Space n}
    (hx : x ∈ densityBody f) : -x ∈ densityBody f := by
  simpa only [densityBody, superlevel, mem_setOf_eq, heven x] using hx

/-- Outside the density body the central contraction increases density by `5^n`. -/
lemma densityBody_density_gain (hf : Reference.logconcaveDensity f)
    {x : Reference.Space n} (hx : x ∉ densityBody f) :
    (5 : ℝ) ^ n * f x ≤ f ((1 / 2 : ℝ) • x) := by
  have h := dilation_density_dominates_outside hf x hx
  rw [div_pow] at h
  have h2 : 0 < (2 : ℝ) ^ n := by positivity
  have h' := (le_div_iff₀ h2).mp h
  convert h' using 1
  field_simp

/-- Haar change of variables at exactly the dilation used in the proof. -/
lemma integral_half (g : Reference.Space n → ℝ) :
    (∫ x, g ((1 / 2 : ℝ) • x)) = (2 : ℝ) ^ n * ∫ x, g x := by
  simpa only [one_div, finrank_euclideanSpace_fin, smul_eq_mul] using
    Measure.integral_comp_inv_smul_of_nonneg volume g (show (0 : ℝ) ≤ 2 by norm_num)

/-- The density body has positive volume. This follows from normalization and
logconcavity, rather than an assumed regularity or geometric witness. -/
theorem densityBody_volume_pos (hf : Reference.logconcaveDensity f)
    (hn : 0 < n) (hnorm : ∫ x, f x = 1) :
    0 < volume (densityBody f) := by
  by_contra h
  have hzero : volume (densityBody f) = 0 := le_antisymm (not_lt.mp h) (zero_le _)
  have hae : ∀ᵐ x, x ∉ densityBody f := by
    apply ae_iff.mpr
    simpa using hzero
  have hi := integrable_of_integral_eq_one hnorm
  have hh := hi.comp_smul (show (1 / 2 : ℝ) ≠ 0 by norm_num)
  have hineq := integral_mono_ae (hi.const_mul ((5 : ℝ) ^ n)) hh
    (hae.mono fun x hx ↦ densityBody_density_gain hf hx)
  rw [integral_const_mul, integral_half, hnorm, mul_one, mul_one] at hineq
  have hpow : (2 : ℝ) ^ n < (5 : ℝ) ^ n :=
    pow_lt_pow_left₀ (by norm_num) (by norm_num) (Nat.ne_of_gt hn)
  linarith

/-- A normalized logconcave density has a full-dimensional density body. -/
theorem densityBody_interior_nonempty (hf : Reference.logconcaveDensity f)
    (hn : 0 < n) (hnorm : ∫ x, f x = 1) :
    (interior (densityBody f)).Nonempty := by
  by_contra h
  have hempty := Set.not_nonempty_iff_eq_empty.mp h
  have hsub : densityBody f ⊆ frontier (densityBody f) := by
    rw [frontier, hempty, diff_empty]
    exact subset_closure
  have hz := measure_mono_null hsub ((densityBody_convex hf).addHaar_frontier volume)
  exact (densityBody_volume_pos hf hn hnorm).ne' hz

/-- Symmetry puts the origin in the interior, with no continuity assumption
on the density itself. -/
theorem densityBody_mem_nhds_zero (hf : Reference.logconcaveDensity f)
    (heven : Function.Even f) (hn : 0 < n) (hnorm : ∫ x, f x = 1) :
    densityBody f ∈ 𝓝 0 := by
  obtain ⟨x, hx⟩ := densityBody_interior_nonempty hf hn hnorm
  have heq : (Homeomorph.neg (Reference.Space n)) ⁻¹' densityBody f = densityBody f := by
    ext y
    change f 0 / (25 : ℝ) ^ n ≤ f (-y) ↔ f 0 / (25 : ℝ) ^ n ≤ f y
    rw [heven y]
  have hneg : -x ∈ interior (densityBody f) := by
    change x ∈ (Homeomorph.neg (Reference.Space n)) ⁻¹' interior (densityBody f)
    rw [Homeomorph.preimage_interior, heq]
    exact hx
  have hc := (densityBody_convex hf).interior hx hneg
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  have h0 : (0 : Reference.Space n) ∈ interior (densityBody f) := by simpa using hc
  exact mem_interior_iff_mem_nhds.mp h0

/-- The actual density-level gauge; it is not an abstract norm selected by an
unproved moment comparison. -/
def densityGauge (f : Reference.Space n → ℝ) : Reference.Space n → ℝ :=
  gauge (densityBody f)

lemma densityGauge_nonneg (x : Reference.Space n) : 0 ≤ densityGauge f x :=
  gauge_nonneg x

lemma densityGauge_le_one {x : Reference.Space n} (hx : x ∈ densityBody f) :
    densityGauge f x ≤ 1 := gauge_le_one_of_mem hx

lemma densityGauge_half (x : Reference.Space n) :
    densityGauge f ((1 / 2 : ℝ) • x) = (1 / 2 : ℝ) * densityGauge f x :=
  gauge_smul_of_nonneg (by norm_num) x

lemma densityGauge_continuous (hf : Reference.logconcaveDensity f)
    (heven : Function.Even f) (hn : 0 < n) (hnorm : ∫ x, f x = 1) :
    Continuous (densityGauge f) :=
  continuous_gauge (densityBody_convex hf) (densityBody_mem_nhds_zero hf heven hn hnorm)

/-- Truncating the moment before applying the contraction avoids assuming in
advance that logconcave densities have all moments. -/
def truncatedGaugeMoment (f : Reference.Space n → ℝ) (N : ℕ) (x : Reference.Space n) : ℝ :=
  min (densityGauge f x ^ n) N

lemma truncatedGaugeMoment_nonneg (N : ℕ) (x : Reference.Space n) :
    0 ≤ truncatedGaugeMoment f N x :=
  le_min (pow_nonneg (densityGauge_nonneg x) _) (Nat.cast_nonneg _)

lemma truncatedGaugeMoment_measurable (hf : Reference.logconcaveDensity f)
    (heven : Function.Even f) (hn : 0 < n) (hnorm : ∫ x, f x = 1) (N : ℕ) :
    Measurable (truncatedGaugeMoment f N) :=
  ((densityGauge_continuous hf heven hn hnorm).pow n).measurable.min measurable_const

lemma truncatedGaugeMoment_integrable (hf : Reference.logconcaveDensity f)
    (heven : Function.Even f) (hn : 0 < n) (hnorm : ∫ x, f x = 1) (N : ℕ) :
    Integrable (fun x ↦ truncatedGaugeMoment f N x * f x) := by
  apply (integrable_of_integral_eq_one hnorm).bdd_mul
    (truncatedGaugeMoment_measurable hf heven hn hnorm N).aestronglyMeasurable
  refine ⟨N, fun x ↦ ?_⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (truncatedGaugeMoment_nonneg N x)]
  exact min_le_right _ _

lemma truncatedGaugeMoment_half_le (N : ℕ) (x : Reference.Space n) :
    truncatedGaugeMoment f N x ≤
      (2 : ℝ) ^ n * truncatedGaugeMoment f N ((1 / 2 : ℝ) • x) := by
  have heq : densityGauge f x ^ n =
      (2 : ℝ) ^ n * densityGauge f ((1 / 2 : ℝ) • x) ^ n := by
    rw [densityGauge_half, ← mul_pow]
    congr 1
    ring
  unfold truncatedGaugeMoment
  by_cases h : densityGauge f ((1 / 2 : ℝ) • x) ^ n ≤ (N : ℝ)
  · rw [min_eq_left h]
    exact (min_le_left _ _).trans_eq heq
  · rw [min_eq_right (le_of_not_ge h)]
    exact (min_le_right _ _).trans
      (le_mul_of_one_le_left (Nat.cast_nonneg N) (one_le_pow₀ (by norm_num)))

/-- The genuine pointwise contraction including the inside-body contribution. -/
lemma truncatedGaugeMoment_density_le (hf : Reference.logconcaveDensity f)
    (N : ℕ) (x : Reference.Space n) :
    truncatedGaugeMoment f N x * f x ≤ f x + (2 / 5 : ℝ) ^ n *
      (truncatedGaugeMoment f N ((1 / 2 : ℝ) • x) * f ((1 / 2 : ℝ) • x)) := by
  have hnonneg : 0 ≤ (2 / 5 : ℝ) ^ n *
      (truncatedGaugeMoment f N ((1 / 2 : ℝ) • x) * f ((1 / 2 : ℝ) • x)) :=
    mul_nonneg (by positivity)
      (mul_nonneg (truncatedGaugeMoment_nonneg _ _) (hf.1 _))
  by_cases hx : x ∈ densityBody f
  · have hle : truncatedGaugeMoment f N x ≤ 1 :=
      (min_le_left _ _).trans (pow_le_one₀ (densityGauge_nonneg x) (densityGauge_le_one hx))
    have hm := mul_le_mul_of_nonneg_right hle (hf.1 x)
    nlinarith
  · have hd := densityBody_density_gain hf hx
    have hq := truncatedGaugeMoment_half_le (f := f) N x
    have hmul := mul_le_mul hq hd (mul_nonneg (by positivity) (hf.1 x))
      (mul_nonneg (by positivity) (truncatedGaugeMoment_nonneg _ _))
    have h5 : 0 < (5 : ℝ) ^ n := by positivity
    have hresult : truncatedGaugeMoment f N x * f x ≤ (2 / 5 : ℝ) ^ n *
        (truncatedGaugeMoment f N ((1 / 2 : ℝ) • x) * f ((1 / 2 : ℝ) • x)) := by
      rw [div_pow, div_mul_eq_mul_div]
      apply (le_div_iff₀ h5).mpr
      convert hmul using 1 <;> ring
    linarith [hf.1 x]

/-- Integrated density contraction, proved for every finite truncation. -/
theorem truncatedGaugeMoment_contraction (hf : Reference.logconcaveDensity f)
    (heven : Function.Even f) (hn : 0 < n) (hnorm : ∫ x, f x = 1) (N : ℕ) :
    (∫ x, truncatedGaugeMoment f N x * f x) ≤
      1 + (4 / 5 : ℝ) ^ n * ∫ x, truncatedGaugeMoment f N x * f x := by
  have hi := truncatedGaugeMoment_integrable hf heven hn hnorm N
  have hhalf := hi.comp_smul (show (1 / 2 : ℝ) ≠ 0 by norm_num)
  have hm := integral_mono hi
    ((integrable_of_integral_eq_one hnorm).add (hhalf.const_mul ((2 / 5 : ℝ) ^ n)))
    (truncatedGaugeMoment_density_le hf N)
  simp only [Pi.add_apply] at hm
  rw [integral_add (integrable_of_integral_eq_one hnorm)
    (hhalf.const_mul ((2 / 5 : ℝ) ^ n)), integral_const_mul,
    integral_half (fun x ↦ truncatedGaugeMoment f N x * f x), hnorm] at hm
  convert hm using 1
  rw [← mul_assoc, ← mul_pow]
  norm_num

/-- A uniform bound independent of the truncation. -/
theorem truncatedGaugeMoment_integral_le_five (hf : Reference.logconcaveDensity f)
    (heven : Function.Even f) (hn : 0 < n) (hnorm : ∫ x, f x = 1) (N : ℕ) :
    (∫ x, truncatedGaugeMoment f N x * f x) ≤ 5 := by
  have h := truncatedGaugeMoment_contraction hf heven hn hnorm N
  have hp : (4 / 5 : ℝ) ^ n ≤ 4 / 5 :=
    pow_le_of_le_one (by norm_num) (by norm_num) (Nat.ne_of_gt hn)
  have hm : 0 ≤ ∫ x, truncatedGaugeMoment f N x * f x :=
    integral_nonneg fun x ↦ mul_nonneg (truncatedGaugeMoment_nonneg _ _) (hf.1 _)
  have hh := mul_le_mul_of_nonneg_right hp hm
  linarith

/-- The full dimension-th gauge moment is finite, derived by monotone
convergence from bounded truncations. No moment integrability is assumed. -/
theorem densityGauge_moment_lintegral_le_five (hf : Reference.logconcaveDensity f)
    (heven : Function.Even f) (hn : 0 < n) (hnorm : ∫ x, f x = 1) :
    (∫⁻ x, ENNReal.ofReal (densityGauge f x ^ n * f x)) ≤ 5 := by
  have heq (x : Reference.Space n) :
      ENNReal.ofReal (densityGauge f x ^ n * f x) =
        ⨆ N : ℕ, ENNReal.ofReal (truncatedGaugeMoment f N x * f x) := by
    apply le_antisymm
    · obtain ⟨N, hN⟩ := exists_nat_ge (densityGauge f x ^ n)
      apply le_iSup_of_le N
      simp only [truncatedGaugeMoment, min_eq_left hN, le_refl]
    · apply iSup_le
      intro N
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (min_le_left _ _) (hf.1 _))
  simp_rw [heq]
  rw [lintegral_iSup]
  · apply iSup_le
    intro N
    rw [← ofReal_integral_eq_lintegral_ofReal
      (truncatedGaugeMoment_integrable hf heven hn hnorm N)
      (Filter.Eventually.of_forall fun x ↦
        mul_nonneg (truncatedGaugeMoment_nonneg _ _) (hf.1 _))]
    exact_mod_cast ENNReal.ofReal_le_ofReal
      (truncatedGaugeMoment_integral_le_five hf heven hn hnorm N)
  · intro N
    exact ((truncatedGaugeMoment_measurable hf heven hn hnorm N).mul hf.2.1).ennreal_ofReal
  · intro N M hNM x
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right
      (min_le_min_left _ (Nat.cast_le.mpr hNM)) (hf.1 _)

/-- Integrability of the actual weighted density-gauge moment. -/
theorem densityGauge_moment_integrable (hf : Reference.logconcaveDensity f)
    (heven : Function.Even f) (hn : 0 < n) (hnorm : ∫ x, f x = 1) :
    Integrable (fun x ↦ densityGauge f x ^ n * f x) := by
  refine ⟨(((densityGauge_continuous hf heven hn hnorm).pow n).measurable.mul
    hf.2.1).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall fun x ↦ mul_nonneg
      (pow_nonneg (densityGauge_nonneg _) _) (hf.1 _))]
  exact lt_of_le_of_lt (densityGauge_moment_lintegral_le_five hf heven hn hnorm) (by norm_num)

/-- The dimension-th moment estimate in the density-body proof. -/
theorem densityGauge_moment_le_five (hf : Reference.logconcaveDensity f)
    (heven : Function.Even f) (hn : 0 < n) (hnorm : ∫ x, f x = 1) :
    (∫ x, densityGauge f x ^ n * f x) ≤ 5 := by
  have h := densityGauge_moment_lintegral_le_five hf heven hn hnorm
  rw [← ofReal_integral_eq_lintegral_ofReal
    (densityGauge_moment_integrable hf heven hn hnorm)
    (Filter.Eventually.of_forall fun x ↦ mul_nonneg
      (pow_nonneg (densityGauge_nonneg _) _) (hf.1 _))] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp (by simpa using h)

/-- The gauge's first moment is integrable as a consequence of its proved
`n`-th moment. -/
theorem densityGauge_firstMoment_integrable (hf : Reference.logconcaveDensity f)
    (heven : Function.Even f) (hn : 0 < n) (hnorm : ∫ x, f x = 1) :
    Integrable (fun x ↦ densityGauge f x * f x) := by
  apply ((integrable_of_integral_eq_one hnorm).add
    (densityGauge_moment_integrable hf heven hn hnorm)).mono'
    ((densityGauge_continuous hf heven hn hnorm).measurable.mul hf.2.1).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (densityGauge_nonneg _) (hf.1 _)), Pi.add_apply]
  have h : densityGauge f x ≤ 1 + densityGauge f x ^ n := by
    rcases le_total (densityGauge f x) 1 with h | h
    · linarith [pow_nonneg (densityGauge_nonneg (f := f) x) n]
    · exact (le_self_pow₀ h (Nat.ne_of_gt hn)).trans (le_add_of_nonneg_left zero_le_one)
  have hm := mul_le_mul_of_nonneg_right h (hf.1 x)
  nlinarith

/-- The scaled low-gauge set lies inside the defining density body. -/
lemma fifty_smul_mem_densityBody_of_gauge_lt (hf : Reference.logconcaveDensity f)
    (heven : Function.Even f) (hn : 0 < n) (hnorm : ∫ x, f x = 1)
    {x : Reference.Space n} (hx : densityGauge f x < 1 / 50) :
    (50 : ℝ) • x ∈ densityBody f := by
  apply interior_subset
  rw [← gauge_lt_one_eq_interior (densityBody_convex hf)
    (densityBody_mem_nhds_zero hf heven hn hnorm)]
  change gauge (densityBody f) ((50 : ℝ) • x) < 1
  rw [gauge_smul_of_nonneg (show (0 : ℝ) ≤ 50 by norm_num), smul_eq_mul]
  change 50 * densityGauge f x < 1
  linarith

/-- The small-ball probability estimate in the density-body proof, expressed
as the actual density integral. -/
theorem densityGauge_smallBall_le_half (hf : Reference.logconcaveDensity f)
    (heven : Function.Even f) (hn : 0 < n) (hnorm : ∫ x, f x = 1) :
    (∫ x, {y | densityGauge f y < 1 / 50}.indicator f x) ≤ 1 / 2 := by
  have hset : MeasurableSet {y | densityGauge f y < 1 / 50} :=
    measurableSet_lt (densityGauge_continuous hf heven hn hnorm).measurable measurable_const
  have hi := integrable_of_integral_eq_one hnorm
  have h50 := hi.comp_smul (show (50 : ℝ) ≠ 0 by norm_num)
  have hm := integral_mono (hi.indicator hset) (h50.const_mul ((25 : ℝ) ^ n))
    (show {y | densityGauge f y < 1 / 50}.indicator f ≤
      (fun x ↦ (25 : ℝ) ^ n * f ((50 : ℝ) • x)) from fun x ↦ by
      by_cases hx : densityGauge f x < 1 / 50
      · simp only [Set.indicator, mem_setOf_eq, hx, ↓reduceIte]
        have hbody := fifty_smul_mem_densityBody_of_gauge_lt hf heven hn hnorm hx
        change f 0 / (25 : ℝ) ^ n ≤ f ((50 : ℝ) • x) at hbody
        have h25 : 0 < (25 : ℝ) ^ n := by positivity
        have hh := (div_le_iff₀ h25).mp hbody
        nlinarith [density_le_at_zero hf heven x]
      · simp only [Set.indicator, mem_setOf_eq, hx, ↓reduceIte]
        exact mul_nonneg (by positivity) (hf.1 _))
  rw [integral_const_mul,
    Measure.integral_comp_smul_of_nonneg volume f 50 (hR := by norm_num),
    finrank_euclideanSpace_fin, smul_eq_mul, hnorm, mul_one] at hm
  have heq : (25 : ℝ) ^ n * ((50 : ℝ) ^ n)⁻¹ = (1 / 2 : ℝ) ^ n := by
    rw [← div_eq_mul_inv, ← div_pow]
    norm_num
  rw [heq] at hm
  exact hm.trans (pow_le_of_le_one (by norm_num) (by norm_num) (Nat.ne_of_gt hn))

/-- The lower first-moment bound in the short proof. -/
theorem densityGauge_firstMoment_ge (hf : Reference.logconcaveDensity f)
    (heven : Function.Even f) (hn : 0 < n) (hnorm : ∫ x, f x = 1) :
    (1 / 100 : ℝ) ≤ ∫ x, densityGauge f x * f x := by
  have hi := integrable_of_integral_eq_one hnorm
  have hg := densityGauge_firstMoment_integrable hf heven hn hnorm
  have hset : MeasurableSet {y | densityGauge f y < 1 / 50} :=
    measurableSet_lt (densityGauge_continuous hf heven hn hnorm).measurable measurable_const
  have hind := hi.indicator hset
  have hm := integral_mono hi ((hg.const_mul 50).add hind)
    (show f ≤ (fun x ↦ 50 * (densityGauge f x * f x)) +
      {y | densityGauge f y < 1 / 50}.indicator f from fun x ↦ by
      dsimp only [Pi.add_apply]
      by_cases hx : densityGauge f x < 1 / 50
      · simp only [Set.indicator, mem_setOf_eq, hx, ↓reduceIte]
        have hnonneg := mul_nonneg (densityGauge_nonneg (f := f) x) (hf.1 x)
        linarith
      · simp only [Set.indicator, mem_setOf_eq, hx, ↓reduceIte, add_zero]
        have hge : 1 ≤ 50 * densityGauge f x := by linarith [le_of_not_gt hx]
        have hh := mul_le_mul_of_nonneg_right hge (hf.1 x)
        nlinarith)
  simp only [Pi.add_apply] at hm
  rw [integral_add (hg.const_mul 50) hind, integral_const_mul, hnorm] at hm
  have hsmall := densityGauge_smallBall_le_half hf heven hn hnorm
  linarith

/-- Dimension-th root of the moment, at the constant in the source proof. -/
theorem densityGauge_moment_root_le_five (hf : Reference.logconcaveDensity f)
    (heven : Function.Even f) (hn : 0 < n) (hnorm : ∫ x, f x = 1) :
    (∫ x, densityGauge f x ^ n * f x) ^ (1 / (n : ℝ)) ≤ 5 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hm := (densityGauge_moment_le_five hf heven hn hnorm).trans
    (le_self_pow₀ (show (1 : ℝ) ≤ 5 by norm_num) (Nat.ne_of_gt hn))
  have hnonneg : 0 ≤ ∫ x, densityGauge f x ^ n * f x :=
    integral_nonneg fun x ↦ mul_nonneg (pow_nonneg (densityGauge_nonneg _) _) (hf.1 _)
  have hr := Real.rpow_le_rpow hnonneg hm (by positivity : (0 : ℝ) ≤ 1 / (n : ℝ))
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
    mul_one_div_cancel hnpos.ne', Real.rpow_one] at hr
  exact hr

/-- The quantitative moment comparison from Lemma 2.2 of the published short
proof (Lemma 4 in arXiv:1205.2515), for the explicitly constructed gauge. -/
theorem densityGauge_moment_comparison (hf : Reference.logconcaveDensity f)
    (heven : Function.Even f) (hn : 0 < n) (hnorm : ∫ x, f x = 1) :
    (∫ x, densityGauge f x ^ n * f x) ^ (1 / (n : ℝ)) ≤
      500 * ∫ x, densityGauge f x * f x := by
  have hl := densityGauge_firstMoment_ge hf heven hn hnorm
  have hu := densityGauge_moment_root_le_five hf heven hn hnorm
  linarith

end GaussianTilt.Paouris
