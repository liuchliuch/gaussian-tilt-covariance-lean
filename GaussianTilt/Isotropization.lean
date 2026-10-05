import GaussianTilt.Geometry
import GaussianTilt.Reference.PaperStatements

/-!
# Uniform law, coordinate symmetries, and diagonal scaling

All integrals below use the normalized restriction of actual Lebesgue measure
to the explicitly constructed body, not an abstract moment model.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal

namespace GaussianTilt

private instance rawVolume_isAddLeftInvariant (d : ℕ) :
    (volume : Measure (RawPoint d)).IsAddLeftInvariant where
  map_add_left_eq_self p :=
    ((measurePreserving_add_left (volume : Measure (Fin d → ℝ)) p.1).prod
      (measurePreserving_add_left (volume : Measure ℝ) p.2)).map_eq

instance rawVolume_isAddHaarMeasure (d : ℕ) :
    (volume : Measure (RawPoint d)).IsAddHaarMeasure := ⟨⟩

/-- The genuine uniform law of the raw body. -/
def rawUniform (d : ℕ) (Δ : ℝ) : Measure (RawPoint d) :=
  ProbabilityTheory.cond volume (rawBodyWith d Δ)

theorem rawBodyWith_volume_pos (d : ℕ) {Δ : ℝ} (hroom : 0 < (d : ℝ) - 2 * Δ) :
    0 < volume (rawBodyWith d Δ) :=
  Measure.measure_pos_of_nonempty_interior volume ⟨0, zero_mem_interior_rawBodyWith d hroom⟩

theorem rawUniform_isProbabilityMeasure (d : ℕ) {Δ : ℝ} (hΔ : 0 < Δ)
    (hroom : 0 < (d : ℝ) - 2 * Δ) : IsProbabilityMeasure (rawUniform d Δ) :=
  ProbabilityTheory.cond_isProbabilityMeasure_of_finite
    (rawBodyWith_volume_pos d hroom).ne' (rawBodyWith_isCompact d hΔ).measure_ne_top

theorem continuous_integrable_rawUniform {d : ℕ} {Δ : ℝ} (hΔ : 0 < Δ)
    (hroom : 0 < (d : ℝ) - 2 * Δ) {f : RawPoint d → ℝ} (hf : Continuous f) :
    Integrable f (rawUniform d Δ) := by
  exact (ContinuousOn.integrableOn_compact (rawBodyWith_isCompact d hΔ) hf.continuousOn).smul_measure
    (ENNReal.inv_ne_top.mpr (rawBodyWith_volume_pos d hroom).ne')

private theorem boolNeg_measurePreserving (b : Bool) :
    MeasurePreserving (fun x : ℝ => if b then -x else x) := by
  cases b
  · exact MeasurePreserving.id volume
  · exact Measure.measurePreserving_neg volume

theorem signChange_volume_preserving {d : ℕ} (s : Fin d → Bool) (axial : Bool) :
    MeasurePreserving (signChange s axial) := by
  exact (volume_preserving_pi fun i => boolNeg_measurePreserving (s i)).prod
    (boolNeg_measurePreserving axial)

def signChangeMeasurableEquiv {d : ℕ} (s : Fin d → Bool) (axial : Bool) :
    RawPoint d ≃ᵐ RawPoint d where
  toFun := signChange s axial
  invFun := signChange s axial
  left_inv := signChange_involutive s axial
  right_inv := signChange_involutive s axial
  measurable_toFun := (signChange_volume_preserving s axial).measurable
  measurable_invFun := (signChange_volume_preserving s axial).measurable

theorem signChange_rawUniform_preserving {d : ℕ} (Δ : ℝ) (s : Fin d → Bool)
    (axial : Bool) : MeasurePreserving (signChange s axial) (rawUniform d Δ) (rawUniform d Δ) := by
  have hpre : signChange s axial ⁻¹' rawBodyWith d Δ = rawBodyWith d Δ := by
    ext p
    exact signChange_mem_rawBodyWith_iff Δ s axial p
  have hm := (signChange_volume_preserving s axial).restrict_preimage
    (rawBodyWith_isClosed d Δ).measurableSet
  rw [hpre] at hm
  exact hm.smul_measure _

theorem integral_signChange_rawUniform {d : ℕ} (Δ : ℝ) (s : Fin d → Bool)
    (axial : Bool) (f : RawPoint d → ℝ) :
    ∫ p, f (signChange s axial p) ∂rawUniform d Δ = ∫ p, f p ∂rawUniform d Δ :=
  (signChange_rawUniform_preserving Δ s axial).integral_comp
    (signChangeMeasurableEquiv s axial).measurableEmbedding f

/-- Every transverse coordinate of the actual uniform law is centered. -/
theorem rawUniform_transverse_mean_zero {d : ℕ} (Δ : ℝ) (i : Fin d) :
    ∫ p, p.1 i ∂rawUniform d Δ = 0 := by
  have h := integral_signChange_rawUniform Δ (fun _ => true) false (fun p => p.1 i)
  simp only [signChange, ↓reduceIte, integral_neg] at h
  linarith

/-- The axial coordinate of the actual uniform law is centered. -/
theorem rawUniform_axial_mean_zero {d : ℕ} (Δ : ℝ) :
    ∫ p, p.2 ∂rawUniform d Δ = 0 := by
  have h := integral_signChange_rawUniform (d := d) Δ (fun _ => false) true (fun p => p.2)
  simp only [signChange, ↓reduceIte, integral_neg] at h
  linarith

/-- Off-diagonal transverse moments vanish by reflecting exactly one coordinate. -/
theorem rawUniform_transverse_cross_zero {d : ℕ} (Δ : ℝ) (i j : Fin d) (hij : i ≠ j) :
    ∫ p, p.1 i * p.1 j ∂rawUniform d Δ = 0 := by
  have h := integral_signChange_rawUniform Δ (fun k => decide (k = i)) false
    (fun p => p.1 i * p.1 j)
  simp only [signChange, decide_true, ↓reduceIte, decide_eq_true_eq] at h
  simp only [hij.symm, ↓reduceIte, neg_mul, integral_neg] at h
  linarith

theorem rawUniform_axial_transverse_cross_zero {d : ℕ} (Δ : ℝ) (i : Fin d) :
    ∫ p, p.1 i * p.2 ∂rawUniform d Δ = 0 := by
  have h := integral_signChange_rawUniform Δ (fun _ => false) true
    (fun p => p.1 i * p.2)
  simp [signChange, mul_neg, integral_neg] at h
  linarith

def transversePermuteMeasurableEquiv {d : ℕ} (σ : Equiv.Perm (Fin d)) :
    RawPoint d ≃ᵐ RawPoint d where
  toFun := transversePermute σ
  invFun := transversePermute σ.symm
  left_inv := by intro p; ext i <;> simp [transversePermute]
  right_inv := by intro p; ext i <;> simp [transversePermute]
  measurable_toFun := by change Measurable (transversePermute σ); unfold transversePermute; fun_prop
  measurable_invFun := by change Measurable (transversePermute σ.symm); unfold transversePermute; fun_prop

theorem transversePermute_volume_preserving {d : ℕ} (σ : Equiv.Perm (Fin d)) :
    MeasurePreserving (transversePermute σ) := by
  convert (volume_measurePreserving_piCongrLeft (fun _ : Fin d => ℝ) σ.symm).prod
    (MeasurePreserving.id (volume : Measure ℝ)) using 1
  ext p i <;> simp [transversePermute, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]

theorem transversePermute_rawUniform_preserving {d : ℕ} (Δ : ℝ)
    (σ : Equiv.Perm (Fin d)) : MeasurePreserving (transversePermute σ)
      (rawUniform d Δ) (rawUniform d Δ) := by
  have hpre : transversePermute σ ⁻¹' rawBodyWith d Δ = rawBodyWith d Δ := by
    ext p
    exact transversePermute_mem_rawBodyWith_iff Δ σ p
  have hm := (transversePermute_volume_preserving σ).restrict_preimage
    (rawBodyWith_isClosed d Δ).measurableSet
  rw [hpre] at hm
  exact hm.smul_measure _

/-- All transverse coordinates have the same second moment. -/
theorem rawUniform_transverse_secondMoment_eq {d : ℕ} (Δ : ℝ) (i j : Fin d) :
    ∫ p, (p.1 i)^2 ∂rawUniform d Δ = ∫ p, (p.1 j)^2 ∂rawUniform d Δ := by
  have h := (transversePermute_rawUniform_preserving Δ (Equiv.swap i j)).integral_comp
    (transversePermuteMeasurableEquiv (Equiv.swap i j)).measurableEmbedding
    (fun p => (p.1 i)^2)
  simpa only [transversePermute, Equiv.swap_apply_left] using h.symm

/-- A coordinate-wise diagonal map, with distinct transverse and axial factors. -/
def diagonalScale {d : ℕ} (a b : ℝ) (p : RawPoint d) : RawPoint d :=
  ((fun i => a * p.1 i), b * p.2)

@[simp] theorem diagonalScale_comp {d : ℕ} (a b c e : ℝ) (p : RawPoint d) :
    diagonalScale a b (diagonalScale c e p) = diagonalScale (a*c) (b*e) p := by
  ext i <;> simp [diagonalScale, mul_assoc]

@[simp] theorem diagonalScale_one {d : ℕ} (p : RawPoint d) : diagonalScale 1 1 p = p := by
  ext i <;> simp [diagonalScale]

theorem diagonalScale_signChange {d : ℕ} (a b : ℝ) (s : Fin d → Bool) (axial : Bool)
    (p : RawPoint d) : diagonalScale a b (signChange s axial p) =
      signChange s axial (diagonalScale a b p) := by
  ext i <;> simp [diagonalScale, signChange] <;> split <;> simp_all

def diagonalScaleLinearMap (d : ℕ) (a b : ℝ) : RawPoint d →ₗ[ℝ] RawPoint d where
  toFun := diagonalScale a b
  map_add' := by intro p q; ext i <;> simp [diagonalScale, mul_add]
  map_smul' := by intro c p; ext i <;> simp [diagonalScale, mul_left_comm]

theorem continuous_diagonalScale (d : ℕ) (a b : ℝ) :
    Continuous (diagonalScale (d := d) a b) := by
  unfold diagonalScale
  fun_prop

def isotropizedBody (d : ℕ) (Δ a b : ℝ) : Set (RawPoint d) :=
  diagonalScale (Real.sqrt a)⁻¹ (Real.sqrt b)⁻¹ '' rawBodyWith d Δ

theorem isotropizedBody_convex (d : ℕ) {Δ : ℝ} (hΔ : 0 ≤ Δ) (a b : ℝ) :
    Convex ℝ (isotropizedBody d Δ a b) :=
  (rawBodyWith_convex d hΔ).linear_image (diagonalScaleLinearMap d _ _)

theorem isotropizedBody_isCompact (d : ℕ) {Δ : ℝ} (hΔ : 0 < Δ) (a b : ℝ) :
    IsCompact (isotropizedBody d Δ a b) :=
  (rawBodyWith_isCompact d hΔ).image (continuous_diagonalScale d _ _)

theorem signChange_mem_isotropizedBody {d : ℕ} (Δ a b : ℝ) (s : Fin d → Bool)
    (axial : Bool) {p : RawPoint d} (hp : p ∈ isotropizedBody d Δ a b) :
    signChange s axial p ∈ isotropizedBody d Δ a b := by
  obtain ⟨q, hq, rfl⟩ := hp
  exact ⟨signChange s axial q, (signChange_mem_rawBodyWith_iff Δ s axial q).mpr hq,
    diagonalScale_signChange _ _ _ _ _⟩

/-- Inverse coordinate identity in Corollary 4.8. -/
theorem isotropization_inverse {d : ℕ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (p : RawPoint d) : diagonalScale (Real.sqrt a) (Real.sqrt b)
      (diagonalScale (Real.sqrt a)⁻¹ (Real.sqrt b)⁻¹ p) = p := by
  rw [diagonalScale_comp, mul_inv_cancel₀ (Real.sqrt_pos.mpr ha).ne',
    mul_inv_cancel₀ (Real.sqrt_pos.mpr hb).ne', diagonalScale_one]


/-- Any nonzero linear functional has a positive square moment on this
full-dimensional uniform law. This also certifies nondegeneracy. -/
theorem rawUniform_linear_square_pos {d : ℕ} {Δ : ℝ} (hΔ : 0 < Δ)
    (hroom : 0 < (d : ℝ) - 2 * Δ) (f : RawPoint d →ₗ[ℝ] ℝ)
    (hf : ∃ v, f v ≠ 0) : 0 < ∫ p, (f p)^2 ∂rawUniform d Δ := by
  obtain ⟨v, hv⟩ := hf
  have hc : Continuous (fun t : ℝ => t • v) := by fun_prop
  have hzero := zero_mem_interior_rawBodyWith d hroom
  have hn : (fun t : ℝ => t • v) ⁻¹' interior (rawBodyWith d Δ) ∈ 𝓝 (0 : ℝ) := by
    apply hc.continuousAt.preimage_mem_nhds
    simpa using isOpen_interior.mem_nhds hzero
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hn
  have ht : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
    simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
    linarith
  have hpoint : (ε / 2) • v ∈ interior (rawBodyWith d Δ) := hball ht
  have hfpoint : (f ((ε / 2) • v))^2 ≠ 0 := by
    simp only [map_smul, smul_eq_mul]
    exact pow_ne_zero 2 (mul_ne_zero (ne_of_gt (half_pos hε)) hv)
  have hcont : Continuous (fun p : RawPoint d => (f p)^2) :=
    f.continuous_of_finiteDimensional.pow 2
  have hvol : 0 < volume (Function.support (fun p : RawPoint d => (f p)^2) ∩
      rawBodyWith d Δ) := by
    apply lt_of_lt_of_le ((hcont.isOpen_support.inter isOpen_interior).measure_pos volume
      ⟨(ε/2) • v, hfpoint, hpoint⟩)
    exact measure_mono (inter_subset_inter_right _ interior_subset)
  have hint : 0 < ∫ p in rawBodyWith d Δ, (f p)^2 := by
    apply (setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ (fun p => sq_nonneg _))
      (ContinuousOn.integrableOn_compact (rawBodyWith_isCompact d hΔ) hcont.continuousOn)).2
    exact hvol
  change 0 < ∫ p, (f p)^2 ∂((volume (rawBodyWith d Δ))⁻¹ • volume.restrict (rawBodyWith d Δ))
  rw [integral_smul_measure, smul_eq_mul]
  exact mul_pos (ENNReal.toReal_pos
    (ENNReal.inv_ne_zero.mpr (rawBodyWith_isCompact d hΔ).measure_ne_top)
    (ENNReal.inv_ne_top.mpr (rawBodyWith_volume_pos d hroom).ne')) hint

/-- An index distinguishes the axial coordinate (`none`) from transverse ones. -/
def rawCoordinate {d : ℕ} : Option (Fin d) → RawPoint d → ℝ
  | none => fun p => p.2
  | some i => fun p => p.1 i

def rawCoordinateLinearMap (d : ℕ) (i : Option (Fin d)) : RawPoint d →ₗ[ℝ] ℝ where
  toFun := rawCoordinate i
  map_add' := by cases i <;> intros <;> rfl
  map_smul' := by cases i <;> intros <;> rfl

theorem rawCoordinate_nonzero (d : ℕ) (i : Option (Fin d)) :
    ∃ p, rawCoordinate i p ≠ 0 := by
  cases i with
  | none => exact ⟨(0,1), by simp [rawCoordinate]⟩
  | some i => exact ⟨(fun _ => 1,0), by simp [rawCoordinate]⟩

theorem rawUniform_coordinate_mean_zero {d : ℕ} (Δ : ℝ) (i : Option (Fin d)) :
    ∫ p, rawCoordinate i p ∂rawUniform d Δ = 0 := by
  cases i with
  | none => exact rawUniform_axial_mean_zero Δ
  | some i => exact rawUniform_transverse_mean_zero Δ i

theorem rawUniform_coordinate_secondMoment_pos {d : ℕ} {Δ : ℝ} (hΔ : 0 < Δ)
    (hroom : 0 < (d : ℝ) - 2 * Δ) (i : Option (Fin d)) :
    0 < ∫ p, (rawCoordinate i p)^2 ∂rawUniform d Δ :=
  rawUniform_linear_square_pos hΔ hroom (rawCoordinateLinearMap d i) (rawCoordinate_nonzero d i)

theorem rawUniform_coordinate_cross_zero {d : ℕ} (Δ : ℝ) (i j : Option (Fin d))
    (hij : i ≠ j) : ∫ p, rawCoordinate i p * rawCoordinate j p ∂rawUniform d Δ = 0 := by
  cases i with
  | none => cases j with
    | none => exact (hij rfl).elim
    | some j => simpa [rawCoordinate, mul_comm] using rawUniform_axial_transverse_cross_zero Δ j
  | some i => cases j with
    | none => exact rawUniform_axial_transverse_cross_zero Δ i
    | some j => exact rawUniform_transverse_cross_zero Δ i j (by simpa using hij)

/-- The covariance matrix, using centered second products of actual coordinates. -/
def rawCovarianceMatrix (d : ℕ) (Δ : ℝ) : Matrix (Option (Fin d)) (Option (Fin d)) ℝ :=
  fun i j => (∫ p, rawCoordinate i p * rawCoordinate j p ∂rawUniform d Δ) -
    (∫ p, rawCoordinate i p ∂rawUniform d Δ) * (∫ p, rawCoordinate j p ∂rawUniform d Δ)

theorem rawCovarianceMatrix_eq_diagonal (d : ℕ) (Δ : ℝ) :
    rawCovarianceMatrix d Δ = Matrix.diagonal
      (fun i => ∫ p, (rawCoordinate i p)^2 ∂rawUniform d Δ) := by
  ext i j
  simp only [rawCovarianceMatrix, rawUniform_coordinate_mean_zero, zero_mul, sub_zero]
  by_cases hij : i = j
  · subst j
    simp [Matrix.diagonal_apply, sq]
  · simp [Matrix.diagonal_apply, hij, rawUniform_coordinate_cross_zero Δ i j hij]

/-- The exact diagonal covariance shape and strict positivity asserted by Lemma 4.2. -/
theorem rawUniform_covariance_shape {d : ℕ} {Δ : ℝ} (hd : 0 < d) (hΔ : 0 < Δ)
    (hroom : 0 < (d : ℝ) - 2 * Δ) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ rawCovarianceMatrix d Δ =
      Matrix.diagonal (fun i => match i with | none => b | some _ => a) := by
  let i : Fin d := ⟨0, hd⟩
  refine ⟨∫ p, (p.1 i)^2 ∂rawUniform d Δ, ∫ p, p.2^2 ∂rawUniform d Δ,
    rawUniform_coordinate_secondMoment_pos hΔ hroom (some i),
    rawUniform_coordinate_secondMoment_pos hΔ hroom none, ?_⟩
  rw [rawCovarianceMatrix_eq_diagonal]
  congr 1
  funext j
  cases j with
  | none => rfl
  | some j => exact rawUniform_transverse_secondMoment_eq Δ j i


def diagonalScaleLinearEquiv (d : ℕ) {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    RawPoint d ≃ₗ[ℝ] RawPoint d where
  __ := diagonalScaleLinearMap d a b
  invFun := diagonalScale a⁻¹ b⁻¹
  left_inv := by intro p; change diagonalScale a⁻¹ b⁻¹ (diagonalScale a b p) = p; simp [ha, hb]
  right_inv := by intro p; change diagonalScale a b (diagonalScale a⁻¹ b⁻¹ p) = p; simp [ha, hb]

theorem zero_mem_interior_isotropizedBody (d : ℕ) {Δ a b : ℝ}
    (hroom : 0 < (d : ℝ) - 2 * Δ) (ha : 0 < a) (hb : 0 < b) :
    (0 : RawPoint d) ∈ interior (isotropizedBody d Δ a b) := by
  let e := (diagonalScaleLinearEquiv d
    (inv_ne_zero (Real.sqrt_pos.mpr ha).ne')
    (inv_ne_zero (Real.sqrt_pos.mpr hb).ne')).toContinuousLinearEquiv.toHomeomorph
  apply e.isOpenMap.image_interior_subset (rawBodyWith d Δ)
  exact ⟨0, zero_mem_interior_rawBodyWith d hroom, by
    change diagonalScale (Real.sqrt a)⁻¹ (Real.sqrt b)⁻¹ 0 = 0
    ext i <;> simp [diagonalScale]⟩

/-- Conditioning commutes with an invertible measurable change of coordinates. -/
theorem map_cond_image {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (e : E ≃ᵐ F) (μ : Measure E) {s : Set E} (hs : MeasurableSet s) :
    Measure.map e (ProbabilityTheory.cond μ s) =
      ProbabilityTheory.cond (Measure.map e μ) (e '' s) := by
  have himg := e.measurableSet_image.mpr hs
  have hpre : e ⁻¹' (e '' s) = s := e.injective.preimage_image s
  rw [ProbabilityTheory.cond, ProbabilityTheory.cond, Measure.map_smul,
    Measure.map_apply e.measurable himg, Measure.restrict_map e.measurable himg, hpre]

/-- Normalization removes a finite positive scalar multiple of the reference measure. -/
theorem cond_smul_measure {E : Type*} [MeasurableSpace E] (μ : Measure E) (s : Set E)
    {c : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ⊤) :
    ProbabilityTheory.cond (c • μ) s = ProbabilityTheory.cond μ s := by
  unfold ProbabilityTheory.cond
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.mul_inv (Or.inl hc0) (Or.inl hct),
    Measure.restrict_smul, smul_smul]
  congr 1
  calc
    (c⁻¹ * (μ s)⁻¹) * c = (μ s)⁻¹ * (c⁻¹ * c) := by ac_rfl
    _ = (μ s)⁻¹ := by rw [ENNReal.inv_mul_cancel hc0 hct, mul_one]

/-- An invertible linear map sends the uniform law to the uniform law of its image. -/
theorem map_uniform_linearEquiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (e : E ≃ₗ[ℝ] E) {s : Set E} (hs : MeasurableSet s) :
    Measure.map e (ProbabilityTheory.cond μ s) = ProbabilityTheory.cond μ (e '' s) := by
  let em := e.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have h := map_cond_image em μ hs
  change Measure.map e (ProbabilityTheory.cond μ s) =
    ProbabilityTheory.cond (Measure.map e μ) (e '' s) at h
  rw [h]
  have hm := Measure.map_linearMap_addHaar_eq_smul_addHaar μ e.isUnit_det'.ne_zero
  simp only [LinearEquiv.coe_coe] at hm
  rw [hm]
  exact cond_smul_measure μ _ (by
    apply ENNReal.ofReal_ne_zero_iff.mpr
    exact abs_pos.mpr (inv_ne_zero e.isUnit_det'.ne_zero)) ENNReal.ofReal_ne_top

def isotropizedUniform (d : ℕ) (Δ a b : ℝ) : Measure (RawPoint d) :=
  ProbabilityTheory.cond volume (isotropizedBody d Δ a b)

theorem map_rawUniform_isotropized {d : ℕ} (Δ : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Measure.map (diagonalScale (Real.sqrt a)⁻¹ (Real.sqrt b)⁻¹) (rawUniform d Δ) =
      isotropizedUniform d Δ a b :=
  map_uniform_linearEquiv volume (diagonalScaleLinearEquiv d
    (inv_ne_zero (Real.sqrt_pos.mpr ha).ne') (inv_ne_zero (Real.sqrt_pos.mpr hb).ne'))
    (rawBodyWith_isClosed d Δ).measurableSet

theorem integral_isotropizedUniform {d : ℕ} (Δ : ℝ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (f : RawPoint d → ℝ) :
    ∫ p, f p ∂isotropizedUniform d Δ a b =
      ∫ p, f (diagonalScale (Real.sqrt a)⁻¹ (Real.sqrt b)⁻¹ p) ∂rawUniform d Δ := by
  rw [← map_rawUniform_isotropized Δ ha hb]
  exact (diagonalScaleLinearEquiv d (inv_ne_zero (Real.sqrt_pos.mpr ha).ne')
    (inv_ne_zero (Real.sqrt_pos.mpr hb).ne')).toContinuousLinearEquiv.toHomeomorph.measurableEmbedding.integral_map f

/-- The actual (common) raw transverse variance, indexed by any transverse coordinate. -/
def rawTransverseVariance {d : ℕ} (Δ : ℝ) (i : Fin d) : ℝ :=
  ∫ p, (p.1 i)^2 ∂rawUniform d Δ

def rawAxialVariance (d : ℕ) (Δ : ℝ) : ℝ := ∫ p, p.2^2 ∂rawUniform d Δ

theorem rawTransverseVariance_pos {d : ℕ} {Δ : ℝ} (hΔ : 0 < Δ)
    (hroom : 0 < (d : ℝ) - 2 * Δ) (i : Fin d) : 0 < rawTransverseVariance Δ i :=
  rawUniform_coordinate_secondMoment_pos hΔ hroom (some i)

theorem rawAxialVariance_pos {d : ℕ} {Δ : ℝ} (hΔ : 0 < Δ)
    (hroom : 0 < (d : ℝ) - 2 * Δ) : 0 < rawAxialVariance d Δ :=
  rawUniform_coordinate_secondMoment_pos hΔ hroom none

def coordinateScale {d : ℕ} (a b : ℝ) : Option (Fin d) → ℝ
  | none => b
  | some _ => a

@[simp] theorem rawCoordinate_diagonalScale {d : ℕ} (a b : ℝ) (i : Option (Fin d))
    (p : RawPoint d) : rawCoordinate i (diagonalScale a b p) =
      coordinateScale a b i * rawCoordinate i p := by
  cases i <;> rfl

theorem isotropizedUniform_mean_zero {d : ℕ} (Δ : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (i : Option (Fin d)) : ∫ p, rawCoordinate i p ∂isotropizedUniform d Δ a b = 0 := by
  rw [integral_isotropizedUniform Δ ha hb]
  simp only [rawCoordinate_diagonalScale, integral_const_mul, rawUniform_coordinate_mean_zero,
    mul_zero]

theorem isotropizedUniform_cross_moment {d : ℕ} (Δ : ℝ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (i j : Option (Fin d)) :
    ∫ p, rawCoordinate i p * rawCoordinate j p ∂isotropizedUniform d Δ a b =
      coordinateScale (Real.sqrt a)⁻¹ (Real.sqrt b)⁻¹ i *
      coordinateScale (Real.sqrt a)⁻¹ (Real.sqrt b)⁻¹ j *
      ∫ p, rawCoordinate i p * rawCoordinate j p ∂rawUniform d Δ := by
  rw [integral_isotropizedUniform Δ ha hb]
  simp only [rawCoordinate_diagonalScale]
  calc
    _ = ∫ p, (coordinateScale (Real.sqrt a)⁻¹ (Real.sqrt b)⁻¹ i *
      coordinateScale (Real.sqrt a)⁻¹ (Real.sqrt b)⁻¹ j) *
      (rawCoordinate i p * rawCoordinate j p) ∂rawUniform d Δ := by
        congr 1; funext p; ring
    _ = _ := integral_const_mul _ _

theorem inv_sqrt_sq_mul_self {a : ℝ} (ha : 0 < a) : (Real.sqrt a)⁻¹ * (Real.sqrt a)⁻¹ * a = 1 := by
  have hsq := Real.sq_sqrt ha.le
  have hn := (Real.sqrt_pos.mpr ha).ne'
  field_simp
  nlinarith

/-- The actual uniformly distributed transformed body is centered and has
identity covariance; the factors are its raw variances, not assumed moments. -/
theorem actual_isotropization_second_moment {d : ℕ} {Δ : ℝ} (hΔ : 0 < Δ)
    (hroom : 0 < (d : ℝ) - 2 * Δ) (i₀ : Fin d) (i j : Option (Fin d)) :
    ∫ p, rawCoordinate i p * rawCoordinate j p
      ∂isotropizedUniform d Δ (rawTransverseVariance Δ i₀) (rawAxialVariance d Δ) =
        if i = j then 1 else 0 := by
  have ha := rawTransverseVariance_pos hΔ hroom i₀
  have hb := rawAxialVariance_pos hΔ hroom
  rw [isotropizedUniform_cross_moment Δ ha hb]
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
    cases i with
    | none => simpa only [coordinateScale, rawCoordinate, ← sq, rawAxialVariance] using
        inv_sqrt_sq_mul_self hb
    | some i =>
      simp only [coordinateScale, rawCoordinate, ← sq]
      rw [rawUniform_transverse_secondMoment_eq Δ i i₀]
      simpa only [sq, rawTransverseVariance] using inv_sqrt_sq_mul_self ha
  · rw [rawUniform_coordinate_cross_zero Δ i j hij, mul_zero, if_neg hij]


/-- Concatenate the axial coordinate first, followed by the transverse coordinates. -/
def rawToPiLinearEquiv (d : ℕ) : RawPoint d ≃ₗ[ℝ] (Fin (d+1) → ℝ) where
  toFun p := Fin.cons p.2 p.1
  invFun y := (fun i => y i.succ, y 0)
  left_inv := by intro p; ext i <;> simp
  right_inv := by intro y; funext i; exact Fin.cases rfl (fun _ => rfl) i
  map_add' := by intro p q; funext i; exact Fin.cases rfl (fun _ => rfl) i
  map_smul' := by intro c p; funext i; exact Fin.cases rfl (fun _ => rfl) i

/-- The actual linear coordinate bridge to the independent Euclidean specification. -/
def rawToEuclidean (d : ℕ) : RawPoint d ≃ₗ[ℝ] Reference.Space (d+1) :=
  (rawToPiLinearEquiv d).trans
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (d+1) => ℝ)).symm.toLinearEquiv

@[simp] theorem rawToEuclidean_zero_coordinate (d : ℕ) (p : RawPoint d) :
    rawToEuclidean d p 0 = p.2 := rfl

@[simp] theorem rawToEuclidean_succ_coordinate (d : ℕ) (p : RawPoint d) (i : Fin d) :
    rawToEuclidean d p i.succ = p.1 i := rfl

/-- The indexing function used to identify raw and Euclidean coordinates. -/
def rawIndex {d : ℕ} (i : Fin (d+1)) : Option (Fin d) := Fin.cases none some i

@[simp] theorem rawToEuclidean_coordinate (d : ℕ) (p : RawPoint d) (i : Fin (d+1)) :
    rawToEuclidean d p i = rawCoordinate (rawIndex i) p := by
  exact Fin.cases rfl (fun _ => rfl) i

theorem rawIndex_injective (d : ℕ) : Function.Injective (rawIndex (d := d)) := by
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · simp
  · simp [rawIndex]
  · simp [rawIndex]
  · simp [rawIndex]

theorem rawToPi_volume_preserving (d : ℕ) : MeasurePreserving (rawToPiLinearEquiv d) := by
  let e := (rawToPiLinearEquiv d).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have hi : MeasurePreserving e.symm := by
    convert Measure.measurePreserving_swap.comp
      (volume_preserving_piFinSuccAbove (fun _ : Fin (d+1) => ℝ) 0) using 1
  exact hi.symm e.symm

theorem rawToEuclidean_volume_preserving (d : ℕ) : MeasurePreserving (rawToEuclidean d) :=
  (PiLp.volume_preserving_toLp (Fin (d+1))).comp (rawToPi_volume_preserving d)

/-- The Euclidean realization of the explicit isotropized body. -/
def euclideanBody {d : ℕ} (Δ : ℝ) (i₀ : Fin d) : Set (Reference.Space (d+1)) :=
  rawToEuclidean d '' isotropizedBody d Δ (rawTransverseVariance Δ i₀) (rawAxialVariance d Δ)

theorem euclideanBody_convexBody {d : ℕ} {Δ : ℝ} (hΔ : 0 < Δ)
    (hroom : 0 < (d : ℝ) - 2 * Δ) (i₀ : Fin d) : Reference.convexBody (euclideanBody Δ i₀) := by
  have ha := rawTransverseVariance_pos hΔ hroom i₀
  have hb := rawAxialVariance_pos hΔ hroom
  refine ⟨(isotropizedBody_convex d hΔ.le _ _).linear_image (rawToEuclidean d).toLinearMap,
    (isotropizedBody_isCompact d hΔ _ _).image
      (rawToEuclidean d).continuous_of_finiteDimensional, ?_⟩
  refine ⟨0, ?_⟩
  apply (rawToEuclidean d).toContinuousLinearEquiv.toHomeomorph.isOpenMap.image_interior_subset
  exact ⟨0, zero_mem_interior_isotropizedBody d hroom ha hb, by simp⟩

theorem map_isotropizedUniform_euclidean {d : ℕ} {Δ : ℝ} (hΔ : 0 < Δ) (i₀ : Fin d) :
    Measure.map (rawToEuclidean d)
      (isotropizedUniform d Δ (rawTransverseVariance Δ i₀) (rawAxialVariance d Δ)) =
        Reference.uniform (euclideanBody Δ i₀) := by
  let e := (rawToEuclidean d).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have h := map_cond_image e volume (isotropizedBody_isCompact d hΔ
    (rawTransverseVariance Δ i₀) (rawAxialVariance d Δ)).measurableSet
  change Measure.map (rawToEuclidean d)
    (isotropizedUniform d Δ (rawTransverseVariance Δ i₀) (rawAxialVariance d Δ)) =
      ProbabilityTheory.cond (Measure.map (rawToEuclidean d) volume) (euclideanBody Δ i₀) at h
  rw [(rawToEuclidean_volume_preserving d).map_eq] at h
  exact h

theorem integral_euclideanBody {d : ℕ} {Δ : ℝ} (hΔ : 0 < Δ) (i₀ : Fin d)
    (f : Reference.Space (d+1) → ℝ) :
    ∫ x, f x ∂(Reference.uniform (euclideanBody Δ i₀)) =
      ∫ p, f (rawToEuclidean d p)
        ∂isotropizedUniform d Δ (rawTransverseVariance Δ i₀) (rawAxialVariance d Δ) := by
  rw [← map_isotropizedUniform_euclidean hΔ i₀]
  exact (rawToEuclidean d).toContinuousLinearEquiv.toHomeomorph.measurableEmbedding.integral_map f

theorem euclideanBody_coordinate_mean_zero {d : ℕ} {Δ : ℝ} (hΔ : 0 < Δ)
    (hroom : 0 < (d : ℝ) - 2 * Δ) (i₀ : Fin d) (i : Fin (d+1)) :
    ∫ x, x i ∂(Reference.uniform (euclideanBody Δ i₀)) = 0 := by
  rw [integral_euclideanBody hΔ i₀]
  simp only [rawToEuclidean_coordinate]
  exact isotropizedUniform_mean_zero Δ (rawTransverseVariance_pos hΔ hroom i₀)
    (rawAxialVariance_pos hΔ hroom) _

theorem euclideanBody_isotropic {d : ℕ} {Δ : ℝ} (hΔ : 0 < Δ)
    (hroom : 0 < (d : ℝ) - 2 * Δ) (i₀ : Fin d) :
    Reference.isotropic (Reference.uniform (euclideanBody Δ i₀)) := by
  have hK := euclideanBody_convexBody hΔ hroom i₀
  have hvol := Measure.measure_pos_of_nonempty_interior volume hK.2.2
  have hint : Integrable (fun x : Reference.Space (d+1) => x)
      (Reference.uniform (euclideanBody Δ i₀)) :=
    (ContinuousOn.integrableOn_compact hK.2.1 continuous_id.continuousOn).smul_measure
      (ENNReal.inv_ne_top.mpr hvol.ne')
  constructor
  · ext i
    change (EuclideanSpace.proj i) (∫ x, x ∂(Reference.uniform (euclideanBody Δ i₀))) = 0
    rw [← (EuclideanSpace.proj i).integral_comp_comm hint]
    exact euclideanBody_coordinate_mean_zero hΔ hroom i₀ i
  · ext i j
    simp only [Reference.covariance, euclideanBody_coordinate_mean_zero hΔ hroom i₀,
      zero_mul, sub_zero]
    rw [integral_euclideanBody hΔ i₀]
    simp only [rawToEuclidean_coordinate]
    rw [actual_isotropization_second_moment hΔ hroom i₀]
    simp only [(rawIndex_injective d).eq_iff, Matrix.one_apply]

theorem euclideanBody_unconditional {d : ℕ} {Δ : ℝ} (i₀ : Fin d) :
    Reference.unconditional (euclideanBody Δ i₀) := by
  classical
  intro x hx ε hε
  obtain ⟨p, hp, rfl⟩ := hx
  let s : Fin d → Bool := fun i => decide (ε i.succ = -1)
  let axial : Bool := decide (ε 0 = -1)
  refine ⟨signChange s axial p, signChange_mem_isotropizedBody _ _ _ s axial hp, ?_⟩
  ext i
  refine Fin.cases ?_ (fun i => ?_) i
  · rcases hε 0 with h | h <;> norm_num [signChange, rawIndex, rawCoordinate, axial, h]
  · rcases hε i.succ with h | h <;> norm_num [signChange, rawIndex, rawCoordinate, s, h]

/-- The explicit body is an unconditional isotropic convex body for every dimension
satisfying the elementary geometric condition; no asymptotic covariance estimate
is assumed in this construction. -/
theorem euclideanBody_certified {d : ℕ} {Δ : ℝ} (hΔ : 0 < Δ)
    (hroom : 0 < (d : ℝ) - 2 * Δ) (i₀ : Fin d) :
    Reference.convexBody (euclideanBody Δ i₀) ∧
    Reference.unconditional (euclideanBody Δ i₀) ∧
    Reference.isotropic (Reference.uniform (euclideanBody Δ i₀)) :=
  ⟨euclideanBody_convexBody hΔ hroom i₀, euclideanBody_unconditional i₀,
    euclideanBody_isotropic hΔ hroom i₀⟩


/-- The Euclidean energy is the coordinate sum of squares, not the auxiliary
product norm used for topology on `RawPoint`. -/
theorem rawToEuclidean_norm_sq (d : ℕ) (p : RawPoint d) :
    ‖rawToEuclidean d p‖^2 = transverseEnergy p + p.2^2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
  simp only [rawToEuclidean_zero_coordinate, rawToEuclidean_succ_coordinate,
    Real.norm_eq_abs, sq_abs, transverseEnergy]
  ring

theorem transverseEnergy_diagonalScale {d : ℕ} (a b : ℝ) (p : RawPoint d) :
    transverseEnergy (diagonalScale a b p) = a^2 * transverseEnergy p := by
  simp only [transverseEnergy, diagonalScale, mul_pow, Finset.mul_sum]

/-- The complete linear map from the raw body to its Euclidean isotropic image. -/
def rawIsotropization (d : ℕ) (a b : ℝ) (p : RawPoint d) : Reference.Space (d+1) :=
  rawToEuclidean d (diagonalScale (Real.sqrt a)⁻¹ (Real.sqrt b)⁻¹ p)

def rawIsotropizationEquiv (d : ℕ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    RawPoint d ≃ₗ[ℝ] Reference.Space (d+1) :=
  (diagonalScaleLinearEquiv d (inv_ne_zero (Real.sqrt_pos.mpr ha).ne')
    (inv_ne_zero (Real.sqrt_pos.mpr hb).ne')).trans (rawToEuclidean d)

theorem rawIsotropization_norm_sq {d : ℕ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (p : RawPoint d) : ‖rawIsotropization d a b p‖^2 = transverseEnergy p / a + p.2^2 / b := by
  rw [rawIsotropization, rawToEuclidean_norm_sq, transverseEnergy_diagonalScale]
  simp only [diagonalScale, mul_pow, inv_pow, Real.sq_sqrt ha.le, Real.sq_sqrt hb.le,
    div_eq_mul_inv]
  ring

theorem map_rawUniform_euclideanBody {d : ℕ} {Δ : ℝ} (hΔ : 0 < Δ)
    (hroom : 0 < (d : ℝ) - 2 * Δ) (i₀ : Fin d) :
    Measure.map (rawIsotropization d (rawTransverseVariance Δ i₀) (rawAxialVariance d Δ))
      (rawUniform d Δ) = Reference.uniform (euclideanBody Δ i₀) := by
  have he : Measurable (rawToEuclidean d : RawPoint d → Reference.Space (d+1)) :=
    (rawToEuclidean d).toContinuousLinearEquiv.toHomeomorph.measurable
  rw [show rawIsotropization d (rawTransverseVariance Δ i₀) (rawAxialVariance d Δ) =
    rawToEuclidean d ∘ diagonalScale (Real.sqrt (rawTransverseVariance Δ i₀))⁻¹
      (Real.sqrt (rawAxialVariance d Δ))⁻¹ by rfl,
    ← Measure.map_map he (continuous_diagonalScale d _ _).measurable,
    map_rawUniform_isotropized Δ (rawTransverseVariance_pos hΔ hroom i₀)
      (rawAxialVariance_pos hΔ hroom), map_isotropizedUniform_euclidean hΔ i₀]

/-- Transporting a density along a measurable embedding transports the base measure. -/
theorem map_withDensity_comp {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    {e : E → F} (he : MeasurableEmbedding e) (μ : Measure E) (f : F → ℝ≥0∞) :
    Measure.map e (μ.withDensity (fun p => f (e p))) = (Measure.map e μ).withDensity f := by
  ext s hs
  rw [Measure.map_apply he.measurable hs, withDensity_apply _ (he.measurable hs),
    withDensity_apply _ hs, Measure.restrict_map he.measurable hs, he.lintegral_map]

/-- The anisotropic raw energy forced by diagonal isotropization. -/
def rawGaussianWeight {d : ℕ} (a b t : ℝ) (p : RawPoint d) : ℝ :=
  Real.exp (-t * (transverseEnergy p / a + p.2^2 / b))

def rawTiltPartition (d : ℕ) (Δ a b t : ℝ) : ℝ :=
  ∫ p, rawGaussianWeight a b t p ∂rawUniform d Δ

def rawTilt (d : ℕ) (Δ a b t : ℝ) : Measure (RawPoint d) :=
  (rawUniform d Δ).withDensity (fun p =>
    ENNReal.ofReal (rawGaussianWeight a b t p / rawTiltPartition d Δ a b t))

theorem euclideanBody_partition_eq_raw {d : ℕ} {Δ : ℝ} (hΔ : 0 < Δ)
    (hroom : 0 < (d : ℝ) - 2 * Δ) (i₀ : Fin d) (t : ℝ) :
    Reference.partition (Reference.uniform (euclideanBody Δ i₀)) t =
      rawTiltPartition d Δ (rawTransverseVariance Δ i₀) (rawAxialVariance d Δ) t := by
  unfold Reference.partition
  rw [← map_rawUniform_euclideanBody hΔ hroom i₀]
  have hi : (∫ x, Real.exp (-t * ‖x‖^2)
      ∂Measure.map (rawIsotropization d (rawTransverseVariance Δ i₀) (rawAxialVariance d Δ))
        (rawUniform d Δ)) = ∫ p, Real.exp (-t * ‖rawIsotropization d
          (rawTransverseVariance Δ i₀) (rawAxialVariance d Δ) p‖^2) ∂rawUniform d Δ :=
    (rawIsotropizationEquiv d (rawTransverseVariance_pos hΔ hroom i₀)
      (rawAxialVariance_pos hΔ hroom)).toContinuousLinearEquiv.toHomeomorph.measurableEmbedding.integral_map _
  rw [hi]
  change (∫ p, Real.exp (-t * ‖rawIsotropization d (rawTransverseVariance Δ i₀)
    (rawAxialVariance d Δ) p‖^2) ∂rawUniform d Δ) = _
  simp only [rawIsotropization_norm_sq (rawTransverseVariance_pos hΔ hroom i₀)
    (rawAxialVariance_pos hΔ hroom)]
  rfl

/-- The exact Gaussian-tilt pushforward bridge used for axial Fubini analysis. -/
theorem euclideanBody_gaussianTilt_eq_map_rawTilt {d : ℕ} {Δ : ℝ} (hΔ : 0 < Δ)
    (hroom : 0 < (d : ℝ) - 2 * Δ) (i₀ : Fin d) (t : ℝ) :
    Reference.gaussianTilt (Reference.uniform (euclideanBody Δ i₀)) t =
      Measure.map (rawIsotropization d (rawTransverseVariance Δ i₀) (rawAxialVariance d Δ))
        (rawTilt d Δ (rawTransverseVariance Δ i₀) (rawAxialVariance d Δ) t) := by
  let e := (rawIsotropizationEquiv d (rawTransverseVariance_pos hΔ hroom i₀)
    (rawAxialVariance_pos hΔ hroom)).toContinuousLinearEquiv.toHomeomorph
  have hm := map_withDensity_comp e.measurableEmbedding (rawUniform d Δ)
    (fun x => ENNReal.ofReal (Real.exp (-t * ‖x‖^2) /
      Reference.partition (Reference.uniform (euclideanBody Δ i₀)) t))
  change Measure.map (rawIsotropization d (rawTransverseVariance Δ i₀) (rawAxialVariance d Δ))
    ((rawUniform d Δ).withDensity (fun p => ENNReal.ofReal
      (Real.exp (-t * ‖rawIsotropization d (rawTransverseVariance Δ i₀) (rawAxialVariance d Δ) p‖^2) /
      Reference.partition (Reference.uniform (euclideanBody Δ i₀)) t))) = _ at hm
  rw [show (e : RawPoint d → Reference.Space (d+1)) = rawIsotropization d
    (rawTransverseVariance Δ i₀) (rawAxialVariance d Δ) by rfl] at hm
  rw [map_rawUniform_euclideanBody hΔ hroom i₀] at hm
  rw [Reference.gaussianTilt, ← hm]
  congr 1
  congr 1
  funext p
  rw [rawIsotropization_norm_sq (rawTransverseVariance_pos hΔ hroom i₀)
    (rawAxialVariance_pos hΔ hroom), euclideanBody_partition_eq_raw hΔ hroom i₀]
  rfl


/-- The easy transverse upper bound in Lemma 4.7. -/
theorem rawTransverseVariance_le_three {d : ℕ} {Δ : ℝ} (hΔ : 0 < Δ)
    (hroom : 0 < (d : ℝ) - 2 * Δ) (i : Fin d) : rawTransverseVariance Δ i ≤ 3 := by
  letI := rawUniform_isProbabilityMeasure d hΔ hroom
  have hi : Integrable (fun p : RawPoint d => (p.1 i)^2) (rawUniform d Δ) :=
    continuous_integrable_rawUniform hΔ hroom (by fun_prop)
  have hb : ∀ᵐ p ∂rawUniform d Δ, (p.1 i)^2 ≤ 3 := by
    filter_upwards [ProbabilityTheory.ae_cond_mem (μ := (volume : Measure (RawPoint d)))
      (rawBodyWith_isClosed d Δ).measurableSet] with p hp
    have h := sq_le_sq₀ (abs_nonneg (p.1 i)) (Real.sqrt_nonneg 3) |>.mpr (hp.1 i)
    simpa only [sq_abs, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)] using h
  calc
    rawTransverseVariance Δ i ≤ ∫ _ : RawPoint d, (3 : ℝ) ∂rawUniform d Δ :=
      integral_mono_ae hi (integrable_const 3) hb
    _ = 3 := by simp

/-- All geometric and covariance assertions in Lemma 4.2 hold for the exact
power scale for all sufficiently large dimensions. -/
theorem eventually_rawBody_full_geometry : ∀ᶠ d : ℕ in atTop,
    IsCompact (rawBody d) ∧ Convex ℝ (rawBody d) ∧
    (0 : RawPoint d) ∈ interior (rawBody d) ∧
    IsProbabilityMeasure (rawUniform d (deviationScale d)) ∧
    (∀ i, ∫ p, rawCoordinate i p ∂rawUniform d (deviationScale d) = 0) ∧
    (∃ a b : ℝ, 0 < a ∧ 0 < b ∧ rawCovarianceMatrix d (deviationScale d) =
      Matrix.diagonal (fun i => match i with | none => b | some _ => a)) := by
  filter_upwards [eventually_rawBody_parameters, eventually_gt_atTop 0] with d hd hd0
  exact ⟨rawBodyWith_isCompact d hd.1, rawBodyWith_convex d hd.1.le,
    zero_mem_interior_rawBodyWith d hd.2, rawUniform_isProbabilityMeasure d hd.1 hd.2,
    rawUniform_coordinate_mean_zero _, rawUniform_covariance_shape hd0 hd.1 hd.2⟩

theorem eventually_explicit_isotropicBody : ∀ᶠ d : ℕ in atTop,
    ∃ i₀ : Fin d,
      Reference.convexBody (euclideanBody (deviationScale d) i₀) ∧
      Reference.unconditional (euclideanBody (deviationScale d) i₀) ∧
      Reference.isotropic (Reference.uniform (euclideanBody (deviationScale d) i₀)) := by
  filter_upwards [eventually_rawBody_parameters, eventually_gt_atTop 0] with d hd hd0
  exact ⟨⟨0, hd0⟩, euclideanBody_certified hd.1 hd.2 ⟨0, hd0⟩⟩


@[simp] theorem rawGaussianWeight_signChange {d : ℕ} (a b t : ℝ) (s : Fin d → Bool)
    (axial : Bool) (p : RawPoint d) :
    rawGaussianWeight a b t (signChange s axial p) = rawGaussianWeight a b t p := by
  have hz : (signChange s axial p).2^2 = p.2^2 := by cases axial <;> simp [signChange]
  simp only [rawGaussianWeight, transverseEnergy_signChange, hz]

theorem signChange_rawTilt_preserving {d : ℕ} (Δ a b t : ℝ) (s : Fin d → Bool)
    (axial : Bool) : MeasurePreserving (signChange s axial) (rawTilt d Δ a b t) (rawTilt d Δ a b t) := by
  have hm := map_withDensity_comp (signChangeMeasurableEquiv s axial).measurableEmbedding
    (rawUniform d Δ) (fun p => ENNReal.ofReal
      (rawGaussianWeight a b t p / rawTiltPartition d Δ a b t))
  change Measure.map (signChange s axial) ((rawUniform d Δ).withDensity
    (fun p => ENNReal.ofReal (rawGaussianWeight a b t (signChange s axial p) /
      rawTiltPartition d Δ a b t))) =
    (Measure.map (signChange s axial) (rawUniform d Δ)).withDensity
      (fun p => ENNReal.ofReal (rawGaussianWeight a b t p / rawTiltPartition d Δ a b t)) at hm
  simp only [rawGaussianWeight_signChange, (signChange_rawUniform_preserving Δ s axial).map_eq] at hm
  exact ⟨(signChange_volume_preserving s axial).measurable, hm⟩

theorem rawTilt_axial_mean_zero (d : ℕ) (Δ a b t : ℝ) :
    ∫ p, p.2 ∂rawTilt d Δ a b t = 0 := by
  have h := (signChange_rawTilt_preserving Δ a b t (fun _ : Fin d => false) true).integral_comp
    (signChangeMeasurableEquiv (fun _ => false) true).measurableEmbedding (fun p => p.2)
  simp only [signChange, ↓reduceIte, integral_neg] at h
  linarith

theorem integral_euclideanBody_gaussianTilt {d : ℕ} {Δ : ℝ} (hΔ : 0 < Δ)
    (hroom : 0 < (d : ℝ) - 2 * Δ) (i₀ : Fin d) (t : ℝ) (f : Reference.Space (d+1) → ℝ) :
    ∫ x, f x ∂(Reference.gaussianTilt (Reference.uniform (euclideanBody Δ i₀)) t) =
      ∫ p, f (rawIsotropization d (rawTransverseVariance Δ i₀) (rawAxialVariance d Δ) p)
        ∂rawTilt d Δ (rawTransverseVariance Δ i₀) (rawAxialVariance d Δ) t := by
  rw [euclideanBody_gaussianTilt_eq_map_rawTilt hΔ hroom i₀]
  exact (rawIsotropizationEquiv d (rawTransverseVariance_pos hΔ hroom i₀)
    (rawAxialVariance_pos hΔ hroom)).toContinuousLinearEquiv.toHomeomorph.measurableEmbedding.integral_map f

/-- The actual axial covariance entry after the Gaussian tilt is the raw axial
square moment divided by the original axial variance. -/
theorem euclideanBody_tilt_covariance_axial {d : ℕ} {Δ : ℝ} (hΔ : 0 < Δ)
    (hroom : 0 < (d : ℝ) - 2 * Δ) (i₀ : Fin d) (t : ℝ) :
    Reference.covariance (Reference.gaussianTilt (Reference.uniform (euclideanBody Δ i₀)) t) 0 0 =
      (∫ p, p.2^2 ∂rawTilt d Δ (rawTransverseVariance Δ i₀) (rawAxialVariance d Δ) t) /
        rawAxialVariance d Δ := by
  unfold Reference.covariance
  rw [integral_euclideanBody_gaussianTilt hΔ hroom i₀,
    integral_euclideanBody_gaussianTilt hΔ hroom i₀]
  simp only [rawIsotropization, rawToEuclidean_zero_coordinate, diagonalScale]
  rw [integral_const_mul, rawTilt_axial_mean_zero]
  simp only [mul_zero, sub_zero]
  have heq : (fun p : RawPoint d => ((Real.sqrt (rawAxialVariance d Δ))⁻¹ * p.2) *
      ((Real.sqrt (rawAxialVariance d Δ))⁻¹ * p.2)) =
      fun p => (rawAxialVariance d Δ)⁻¹ * p.2^2 := by
    funext p
    rw [mul_mul_mul_comm, ← sq, inv_pow,
      Real.sq_sqrt (rawAxialVariance_pos hΔ hroom).le]
    ring
  rw [heq, integral_const_mul]
  simp [div_eq_mul_inv, mul_comm]

end GaussianTilt
