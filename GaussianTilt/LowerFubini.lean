import GaussianTilt.LowerMarginal
import GaussianTilt.Isotropization
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Measure-level bridges for the actual lower-bound body
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Real
open scoped ENNReal BigOperators

namespace GaussianTilt
namespace LowerFubini
open LowerProbability LowerMarginal

/-- Product tilting is the joint density given by the product of the genuine
one-coordinate normalized densities. -/
theorem tiltedCubeLaw_withDensity (d : ℕ) (τ : ℝ) :
    tiltedCubeLaw d τ = (cubeLaw d).withDensity
      (fun x ↦ ENNReal.ofReal (∏ i : Fin d,
        Real.exp (-τ * (x i) ^ 2) / ∫ u, Real.exp (-τ * u ^ 2) ∂cubeCoordinateLaw)) := by
  let f : ℝ → ℝ := fun x ↦ Real.exp (-τ * x ^ 2) /
    ∫ u, Real.exp (-τ * u ^ 2) ∂cubeCoordinateLaw
  have hf : Integrable f cubeCoordinateLaw := (tiltedCoordinate_exponential_integrable τ).div_const _
  have hfn : ∀ x, 0 ≤ f x := by intro x; dsimp [f]; positivity
  change Measure.pi (fun _ : Fin d ↦ tiltedCoordinateLaw τ) = _
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  change (∫⁻ x in univ.pi s, ENNReal.ofReal (∏ i, f (x i)) ∂cubeLaw d) = _
  rw [cubeLaw, Measure.restrict_pi_pi]
  have hprod : Integrable (fun x : Fin d → ℝ ↦ ∏ i, f (x i))
      (Measure.pi (fun i ↦ cubeCoordinateLaw.restrict (s i))) :=
    Integrable.fintype_prod (fun _ ↦ hf.integrableOn)
  rw [← ofReal_integral_eq_lintegral_ofReal hprod
    (ae_of_all _ fun x ↦ Finset.prod_nonneg (fun i _ ↦ hfn (x i))),
    integral_fintype_prod_eq_prod]
  rw [ENNReal.ofReal_prod_of_nonneg]
  · apply Finset.prod_congr rfl
    intro i _
    rw [tiltedCoordinateLaw, tilted_apply_eq_ofReal_integral' _ (hs i)]
  · intro i _
    exact integral_nonneg (hfn)

/-- The product cube law is a scalar multiple of Lebesgue measure restricted
to the transverse cube. -/
theorem cubeLaw_eq_smul_restrict (d : ℕ) :
    cubeLaw d = (volume (Icc (-Real.sqrt (3 : ℝ)) (Real.sqrt 3)))⁻¹ ^ d •
      (volume : Measure (Fin d → ℝ)).restrict
        (univ.pi (fun _ ↦ Icc (-Real.sqrt (3 : ℝ)) (Real.sqrt 3))) := by
  change Measure.pi (fun _ : Fin d ↦ ProbabilityTheory.cond volume (Icc (-Real.sqrt 3) (Real.sqrt 3))) = _
  apply Measure.pi_eq
  intro s hs
  rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply (MeasurableSet.univ_pi hs)]
  rw [← Set.pi_inter_distrib, volume_pi_pi]
  simp only [ProbabilityTheory.cond, Measure.smul_apply, smul_eq_mul]
  simp_rw [Measure.restrict_apply (hs _)]
  rw [Finset.prod_mul_distrib]
  simp

/-- Tonelli's theorem identifies the axial marginal of a restricted product
measure with the actual measures of its transverse sections. -/
theorem map_snd_restrict_product {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    {E : Set (X × Y)} (hE : MeasurableSet E) :
    Measure.map Prod.snd ((μ.prod ν).restrict E) =
      ν.withDensity (fun y ↦ μ ((fun x ↦ (x, y)) ⁻¹' E)) := by
  ext s hs
  rw [Measure.map_apply measurable_snd hs, Measure.restrict_apply (measurable_snd hs),
    Measure.prod_apply_symm ((measurable_snd hs).inter hE), withDensity_apply _ hs,
    ← lintegral_indicator hs _]
  apply lintegral_congr
  intro y
  by_cases hy : y ∈ s
  · rw [Set.indicator_of_mem hy]
    congr 1
    ext x
    simp [hy]
  · rw [Set.indicator_of_notMem hy]
    have hempty : (fun x : X ↦ (x, y)) ⁻¹' (Prod.snd ⁻¹' s ∩ E) = ∅ := by
      ext x
      simp [hy]
    rw [hempty, measure_empty]

/-- The unnormalized axial Gaussian reference measure. -/
def gaussianBase (t : ℝ) : Measure ℝ :=
  volume.withDensity (fun z ↦ ENNReal.ofReal (Real.exp (-t * z ^ 2)))

lemma gaussianBase_finite {t : ℝ} (ht : 0 < t) : IsFiniteMeasure (gaussianBase t) := by
  apply isFiniteMeasure_withDensity
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_exp_neg_mul_sq ht)
    (ae_of_all _ fun _ ↦ Real.exp_nonneg _)]
  exact ENNReal.ofReal_ne_top

/-- The actual slice inequality in raw transverse and scaled axial coordinates. -/
def sliceRegion (d : ℕ) (Δ b : ℝ) : Set ((Fin d → ℝ) × ℝ) :=
  {q | (∑ i, (q.1 i) ^ 2) ≤ (d : ℝ) - 2 * Δ * (1 + Real.sqrt b * |q.2|)}

lemma sliceRegion_measurable (d : ℕ) (Δ b : ℝ) : MeasurableSet (sliceRegion d Δ b) := by
  apply measurableSet_le <;> fun_prop

/-- Product law conditioned on the actual quadratic-energy slice constraint. -/
def conditionedJointLaw (d : ℕ) (τ Δ b t : ℝ) : Measure ((Fin d → ℝ) × ℝ) :=
  ProbabilityTheory.cond ((tiltedCubeLaw d τ).prod (gaussianBase t)) (sliceRegion d Δ b)

lemma map_snd_joint_unnormalized (d : ℕ) (τ Δ b : ℝ) {t : ℝ} (ht : 0 < t) :
    Measure.map Prod.snd (((tiltedCubeLaw d τ).prod (gaussianBase t)).restrict
      (sliceRegion d Δ b)) = volume.withDensity
        (fun z ↦ ENNReal.ofReal (kernel t (tiltedSlice d τ Δ b) z)) := by
  letI := gaussianBase_finite ht
  rw [map_snd_restrict_product _ _ (sliceRegion_measurable d Δ b), gaussianBase,
    ← withDensity_mul _ (by fun_prop)
      (measurable_measure_prodMk_right (sliceRegion_measurable d Δ b))]
  apply withDensity_congr_ae
  filter_upwards [] with z
  change ENNReal.ofReal (Real.exp (-t * z ^ 2)) *
    (tiltedCubeLaw d τ) {x | (∑ i, (x i) ^ 2) ≤ (d : ℝ) - 2 * Δ * (1 + Real.sqrt b * |z|)} = _
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _), ← ENNReal.ofReal_mul (Real.exp_nonneg _)]
  rfl

lemma map_normalized_measure {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) {f : X → Y} (hf : Measurable f) :
    Measure.map f ((μ univ)⁻¹ • μ) = ((Measure.map f μ) univ)⁻¹ • Measure.map f μ := by
  rw [Measure.map_smul, Measure.map_apply hf MeasurableSet.univ, preimage_univ]

lemma axialLaw_eq_normalized_density {t : ℝ} {p : ℝ → ℝ} (ht : 0 < t)
    (hm : Measurable p) (hp : ∀ x, p x ∈ Icc (0 : ℝ) 1) (hpos : 0 < mass t p) :
    axialLaw t p = ((volume.withDensity (fun x ↦ ENNReal.ofReal (kernel t p x))) univ)⁻¹ •
      volume.withDensity (fun x ↦ ENNReal.ofReal (kernel t p x)) := by
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (kernel_integrable ht hm hp)
      (ae_of_all _ fun x ↦ kernel_nonneg (fun y ↦ (hp y).1) x)]
  change volume.withDensity (fun x ↦ ENNReal.ofReal (kernel t p x / mass t p)) =
    (ENNReal.ofReal (mass t p))⁻¹ • _
  rw [← withDensity_smul _ (by unfold kernel; fun_prop)]
  apply withDensity_congr_ae
  filter_upwards [] with x
  rw [ENNReal.ofReal_div_of_pos hpos]
  simp [div_eq_mul_inv, mul_comm]

/-- Genuine Tonelli marginal formula for the conditioned product construction;
there is no assumed marginal-density identity in this theorem. -/
theorem conditionedJointLaw_axial_marginal (d : ℕ) (τ Δ b : ℝ) {t : ℝ} (ht : 0 < t)
    (hpos : 0 < mass t (tiltedSlice d τ Δ b)) :
    Measure.map Prod.snd (conditionedJointLaw d τ Δ b t) =
      axialLaw t (tiltedSlice d τ Δ b) := by
  unfold conditionedJointLaw ProbabilityTheory.cond
  have hmass : ((tiltedCubeLaw d τ).prod (gaussianBase t)) (sliceRegion d Δ b) =
      (((tiltedCubeLaw d τ).prod (gaussianBase t)).restrict (sliceRegion d Δ b)) univ := by simp
  rw [hmass, map_normalized_measure _ measurable_snd,
    map_snd_joint_unnormalized d τ Δ b ht,
    axialLaw_eq_normalized_density ht (tiltedSlice_measurable d τ Δ b)
      (tiltedSlice_mem_Icc d τ Δ b) hpos]

/-- Normalizing a finite positive density is conditioning its weighted measure
on the whole space. -/
lemma normalized_density_eq_cond {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {f : X → ℝ} (hf : Measurable f)
    (hfi : Integrable f μ) (hfn : ∀ x, 0 ≤ f x) (hp : 0 < ∫ x, f x ∂μ) :
    μ.withDensity (fun x ↦ ENNReal.ofReal (f x / ∫ y, f y ∂μ)) =
      ProbabilityTheory.cond (μ.withDensity (fun x ↦ ENNReal.ofReal (f x))) univ := by
  unfold ProbabilityTheory.cond
  rw [Measure.restrict_univ, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal hfi (ae_of_all _ hfn),
    ← withDensity_smul _ hf.ennreal_ofReal]
  apply withDensity_congr_ae
  filter_upwards [] with x
  rw [ENNReal.ofReal_div_of_pos hp]
  simp [div_eq_mul_inv, mul_comm]

lemma cond_restrict_eq (X : Type*) [MeasurableSpace X] (μ : Measure X)
    {C S : Set X} (hC : MeasurableSet C) (hS : MeasurableSet S) :
    ProbabilityTheory.cond (μ.restrict C) S = ProbabilityTheory.cond μ (S ∩ C) := by
  simp only [ProbabilityTheory.cond, Measure.restrict_apply hS, Measure.restrict_restrict hS]

/-- The raw Gaussian tilt is exactly the normalized weighted Lebesgue law on
the actual body. -/
theorem rawTilt_eq_cond_weighted_volume {d : ℕ} {Δ : ℝ} (hΔ : 0 < Δ)
    (hroom : 0 < (d : ℝ) - 2 * Δ) (a b t : ℝ) :
    rawTilt d Δ a b t = ProbabilityTheory.cond
      (volume.withDensity (fun p : RawPoint d ↦ ENNReal.ofReal (rawGaussianWeight a b t p)))
      (rawBodyWith d Δ) := by
  letI := rawUniform_isProbabilityMeasure d hΔ hroom
  have hi : Integrable (rawGaussianWeight (d := d) a b t) (rawUniform d Δ) :=
    continuous_integrable_rawUniform hΔ hroom (by unfold rawGaussianWeight transverseEnergy; fun_prop)
  have hp : 0 < ∫ p, rawGaussianWeight a b t p ∂rawUniform d Δ :=
    integral_exp_pos hi
  unfold rawTilt rawTiltPartition
  rw [normalized_density_eq_cond _ (by unfold rawGaussianWeight transverseEnergy; fun_prop)
    hi (fun _ ↦ Real.exp_nonneg _) hp]
  unfold rawUniform ProbabilityTheory.cond
  rw [withDensity_smul_measure]
  change ProbabilityTheory.cond
    ((volume (rawBodyWith d Δ))⁻¹ •
      ((volume.restrict (rawBodyWith d Δ)).withDensity
        (fun p ↦ ENNReal.ofReal (rawGaussianWeight a b t p)))) univ = _
  rw [cond_smul_measure _ _
    (ENNReal.inv_ne_zero.mpr (rawBodyWith_isCompact d hΔ).measure_ne_top)
    (ENNReal.inv_ne_top.mpr (rawBodyWith_volume_pos d hroom).ne'),
    ← restrict_withDensity (rawBodyWith_isClosed d Δ).measurableSet,
    cond_restrict_eq _ _ (rawBodyWith_isClosed d Δ).measurableSet MeasurableSet.univ,
    univ_inter]
  rfl

/-- The transverse cube, expressed as a measurable product set. -/
def transverseCube (d : ℕ) : Set (Fin d → ℝ) :=
  univ.pi (fun _ ↦ Icc (-Real.sqrt (3 : ℝ)) (Real.sqrt 3))

def cubeCylinder (d : ℕ) : Set (RawPoint d) := transverseCube d ×ˢ univ

lemma transverseCube_measurable (d : ℕ) : MeasurableSet (transverseCube d) :=
  MeasurableSet.univ_pi (fun _ ↦ measurableSet_Icc)

lemma cubeCylinder_measurable (d : ℕ) : MeasurableSet (cubeCylinder d) :=
  (transverseCube_measurable d).prod MeasurableSet.univ

lemma mem_transverseCube_iff {d : ℕ} (x : Fin d → ℝ) :
    x ∈ transverseCube d ↔ ∀ i, |x i| ≤ Real.sqrt 3 := by
  simp only [transverseCube, Set.mem_pi, mem_univ, forall_const, mem_Icc, abs_le]

/-- Unnormalized product Gaussian weight in raw transverse and scaled axial coordinates. -/
def jointWeight {d : ℕ} (τ t : ℝ) (p : RawPoint d) : ℝ :=
  Real.exp (-τ * transverseEnergy p - t * p.2 ^ 2)

lemma jointWeight_measurable (d : ℕ) (τ t : ℝ) :
    Measurable (jointWeight (d := d) τ t) := by
  unfold jointWeight transverseEnergy
  fun_prop

/-- An exact density formula, including both normalizing constants, for the
unconditioned product construction. -/
theorem joint_product_eq_smul_weighted_volume (d : ℕ) (τ t : ℝ) :
    (tiltedCubeLaw d τ).prod (gaussianBase t) =
      ((volume (Icc (-Real.sqrt (3 : ℝ)) (Real.sqrt 3)))⁻¹ ^ d *
        ENNReal.ofReal ((∫ u, Real.exp (-τ * u ^ 2) ∂cubeCoordinateLaw)⁻¹ ^ d)) •
      ((volume : Measure (RawPoint d)).restrict (cubeCylinder d)).withDensity
        (fun p ↦ ENNReal.ofReal (jointWeight τ t p)) := by
  rw [tiltedCubeLaw_withDensity, gaussianBase, prod_withDensity (by fun_prop) (by fun_prop),
    cubeLaw_eq_smul_restrict, Measure.prod_smul_left, withDensity_smul_measure]
  have hprod : ((volume : Measure (Fin d → ℝ)).restrict (transverseCube d)).prod
      (volume : Measure ℝ) = (volume : Measure (RawPoint d)).restrict (cubeCylinder d) := by
    simpa only [Measure.restrict_univ] using
      (Measure.prod_restrict (μ := (volume : Measure (Fin d → ℝ)))
        (ν := (volume : Measure ℝ)) (transverseCube d) univ)
  unfold transverseCube at hprod
  rw [hprod]
  change _ • ((volume : Measure (RawPoint d)).restrict (cubeCylinder d)).withDensity _ = _
  rw [← smul_smul, ← withDensity_smul _ (jointWeight_measurable d τ t).ennreal_ofReal]
  congr 1
  apply withDensity_congr_ae
  filter_upwards [] with p
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← Real.exp_sum, ← Finset.mul_sum, jointWeight, transverseEnergy,
    sub_eq_add_neg, Real.exp_add]
  ring

lemma joint_product_scalar_ne_zero (d : ℕ) (τ : ℝ) :
    ((volume (Icc (-Real.sqrt (3 : ℝ)) (Real.sqrt 3)))⁻¹ ^ d *
      ENNReal.ofReal ((∫ u, Real.exp (-τ * u ^ 2) ∂cubeCoordinateLaw)⁻¹ ^ d)) ≠ 0 := by
  apply mul_ne_zero
  · exact pow_ne_zero _ (ENNReal.inv_ne_zero.mpr (by simp))
  · apply ENNReal.ofReal_ne_zero_iff.mpr
    exact pow_pos (inv_pos.mpr (integral_exp_pos (tiltedCoordinate_exponential_integrable τ))) _

lemma joint_product_scalar_ne_top (d : ℕ) (τ : ℝ) :
    ((volume (Icc (-Real.sqrt (3 : ℝ)) (Real.sqrt 3)))⁻¹ ^ d *
      ENNReal.ofReal ((∫ u, Real.exp (-τ * u ^ 2) ∂cubeCoordinateLaw)⁻¹ ^ d)) ≠ ⊤ := by
  apply ENNReal.mul_ne_top
  · apply ENNReal.pow_ne_top
    apply ENNReal.inv_ne_top.mpr
    simp only [Real.volume_Icc, ne_eq, ENNReal.ofReal_eq_zero]
    nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)]
  · exact ENNReal.ofReal_ne_top

/-- Conditioning the product construction cancels its arbitrary product
normalizations and retains precisely the true cube and quadratic constraint. -/
theorem conditionedJointLaw_eq_cond_weighted_volume (d : ℕ) (τ Δ b t : ℝ) :
    conditionedJointLaw d τ Δ b t = ProbabilityTheory.cond
      (volume.withDensity (fun p : RawPoint d ↦ ENNReal.ofReal (jointWeight τ t p)))
      (sliceRegion d Δ b ∩ cubeCylinder d) := by
  rw [conditionedJointLaw, joint_product_eq_smul_weighted_volume,
    cond_smul_measure _ _ (joint_product_scalar_ne_zero d τ) (joint_product_scalar_ne_top d τ),
    ← restrict_withDensity (cubeCylinder_measurable d),
    cond_restrict_eq _ _ (cubeCylinder_measurable d) (sliceRegion_measurable d Δ b)]

/-- A linear coordinate change of a weighted conditional law has the transported
weight on its image; its constant Lebesgue Jacobian cancels in normalization. -/
theorem map_cond_weighted_volume_linearEquiv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (e : E ≃ₗ[ℝ] E)
    (g : E → ℝ≥0∞) {S : Set E} (hS : MeasurableSet S) :
    Measure.map e (ProbabilityTheory.cond (μ.withDensity (fun p ↦ g (e p))) S) =
      ProbabilityTheory.cond (μ.withDensity g) (e '' S) := by
  let em := e.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  change Measure.map em (ProbabilityTheory.cond (μ.withDensity (fun p ↦ g (em p))) S) =
    ProbabilityTheory.cond (μ.withDensity g) (em '' S)
  rw [map_cond_image em _ hS, map_withDensity_comp em.measurableEmbedding]
  have hm := Measure.map_linearMap_addHaar_eq_smul_addHaar μ e.isUnit_det'.ne_zero
  simp only [LinearEquiv.coe_coe] at hm
  change ProbabilityTheory.cond ((Measure.map e μ).withDensity g) (e '' S) = _
  rw [hm, withDensity_smul_measure]
  exact cond_smul_measure _ _
    (ENNReal.ofReal_ne_zero_iff.mpr (abs_pos.mpr (inv_ne_zero e.isUnit_det'.ne_zero)))
    ENNReal.ofReal_ne_top

/-- Only the axial coordinate is scaled in the product construction. -/
def axialScaleEquiv (d : ℕ) {b : ℝ} (hb : 0 < b) : RawPoint d ≃ₗ[ℝ] RawPoint d :=
  diagonalScaleLinearEquiv d (one_ne_zero) (inv_ne_zero (Real.sqrt_pos.mpr hb).ne')

lemma axialScale_body_image (d : ℕ) (Δ : ℝ) {b : ℝ} (hb : 0 < b) :
    axialScaleEquiv d hb '' rawBodyWith d Δ = sliceRegion d Δ b ∩ cubeCylinder d := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    have hs := (Real.sqrt_pos.mpr hb).ne'
    constructor
    · change (∑ i, (1 * q.1 i) ^ 2) ≤
        (d : ℝ) - 2 * Δ * (1 + Real.sqrt b * |(Real.sqrt b)⁻¹ * q.2|)
      rw [abs_mul, abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr hb)),
        ← mul_assoc, mul_inv_cancel₀ hs, one_mul]
      simpa only [one_mul, transverseEnergy] using (by linarith [hq.2] :
        transverseEnergy q ≤ (d : ℝ) - 2 * Δ * (1 + |q.2|))
    · refine ⟨(mem_transverseCube_iff _).mpr ?_, mem_univ _⟩
      change ∀ i, |1 * q.1 i| ≤ Real.sqrt 3
      simpa only [one_mul] using hq.1
  · rintro ⟨hp, hc⟩
    refine ⟨diagonalScale 1 (Real.sqrt b) p, ?_, ?_⟩
    · constructor
      · simpa only [diagonalScale, one_mul] using (mem_transverseCube_iff _).mp hc.1
      · change transverseEnergy (diagonalScale 1 (Real.sqrt b) p) +
          2 * Δ * |Real.sqrt b * p.2| ≤ _
        rw [transverseEnergy_diagonalScale, one_pow, one_mul, abs_mul,
          abs_of_pos (Real.sqrt_pos.mpr hb)]
        change (∑ i, (p.1 i) ^ 2) ≤
          (d : ℝ) - 2 * Δ * (1 + Real.sqrt b * |p.2|) at hp
        dsimp [transverseEnergy]
        linarith
    · change diagonalScale 1 (Real.sqrt b)⁻¹ (diagonalScale 1 (Real.sqrt b) p) = p
      rw [diagonalScale_comp, one_mul, inv_mul_cancel₀ (Real.sqrt_pos.mpr hb).ne', diagonalScale_one]

lemma jointWeight_axialScale {d : ℕ} (a t : ℝ) {b : ℝ} (hb : 0 < b) (p : RawPoint d) :
    jointWeight (t / a) t (axialScaleEquiv d hb p) = rawGaussianWeight a b t p := by
  unfold jointWeight rawGaussianWeight
  change Real.exp (-(t / a) * transverseEnergy (diagonalScale 1 (Real.sqrt b)⁻¹ p) -
    t * ((Real.sqrt b)⁻¹ * p.2)^2) = _
  rw [transverseEnergy_diagonalScale, one_pow, one_mul, mul_pow, inv_pow, Real.sq_sqrt hb.le]
  congr 1
  ring

set_option maxHeartbeats 600000 in
/-- The missing measure-level bridge: the product construction conditioned on
the quadratic slice is exactly the axial rescaling of the genuine raw body tilt. -/
theorem map_rawTilt_eq_conditionedJointLaw {d : ℕ} {Δ : ℝ} (hΔ : 0 < Δ)
    (hroom : 0 < (d : ℝ) - 2 * Δ) (a : ℝ) {b : ℝ} (hb : 0 < b) (t : ℝ) :
    Measure.map (axialScaleEquiv d hb) (rawTilt d Δ a b t) =
      conditionedJointLaw d (t / a) Δ b t := by
  rw [rawTilt_eq_cond_weighted_volume hΔ hroom,
    conditionedJointLaw_eq_cond_weighted_volume,
    ← axialScale_body_image d Δ hb]
  have hw : (fun p : RawPoint d ↦ ENNReal.ofReal (rawGaussianWeight a b t p)) =
      fun p ↦ ENNReal.ofReal (jointWeight (t / a) t (axialScaleEquiv d hb p)) := by
    funext p
    rw [jointWeight_axialScale]
  rw [hw]
  exact map_cond_weighted_volume_linearEquiv (E := RawPoint d)
    (volume : Measure (RawPoint d)) (axialScaleEquiv d hb)
    (fun p : RawPoint d ↦ ENNReal.ofReal (jointWeight (t / a) t p))
    (rawBodyWith_isClosed d Δ).measurableSet

lemma rawTilt_probability {d : ℕ} {Δ : ℝ} (hΔ : 0 < Δ)
    (hroom : 0 < (d : ℝ) - 2 * Δ) (a b t : ℝ) :
    IsProbabilityMeasure (rawTilt d Δ a b t) := by
  letI := rawUniform_isProbabilityMeasure d hΔ hroom
  change IsProbabilityMeasure ((rawUniform d Δ).tilted
    (fun p ↦ -t * (transverseEnergy p / a + p.2 ^ 2 / b)))
  apply isProbabilityMeasure_tilted
  exact continuous_integrable_rawUniform hΔ hroom (by unfold transverseEnergy; fun_prop)

lemma conditionedJointLaw_probability {d : ℕ} {Δ : ℝ} (hΔ : 0 < Δ)
    (hroom : 0 < (d : ℝ) - 2 * Δ) (a : ℝ) {b : ℝ} (hb : 0 < b) (t : ℝ) :
    IsProbabilityMeasure (conditionedJointLaw d (t / a) Δ b t) := by
  letI := rawTilt_probability hΔ hroom a b t
  rw [← map_rawTilt_eq_conditionedJointLaw hΔ hroom a hb t]
  exact Measure.isProbabilityMeasure_map
    (axialScaleEquiv d hb).toContinuousLinearEquiv.toHomeomorph.measurable.aemeasurable

lemma actual_tiltedSlice_mass_pos {d : ℕ} {Δ : ℝ} (hΔ : 0 < Δ)
    (hroom : 0 < (d : ℝ) - 2 * Δ) (a : ℝ) {b t : ℝ} (hb : 0 < b) (ht : 0 < t) :
    0 < mass t (tiltedSlice d (t / a) Δ b) := by
  letI := gaussianBase_finite ht
  letI := conditionedJointLaw_probability hΔ hroom a hb t
  have hn : ((tiltedCubeLaw d (t / a)).prod (gaussianBase t)) (sliceRegion d Δ b) ≠ 0 := by
    intro hz
    exact IsProbabilityMeasure.ne_zero (conditionedJointLaw d (t / a) Δ b t)
      (cond_eq_zero_of_meas_eq_zero hz)
  have hm := congrArg (fun μ : Measure ℝ ↦ μ univ)
    (map_snd_joint_unnormalized d (t / a) Δ b ht)
  dsimp only at hm
  rw [Measure.map_apply measurable_snd MeasurableSet.univ, preimage_univ,
    Measure.restrict_apply MeasurableSet.univ, univ_inter,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal
      (kernel_integrable ht (tiltedSlice_measurable d (t / a) Δ b)
        (tiltedSlice_mem_Icc d (t / a) Δ b))
      (ae_of_all _ fun x ↦ kernel_nonneg
        (fun y ↦ (tiltedSlice_mem_Icc d (t / a) Δ b y).1) x)] at hm
  exact ENNReal.ofReal_ne_zero_iff.mp (hm ▸ hn)

/-- The actual scaled axial coordinate under the body tilt has the derived
Gaussian-times-acceptance density. -/
theorem rawTilt_axial_marginal {d : ℕ} {Δ : ℝ} (hΔ : 0 < Δ)
    (hroom : 0 < (d : ℝ) - 2 * Δ) (a : ℝ) {b t : ℝ} (hb : 0 < b) (ht : 0 < t) :
    Measure.map (fun p : RawPoint d ↦ (Real.sqrt b)⁻¹ * p.2) (rawTilt d Δ a b t) =
      axialLaw t (tiltedSlice d (t / a) Δ b) := by
  have hm := conditionedJointLaw_axial_marginal d (t / a) Δ b ht
    (actual_tiltedSlice_mass_pos hΔ hroom a hb ht)
  have he : Measurable (axialScaleEquiv d hb : RawPoint d → RawPoint d) :=
    (axialScaleEquiv d hb).toContinuousLinearEquiv.toHomeomorph.measurable
  rw [← map_rawTilt_eq_conditionedJointLaw hΔ hroom a hb t,
    Measure.map_map measurable_snd he] at hm
  exact hm

/-- Fubini formula for the true Euclidean isotropic body's tilted axial marginal. -/
theorem euclideanBody_tilt_axial_marginal {d : ℕ} {Δ : ℝ} (hΔ : 0 < Δ)
    (hroom : 0 < (d : ℝ) - 2 * Δ) (i₀ : Fin d) {t : ℝ} (ht : 0 < t) :
    Measure.map (fun x : Reference.Space (d + 1) ↦ x 0)
      (Reference.gaussianTilt (Reference.uniform (euclideanBody Δ i₀)) t) =
      axialLaw t (tiltedSlice d (t / rawTransverseVariance Δ i₀) Δ (rawAxialVariance d Δ)) := by
  have he : Measurable (rawIsotropization d (rawTransverseVariance Δ i₀) (rawAxialVariance d Δ)) :=
    (rawIsotropizationEquiv d (rawTransverseVariance_pos hΔ hroom i₀)
      (rawAxialVariance_pos hΔ hroom)).toContinuousLinearEquiv.toHomeomorph.measurable
  have hx : Measurable (fun x : Reference.Space (d+1) ↦ x 0) :=
    (EuclideanSpace.proj (0 : Fin (d+1))).continuous.measurable
  rw [euclideanBody_gaussianTilt_eq_map_rawTilt hΔ hroom i₀, Measure.map_map hx he]
  exact rawTilt_axial_marginal hΔ hroom _ (rawAxialVariance_pos hΔ hroom) ht

/-- The axial covariance entry is the variance of the fully identified slice law. -/
theorem euclideanBody_tilt_covariance_eq_axialLaw {d : ℕ} {Δ : ℝ} (hΔ : 0 < Δ)
    (hroom : 0 < (d : ℝ) - 2 * Δ) (i₀ : Fin d) {t : ℝ} (ht : 0 < t) :
    Reference.covariance (Reference.gaussianTilt (Reference.uniform (euclideanBody Δ i₀)) t) 0 0 =
      variance (fun z : ℝ ↦ z)
        (axialLaw t (tiltedSlice d (t / rawTransverseVariance Δ i₀) Δ (rawAxialVariance d Δ))) := by
  have hx : Measurable (fun x : Reference.Space (d+1) ↦ x 0) :=
    (EuclideanSpace.proj (0 : Fin (d+1))).continuous.measurable
  rw [← euclideanBody_tilt_axial_marginal hΔ hroom i₀ ht,
    variance_map (by fun_prop) hx.aemeasurable]
  change _ = variance (fun x : Reference.Space (d+1) ↦ x 0) _
  rw [variance_eq_integral hx.aemeasurable]
  have hmean : (∫ x : Reference.Space (d + 1), x 0
      ∂(Reference.gaussianTilt (Reference.uniform (euclideanBody Δ i₀)) t)) = 0 := by
    rw [integral_euclideanBody_gaussianTilt hΔ hroom i₀]
    simp only [rawIsotropization, rawToEuclidean_zero_coordinate, diagonalScale,
      integral_const_mul, rawTilt_axial_mean_zero, mul_zero]
  simp only [Reference.covariance, hmean, zero_mul, sub_zero, sq]

/-- Corollary 4.10 for the genuine body's covariance, once the deterministic
precision and raw covariance scale inequalities have been verified. -/
theorem euclideanBody_tilt_covariance_lower {d : ℕ} {Δ : ℝ} (hΔ : 0 < Δ)
    (hroom : 0 < (d : ℝ) - 2 * Δ) (i₀ : Fin d) {t L : ℝ} (ht : 0 < t)
    (hτ : t / rawTransverseVariance Δ i₀ ∈ Icc (0 : ℝ) 1)
    (hL : 0 < L) (htL : t * L ^ 2 = 1)
    (hdef : 2 * Δ * (1 + Real.sqrt (rawAxialVariance d Δ) * L) + Δ ≤
      (d : ℝ) * meanDeficitConstant * (t / rawTransverseVariance Δ i₀))
    (hrate : (9 / 2 : ℝ) * Real.log 2 ≤ Δ ^ 2 / (d : ℝ)) :
    windowConstant / t ≤
      Reference.covariance (Reference.gaussianTilt (Reference.uniform (euclideanBody Δ i₀)) t) 0 0 := by
  rw [euclideanBody_tilt_covariance_eq_axialLaw hΔ hroom i₀ ht]
  exact actual_tiltedSlice_variance d hτ hΔ.le ht hL htL hdef hrate

/-- The exact conversion from the centered energy event to the slice threshold. -/
lemma cubeSlice_eq_energy_event (d : ℕ) (Δ s : ℝ) :
    cubeSlice d Δ s = (cubeLaw d).real
      {x | (∑ i, (x i) ^ 2) ≤ (d : ℝ) - 2 * Δ * (1 + s)} := by
  unfold cubeSlice sliceProbability
  congr 1
  ext x
  simp only [mem_setOf_eq, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  constructor <;> intro h <;> linarith

lemma cubeSlice_measurable (d : ℕ) (Δ : ℝ) : Measurable (cubeSlice d Δ) := by
  have hs : MeasurableSet {q : ℝ × (Fin d → ℝ) |
      (∑ i, (q.2 i) ^ 2) ≤ (d : ℝ) - 2 * Δ * (1 + q.1)} := by
    apply measurableSet_le <;> fun_prop
  have hm := (measurable_measure_prodMk_left (ν := cubeLaw d) hs).ennreal_toReal
  change Measurable (fun s ↦ cubeSlice d Δ s)
  simp_rw [cubeSlice_eq_energy_event]
  exact hm

lemma cubeSlice_nonneg (d : ℕ) (Δ s : ℝ) : 0 ≤ cubeSlice d Δ s := measureReal_nonneg

lemma rawBody_eq_slice_cube (d : ℕ) (Δ : ℝ) :
    rawBodyWith d Δ = sliceRegion d Δ 1 ∩ cubeCylinder d := by
  ext p
  simp only [rawBodyWith, mem_setOf_eq, mem_inter_iff, sliceRegion, cubeCylinder,
    mem_prod, mem_univ, and_true, mem_transverseCube_iff, Real.sqrt_one, one_mul]
  dsimp [transverseEnergy]
  constructor
  · rintro ⟨hc, he⟩
    exact ⟨by linarith, hc⟩
  · rintro ⟨he, hc⟩
    exact ⟨hc, by linarith⟩

/-- The unweighted product slice restriction is exactly a known positive
constant times the actual body's Lebesgue restriction. -/
lemma cubeJoint_restrict_eq (d : ℕ) (Δ : ℝ) :
    (((cubeLaw d).prod volume).restrict (sliceRegion d Δ 1)) =
      (volume (Icc (-Real.sqrt (3 : ℝ)) (Real.sqrt 3)))⁻¹ ^ d •
        (volume : Measure (RawPoint d)).restrict (rawBodyWith d Δ) := by
  rw [cubeLaw_eq_smul_restrict, Measure.prod_smul_left, Measure.restrict_smul]
  have hprod := Measure.prod_restrict (μ := (volume : Measure (Fin d → ℝ)))
    (ν := (volume : Measure ℝ)) (transverseCube d) univ
  rw [Measure.restrict_univ] at hprod
  unfold transverseCube at hprod
  rw [hprod, Measure.restrict_restrict (sliceRegion_measurable d Δ 1), rawBody_eq_slice_cube]
  rfl

/-- Tonelli gives the actual raw axial slice density. -/
lemma cubeJoint_axial_density (d : ℕ) (Δ : ℝ) :
    Measure.map Prod.snd (((cubeLaw d).prod volume).restrict (sliceRegion d Δ 1)) =
      volume.withDensity (fun z ↦ ENNReal.ofReal (cubeSlice d Δ |z|)) := by
  rw [map_snd_restrict_product _ _ (sliceRegion_measurable d Δ 1)]
  apply withDensity_congr_ae
  filter_upwards [] with z
  rw [cubeSlice_eq_energy_event, ← ENNReal.ofReal_toReal (measure_ne_top (cubeLaw d) _)]
  simp only [sliceRegion, Real.sqrt_one, one_mul]
  rfl

/-- The raw-body axial Fubini identity for every measurable real observable.
Both sides are actual Lebesgue integrals. -/
theorem rawBody_axial_fubini (d : ℕ) (Δ : ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    (∫ z, cubeSlice d Δ |z| * f z) =
      ((volume (Icc (-Real.sqrt (3 : ℝ)) (Real.sqrt 3)))⁻¹ ^ d).toReal *
        ∫ p in rawBodyWith d Δ, f p.2 := by
  have hm := integral_map (μ := ((cubeLaw d).prod volume).restrict (sliceRegion d Δ 1))
    measurable_snd.aemeasurable hf.aestronglyMeasurable
  have hq : Measurable (fun z ↦ ENNReal.ofReal (cubeSlice d Δ |z|)) :=
    ((cubeSlice_measurable d Δ).comp measurable_abs).ennreal_ofReal
  rw [cubeJoint_axial_density, integral_withDensity_eq_integral_toReal_smul hq
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top),
    cubeJoint_restrict_eq, integral_smul_measure] at hm
  simpa only [ENNReal.toReal_ofReal (cubeSlice_nonneg d Δ _), smul_eq_mul] using hm

/-- The zeroth slice integral computes actual body volume. -/
theorem rawBody_volume_fubini (d : ℕ) (Δ : ℝ) :
    (∫ z, cubeSlice d Δ |z|) =
      ((volume (Icc (-Real.sqrt (3 : ℝ)) (Real.sqrt 3)))⁻¹ ^ d).toReal *
        volume.real (rawBodyWith d Δ) := by
  simpa only [mul_one, setIntegral_const, smul_eq_mul] using
    rawBody_axial_fubini d Δ (f := fun _ ↦ (1 : ℝ)) measurable_const

lemma cubeVolumeFactor_pos (d : ℕ) :
    0 < ((volume (Icc (-Real.sqrt (3 : ℝ)) (Real.sqrt 3)))⁻¹ ^ d).toReal := by
  apply ENNReal.toReal_pos
  · exact pow_ne_zero _ (ENNReal.inv_ne_zero.mpr (by simp))
  · apply ENNReal.pow_ne_top
    apply ENNReal.inv_ne_top.mpr
    simp only [Real.volume_Icc, ne_eq, ENNReal.ofReal_eq_zero]
    nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)]

/-- The axial second moment of the true raw uniform law is the ratio of its
two actual slice integrals. -/
theorem rawAxialVariance_eq_slice_ratio {d : ℕ} {Δ : ℝ} (hΔ : 0 < Δ)
    (hroom : 0 < (d : ℝ) - 2 * Δ) :
    rawAxialVariance d Δ =
      (∫ z, z ^ 2 * cubeSlice d Δ |z|) / (∫ z, cubeSlice d Δ |z|) := by
  rw [rawBody_volume_fubini]
  have hnum := rawBody_axial_fubini d Δ (f := fun z ↦ z ^ 2) (by fun_prop)
  simp only [mul_comm (cubeSlice d Δ _) (_ ^ 2)] at hnum
  rw [hnum, mul_div_mul_left _ _ (cubeVolumeFactor_pos d).ne']
  unfold rawAxialVariance rawUniform ProbabilityTheory.cond
  rw [integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]
  simp only [div_eq_mul_inv, measureReal_def, mul_comm]

/-- Every continuous axial observable is integrable against the slice density,
because it is the marginal of the actual compact raw body. -/
lemma cubeSlice_mul_integrable {d : ℕ} {Δ : ℝ} (hΔ : 0 < Δ)
    {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable (fun z ↦ f z * cubeSlice d Δ |z|) := by
  have hi : Integrable (fun p : RawPoint d ↦ f p.2)
      (((cubeLaw d).prod volume).restrict (sliceRegion d Δ 1)) := by
    rw [cubeJoint_restrict_eq]
    exact (ContinuousOn.integrableOn_compact (rawBodyWith_isCompact d hΔ)
      (hf.comp continuous_snd).continuousOn).smul_measure
      (by apply ENNReal.pow_ne_top; apply ENNReal.inv_ne_top.mpr;
          simp only [Real.volume_Icc, ne_eq, ENNReal.ofReal_eq_zero];
          nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)])
  have him := (integrable_map_measure hf.aestronglyMeasurable measurable_snd.aemeasurable).mpr hi
  have hq : Measurable (fun z ↦ ENNReal.ofReal (cubeSlice d Δ |z|)) :=
    ((cubeSlice_measurable d Δ).comp measurable_abs).ennreal_ofReal
  rw [cubeJoint_axial_density, integrable_withDensity_iff hq
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)] at him
  simpa only [ENNReal.toReal_ofReal (cubeSlice_nonneg d Δ _)] using him

lemma integral_even_eq_twice_halfline {f : ℝ → ℝ} (hf : Integrable f)
    (he : ∀ x, f (-x) = f x) : (∫ x, f x) = 2 * ∫ x in Ici (0 : ℝ), f x := by
  have hs := integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi hf
  have hn := integral_comp_neg_Ioi 0 f
  simp only [he, neg_zero] at hn
  rw [compl_Ioi, ← hn] at hs
  rw [integral_Ici_eq_integral_Ioi]
  linarith

/-- The exact half-line slice ratio stated in Lemma 4.7, without an assumed
marginal law or unproved Fubini step. -/
theorem rawAxialVariance_eq_halfline_slice_ratio {d : ℕ} {Δ : ℝ} (hΔ : 0 < Δ)
    (hroom : 0 < (d : ℝ) - 2 * Δ) :
    rawAxialVariance d Δ =
      (∫ s in Ici (0 : ℝ), s ^ 2 * cubeSlice d Δ s) /
        (∫ s in Ici (0 : ℝ), cubeSlice d Δ s) := by
  rw [rawAxialVariance_eq_slice_ratio hΔ hroom]
  have h0 : Integrable (fun z ↦ cubeSlice d Δ |z|) := by
    simpa only [one_mul] using cubeSlice_mul_integrable hΔ (f := fun _ ↦ (1 : ℝ)) continuous_const
  have h2 := cubeSlice_mul_integrable (d := d) hΔ (f := fun z ↦ z ^ 2) (by fun_prop)
  rw [integral_even_eq_twice_halfline h2 (by intro z; simp),
    integral_even_eq_twice_halfline h0 (by intro z; simp), mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]
  congr 1 <;> apply setIntegral_congr_fun measurableSet_Ici <;>
    intro z hz <;> simp only [abs_of_nonneg (show 0 ≤ z from hz)]

/-- The transverse version of the restricted-product Tonelli identity. -/
lemma map_fst_restrict_product {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    {E : Set (X × Y)} (hE : MeasurableSet E) :
    Measure.map Prod.fst ((μ.prod ν).restrict E) =
      μ.withDensity (fun x ↦ ν ((fun y ↦ (x, y)) ⁻¹' E)) := by
  ext s hs
  rw [Measure.map_apply measurable_fst hs, Measure.restrict_apply (measurable_fst hs),
    Measure.prod_apply ((measurable_fst hs).inter hE), withDensity_apply _ hs,
    ← lintegral_indicator hs _]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx]
    congr 1
    ext y
    simp [hx]
  · rw [Set.indicator_of_notMem hx]
    have hempty : (fun y : Y ↦ (x, y)) ⁻¹' (Prod.fst ⁻¹' s ∩ E) = ∅ := by
      ext y
      simp [hx]
    rw [hempty, measure_empty]

/-- The true length of the admissible axial interval above a cube point. -/
def axialLength (d : ℕ) (Δ : ℝ) (x : Fin d → ℝ) : ℝ :=
  max ((d : ℝ) - 2 * Δ - ∑ i, (x i) ^ 2) 0 / Δ

lemma axialLength_nonneg (d : ℕ) {Δ : ℝ} (hΔ : 0 < Δ) (x : Fin d → ℝ) :
    0 ≤ axialLength d Δ x := div_nonneg (le_max_right _ _) hΔ.le

lemma axialLength_le (d : ℕ) {Δ : ℝ} (hΔ : 0 < Δ) (x : Fin d → ℝ) :
    axialLength d Δ x ≤ (d : ℝ) / Δ := by
  apply div_le_div_of_nonneg_right _ hΔ.le
  apply max_le
  · have hn : 0 ≤ ∑ i : Fin d, (x i) ^ 2 := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
    linarith
  · positivity

lemma axialLength_continuous (d : ℕ) (Δ : ℝ) : Continuous (axialLength d Δ) := by
  unfold axialLength
  fun_prop

lemma sliceRegion_fiber_volume (d : ℕ) {Δ : ℝ} (hΔ : 0 < Δ) (x : Fin d → ℝ) :
    volume ((fun z ↦ (x, z)) ⁻¹' sliceRegion d Δ 1) = ENNReal.ofReal (axialLength d Δ x) := by
  let L := ((d : ℝ) - 2 * Δ - ∑ i, (x i) ^ 2) / (2 * Δ)
  have hfiber : (fun z ↦ (x, z)) ⁻¹' sliceRegion d Δ 1 = Icc (-L) L := by
    ext z
    simp only [mem_preimage, sliceRegion, mem_setOf_eq, Real.sqrt_one, one_mul,
      mem_Icc, ← abs_le]
    rw [le_div_iff₀ (show 0 < 2 * Δ by positivity)]
    constructor <;> intro hz <;> linarith
  rw [hfiber, Real.volume_Icc]
  have hlen : L - -L = ((d : ℝ) - 2 * Δ - ∑ i, (x i) ^ 2) / Δ := by dsimp [L]; ring
  rw [hlen, axialLength, ENNReal.ofReal_div_of_pos hΔ, ENNReal.ofReal_div_of_pos hΔ,
    ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left (zero_le _)]

/-- The true transverse marginal of the unnormalized raw body has the axial
length density used in the paper's volume argument. -/
lemma cubeJoint_transverse_density (d : ℕ) {Δ : ℝ} (hΔ : 0 < Δ) :
    Measure.map Prod.fst (((cubeLaw d).prod volume).restrict (sliceRegion d Δ 1)) =
      (cubeLaw d).withDensity (fun x ↦ ENNReal.ofReal (axialLength d Δ x)) := by
  rw [map_fst_restrict_product _ _ (sliceRegion_measurable d Δ 1)]
  congr 1
  funext x
  exact sliceRegion_fiber_volume d hΔ x

/-- Fubini in the transverse direction, for the actual body and normalized cube. -/
theorem rawBody_transverse_fubini (d : ℕ) {Δ : ℝ} (hΔ : 0 < Δ)
    {f : (Fin d → ℝ) → ℝ} (hf : Measurable f) :
    (∫ x, axialLength d Δ x * f x ∂cubeLaw d) =
      ((volume (Icc (-Real.sqrt (3 : ℝ)) (Real.sqrt 3)))⁻¹ ^ d).toReal *
        ∫ p in rawBodyWith d Δ, f p.1 := by
  have hm := integral_map (μ := ((cubeLaw d).prod volume).restrict (sliceRegion d Δ 1))
    measurable_fst.aemeasurable hf.aestronglyMeasurable
  have hmL : Measurable (fun x ↦ ENNReal.ofReal (axialLength d Δ x)) :=
    (axialLength_continuous d Δ).measurable.ennreal_ofReal
  rw [cubeJoint_transverse_density d hΔ, integral_withDensity_eq_integral_toReal_smul hmL
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top), cubeJoint_restrict_eq,
    integral_smul_measure] at hm
  simpa only [ENNReal.toReal_ofReal (axialLength_nonneg d hΔ _), smul_eq_mul] using hm

/-- Both genuine Fubini formulas for the body's normalized volume agree. -/
theorem axialLength_integral_eq_slice_integral (d : ℕ) {Δ : ℝ} (hΔ : 0 < Δ) :
    (∫ x, axialLength d Δ x ∂cubeLaw d) = ∫ z, cubeSlice d Δ |z| := by
  rw [rawBody_volume_fubini]
  simpa only [mul_one, setIntegral_const, smul_eq_mul] using
    rawBody_transverse_fubini d hΔ (f := fun _ ↦ (1 : ℝ)) measurable_const

/-- The low-energy portion of actual raw-body volume has the exponentially
small upper bound asserted in the proof of Lemma 4.7. -/
theorem rawBody_lowEnergy_volume_bound {d : ℕ} (hd : 0 < d) {Δ : ℝ} (hΔ : 0 < Δ) :
    ((volume (Icc (-Real.sqrt (3 : ℝ)) (Real.sqrt 3)))⁻¹ ^ d).toReal *
      volume.real (rawBodyWith d Δ ∩ {p | transverseEnergy p ≤ (d : ℝ) / 2}) ≤
        ((d : ℝ) / Δ) * Real.exp (-(d : ℝ) / 18) := by
  let E : Set (Fin d → ℝ) := {x | (∑ i, (x i) ^ 2) ≤ (d : ℝ) / 2}
  have hE : MeasurableSet E := by apply measurableSet_le <;> fun_prop
  have hf := rawBody_transverse_fubini d hΔ (f := E.indicator (fun _ ↦ (1 : ℝ)))
    (measurable_const.indicator hE)
  have hid : (fun p : RawPoint d ↦ E.indicator (fun _ ↦ (1 : ℝ)) p.1) =
      {p : RawPoint d | transverseEnergy p ≤ (d : ℝ) / 2}.indicator (fun _ ↦ (1 : ℝ)) := by
    funext p
    simp only [E, transverseEnergy, indicator_apply, mem_setOf_eq]
  have hEr : MeasurableSet {p : RawPoint d | transverseEnergy p ≤ (d : ℝ) / 2} :=
    measurableSet_le (continuous_transverseEnergy d).measurable measurable_const
  rw [hid, integral_indicator hEr] at hf
  rw [Measure.restrict_restrict hEr, setIntegral_const,
    smul_eq_mul, mul_one, inter_comm] at hf
  rw [← hf]
  have hiL : Integrable (axialLength d Δ) (cubeLaw d) :=
    Integrable.of_mem_Icc 0 ((d : ℝ) / Δ) (axialLength_continuous d Δ).measurable.aemeasurable
      (ae_of_all _ fun x ↦ ⟨axialLength_nonneg d hΔ x, axialLength_le d hΔ x⟩)
  have hif : Integrable (fun x ↦ axialLength d Δ x * E.indicator (fun _ ↦ (1 : ℝ)) x)
      (cubeLaw d) := by
    simpa only [← Set.indicator_mul_right, mul_one] using hiL.indicator hE
  calc
    _ ≤ ∫ x, ((d : ℝ) / Δ) * E.indicator (fun _ ↦ (1 : ℝ)) x ∂cubeLaw d := by
      apply integral_mono_ae hif ((integrable_const (1 : ℝ)).indicator hE |>.const_mul _)
      filter_upwards [] with x
      exact mul_le_mul_of_nonneg_right (axialLength_le d hΔ x) (by by_cases hx : x ∈ E <;> simp [hx])
    _ = ((d : ℝ) / Δ) * (cubeLaw d).real E := by
      rw [integral_const_mul, integral_indicator_const (1 : ℝ) hE, smul_eq_mul, mul_one]
    _ ≤ _ := mul_le_mul_of_nonneg_left (cube_low_energy_tail d hd) (by positivity)
lemma cubeSlice_antitone {d : ℕ} {Δ : ℝ} (hΔ : 0 ≤ Δ) : Antitone (cubeSlice d Δ) := by
  intro s t hst
  rw [cubeSlice_eq_energy_event, cubeSlice_eq_energy_event]
  apply measureReal_mono
  · intro x hx
    simp only [mem_setOf_eq] at hx ⊢
    nlinarith
  · exact measure_ne_top _ _

lemma rawBody_normalized_volume_lower (d : ℕ) {Δ : ℝ} (hΔ : 0 < Δ) :
    cubeSlice d Δ 1 ≤
      ((volume (Icc (-Real.sqrt (3 : ℝ)) (Real.sqrt 3)))⁻¹ ^ d).toReal *
        volume.real (rawBodyWith d Δ) := by
  rw [← rawBody_volume_fubini]
  have hi : Integrable (fun z ↦ cubeSlice d Δ |z|) := by
    simpa only [one_mul] using cubeSlice_mul_integrable (d := d) hΔ
      (f := fun _ ↦ (1 : ℝ)) continuous_const
  calc
    cubeSlice d Δ 1 = ∫ z in Icc (0 : ℝ) 1, cubeSlice d Δ 1 := by
      simp [setIntegral_const, Real.volume_real_Icc]
    _ ≤ ∫ z in Icc (0 : ℝ) 1, cubeSlice d Δ |z| := by
      apply integral_mono_ae (integrable_const _) hi.integrableOn
      filter_upwards [ae_restrict_mem measurableSet_Icc] with z hz
      exact cubeSlice_antitone hΔ.le (by simpa [abs_of_nonneg hz.1] using hz.2)
    _ ≤ _ := setIntegral_le_integral hi (ae_of_all _ fun z ↦ cubeSlice_nonneg d Δ |z|)

lemma rawUniform_real_apply (d : ℕ) (Δ : ℝ) {E : Set (RawPoint d)} (hE : MeasurableSet E) :
    (rawUniform d Δ).real E = volume.real (rawBodyWith d Δ ∩ E) / volume.real (rawBodyWith d Δ) := by
  rw [measureReal_def, rawUniform, ProbabilityTheory.cond, Measure.smul_apply,
    smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_inv, Measure.restrict_apply hE]
  simp only [measureReal_def, div_eq_mul_inv, mul_comm, inter_comm]

lemma rawUniform_energy_integral {d : ℕ} {Δ : ℝ} (hΔ : 0 < Δ)
    (hroom : 0 < (d : ℝ) - 2 * Δ) (i₀ : Fin d) :
    (∫ p, transverseEnergy p ∂rawUniform d Δ) = (d : ℝ) * rawTransverseVariance Δ i₀ := by
  change (∫ p, ∑ i, (p.1 i) ^ 2 ∂rawUniform d Δ) = _
  rw [integral_finset_sum]
  · simp_rw [rawUniform_transverse_secondMoment_eq Δ _ i₀]
    simp [rawTransverseVariance]
  · intro i _
    exact continuous_integrable_rawUniform hΔ hroom (by fun_prop)

/-- Small normalized low-energy volume forces every genuine transverse variance
away from zero, by permutation symmetry and the actual energy expectation. -/
theorem rawTransverseVariance_lower_of_lowEnergy {d : ℕ} {Δ : ℝ} (hΔ : 0 < Δ)
    (hroom : 0 < (d : ℝ) - 2 * Δ) (i₀ : Fin d)
    (hbad : (rawUniform d Δ).real {p | transverseEnergy p ≤ (d : ℝ) / 2} ≤ 1 / 2) :
    (1 / 4 : ℝ) ≤ rawTransverseVariance Δ i₀ := by
  letI := rawUniform_isProbabilityMeasure d hΔ hroom
  let E : Set (RawPoint d) := {p | transverseEnergy p ≤ (d : ℝ) / 2}
  have hE : MeasurableSet E :=
    measurableSet_le (continuous_transverseEnergy d).measurable measurable_const
  have hi : Integrable transverseEnergy (rawUniform d Δ) :=
    continuous_integrable_rawUniform hΔ hroom (continuous_transverseEnergy d)
  have hpoint : ∀ p : RawPoint d,
      Eᶜ.indicator (fun _ ↦ ((d : ℝ) / 2)) p ≤ transverseEnergy p := by
    intro p
    by_cases hp : p ∈ E
    · rw [indicator_of_notMem (by simpa using hp)]
      exact transverseEnergy_nonneg p
    · rw [indicator_of_mem hp]
      exact le_of_lt (not_le.mp hp)
  have hbound := integral_mono_ae ((integrable_const _).indicator hE.compl) hi (ae_of_all _ hpoint)
  rw [integral_indicator_const _ hE.compl, smul_eq_mul,
    measureReal_compl hE, measureReal_univ_eq_one, rawUniform_energy_integral hΔ hroom i₀] at hbound
  have hd : (0 : ℝ) < d := by exact_mod_cast (Nat.lt_of_le_of_lt (Nat.zero_le i₀.val) i₀.isLt)
  have hn : 0 ≤ (d : ℝ) / 2 := by positivity
  have hgood : (1 / 2 : ℝ) ≤ 1 - (rawUniform d Δ).real E := by linarith
  have hm := mul_le_mul_of_nonneg_right hgood hn
  nlinarith

end LowerFubini
end GaussianTilt
