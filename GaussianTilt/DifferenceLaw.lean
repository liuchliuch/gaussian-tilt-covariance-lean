import GaussianTilt.LogConcaveLinearImages
import GaussianTilt.BlockPrekopa

/-! # Genuine compact logconcave difference-law densities and symmetrization -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace GaussianTilt.DifferenceLaw
open LogConcaveMarginal
variable {n : ℕ}

/-- The actual Lebesgue convolution density of X−X′. -/
def differenceDensity (f : Reference.Space n → ℝ) (z : Reference.Space n) : ℝ :=
  ∫ y, f (z + y) * f y

lemma norm_pi_le_toLp (y : Fin n → ℝ) :
    ‖y‖ ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm y‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  exact PiLp.norm_apply_le ((EuclideanSpace.equiv (Fin n) ℝ).symm y) i

lemma differenceDensity_properties {f : Reference.Space n → ℝ} {R : ℝ}
    (hf : IsLogConcave f) (hm : Measurable f) (hs : ∀ x, R < ‖x‖ → f x = 0) :
    IsLogConcave (differenceDensity f) ∧ Measurable (differenceDensity f) ∧
      Function.Even (differenceDensity f) ∧
      (∀ z, 2 * R < ‖z‖ → differenceDensity f z = 0) ∧
      ∀ z, Integrable (fun y ↦ f (z + y) * f y) := by
  let e := (EuclideanSpace.equiv (Fin n) ℝ).symm
  let L : (Reference.Space n × (Fin n → ℝ)) →ₗ[ℝ] Reference.Space n :=
    e.toLinearMap.comp (LinearMap.snd ℝ _ _)
  let J : (Reference.Space n × (Fin n → ℝ)) →ₗ[ℝ] Reference.Space n :=
    LinearMap.fst ℝ _ _ + L
  let F : Reference.Space n × (Fin n → ℝ) → ℝ := fun p ↦ f (p.1 + e p.2) * f (e p.2)
  have hF : IsLogConcave F :=
    (BlockPrekopa.logconcave_comp_linear hf J).mul (BlockPrekopa.logconcave_comp_linear hf L)
  have hFm : Measurable F :=
    (hm.comp (measurable_fst.add (e.continuous.measurable.comp measurable_snd))).mul
      (hm.comp (e.continuous.measurable.comp measurable_snd))
  have hFs (z : Reference.Space n) (y : Fin n → ℝ) (hy : R < ‖y‖) : F (z, y) = 0 := by
    dsimp only [F]
    rw [hs _ (hy.trans_le (norm_pi_le_toLp y)), mul_zero]
  obtain ⟨hLC, hI⟩ := BlockPrekopa.logconcave_marginal_and_fibres hF hFm hFs
  have htransport (z : Reference.Space n) :
      (∫ y : Fin n → ℝ, F (z, y)) = differenceDensity f z := by
    exact (PiLp.volume_preserving_toLp (Fin n)).integral_comp
      e.toHomeomorph.measurableEmbedding (fun y ↦ f (z + y) * f y)
  have hLC' : IsLogConcave (differenceDensity f) := by simpa only [htransport] using hLC
  have hM' : Measurable (differenceDensity f) := by
    simpa only [htransport] using BlockPrekopa.marginal_measurable hFm
  refine ⟨hLC', hM', ?_, ?_, ?_⟩
  · intro z
    have h := (measurePreserving_add_right (volume : Measure (Reference.Space n)) z).integral_comp
      (Homeomorph.addRight z).measurableEmbedding (fun y ↦ f (-z + y) * f y)
    change (∫ y, f (-z + (y + z)) * f (y + z)) = differenceDensity f (-z) at h
    rw [← h]
    unfold differenceDensity
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y ↦ by
      dsimp only
      rw [show -z + (y + z) = y by module, add_comm y z]
      ring
  · intro z hz
    apply integral_eq_zero_of_ae
    filter_upwards [] with y
    change f (z + y) * f y = 0
    by_cases hy : R < ‖y‖
    · rw [hs y hy, mul_zero]
    by_cases hzy : R < ‖z + y‖
    · rw [hs _ hzy, zero_mul]
    have hn : ‖z‖ ≤ ‖z + y‖ + ‖y‖ := by
      simpa only [add_sub_cancel_right] using norm_sub_le (z + y) y
    exact False.elim (by linarith)
  · intro z
    apply ((PiLp.volume_preserving_toLp (Fin n)).integrable_comp
      (((hm.comp (continuous_const.add continuous_id).measurable).mul hm).aestronglyMeasurable)).mp
    exact hI z

def subtractShearLinear (n : ℕ) :
    (Reference.Space n × Reference.Space n) ≃ₗ[ℝ] (Reference.Space n × Reference.Space n) where
  toFun p := (p.1 - p.2, p.2)
  invFun p := (p.1 + p.2, p.2)
  left_inv := by intro p; apply Prod.ext <;> simp
  right_inv := by intro p; apply Prod.ext <;> simp
  map_add' := by
    intro p q
    apply Prod.ext
    · dsimp; module
    · rfl
  map_smul' := by
    intro c p
    apply Prod.ext
    · dsimp; module
    · rfl

def subtractShear (n : ℕ) := (subtractShearLinear n).toContinuousLinearEquiv

lemma subtractShear_measurePreserving (n : ℕ) :
    MeasurePreserving (subtractShear n) (volume.prod volume) (volume.prod volume) :=
  measurePreserving_sub_prod (volume : Measure (Reference.Space n)) volume

/-- The exact joint density after subtracting the independent second sample. -/
lemma subtractShear_density {f : Reference.Space n → ℝ} (hf : ∀ x, 0 ≤ f x)
    (hm : Measurable f) :
    Measure.map (subtractShear n)
      ((volume.withDensity (fun x ↦ ENNReal.ofReal (f x))).prod
        (volume.withDensity (fun x ↦ ENNReal.ofReal (f x)))) =
      (volume.prod volume).withDensity (fun p : Reference.Space n × Reference.Space n ↦
        ENNReal.ofReal (f (p.1 + p.2) * f p.2)) := by
  have hp : (volume.withDensity (fun x ↦ ENNReal.ofReal (f x))).prod
      (volume.withDensity (fun x ↦ ENNReal.ofReal (f x))) =
      (volume.prod volume).withDensity
        (fun p : Reference.Space n × Reference.Space n ↦ ENNReal.ofReal (f p.1 * f p.2)) := by
    rw [prod_withDensity hm.ennreal_ofReal hm.ennreal_ofReal]
    congr 1
    funext p
    exact (ENNReal.ofReal_mul (hf p.1)).symm
  rw [hp]
  have h := GaussianTilt.map_withDensity_comp (subtractShear n).toHomeomorph.measurableEmbedding
    (volume.prod volume) (fun p : Reference.Space n × Reference.Space n ↦
      ENNReal.ofReal (f (p.1 + p.2) * f p.2))
  change Measure.map (subtractShear n) ((volume.prod volume).withDensity
    (fun p ↦ ENNReal.ofReal (f ((p.1 - p.2) + p.2) * f p.2))) =
    (Measure.map (subtractShear n) (volume.prod volume)).withDensity _ at h
  simpa only [sub_add_cancel, (subtractShear_measurePreserving n).map_eq] using h

/-- The law of X−X′ is identified with the genuine convolution density. -/
theorem differenceLaw_density {f : Reference.Space n → ℝ} {R : ℝ}
    (hf : IsLogConcave f) (hm : Measurable f) (hs : ∀ x, R < ‖x‖ → f x = 0) :
    Measure.map (fun p : Reference.Space n × Reference.Space n ↦ p.1 - p.2)
      ((volume.withDensity (fun x ↦ ENNReal.ofReal (f x))).prod
        (volume.withDensity (fun x ↦ ENNReal.ofReal (f x)))) =
      volume.withDensity (fun z ↦ ENNReal.ofReal (differenceDensity f z)) := by
  have hI := (differenceDensity_properties hf hm hs).2.2.2.2
  have h := LogConcaveLinearImages.map_fst_withDensity
    (f := fun p : Reference.Space n × Reference.Space n ↦ f (p.1 + p.2) * f p.2)
    (fun p ↦ mul_nonneg (hf.1 _) (hf.1 _))
    ((hm.comp (measurable_fst.add measurable_snd)).mul (hm.comp measurable_snd)) hI
  rw [← subtractShear_density hf.1 hm, Measure.map_map measurable_fst
    (subtractShear n).continuous.measurable] at h
  exact h

end GaussianTilt.DifferenceLaw
