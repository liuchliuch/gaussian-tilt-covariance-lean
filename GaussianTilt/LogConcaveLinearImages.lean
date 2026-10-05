import GaussianTilt.LinearImageDensity
import GaussianTilt.ScalarLogConcaveMoments
import GaussianTilt.Reference.PaperStatements

/-! # Compact logconcave laws under actual surjective linear images

The density is obtained by a Haar change of variables and actual block
integration. Compact support is a hypothesis of the results in this file.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology InnerProductSpace
namespace GaussianTilt.LogConcaveLinearImages
open LogConcaveMarginal

section Decomposition
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem exists_linearEquiv_fst (L : E →ₗ[ℝ] F) (hL : Function.Surjective L) :
    ∃ k : ℕ, ∃ e : E ≃L[ℝ] F × (Fin k → ℝ), ∀ x, (e x).1 = L x := by
  obtain ⟨r, hr⟩ := L.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hL)
  have hright (y : F) : L (r y) = y := LinearMap.congr_fun hr y
  let e₀ : E ≃ₗ[ℝ] F × LinearMap.ker L :=
    { toFun := fun x ↦ (L x, ⟨x - r (L x), by simp [LinearMap.mem_ker, hright]⟩)
      invFun := fun p ↦ r p.1 + p.2
      left_inv := by intro x; dsimp; abel
      right_inv := by
        intro ⟨y, z⟩
        apply Prod.ext
        · simp [hright, LinearMap.mem_ker.mp z.property]
        · apply Subtype.ext
          simp [hright, LinearMap.mem_ker.mp z.property]
      map_add' := by
        intro x y
        apply Prod.ext
        · exact L.map_add x y
        · apply Subtype.ext
          change x + y - r (L (x + y)) = (x - r (L x)) + (y - r (L y))
          simp only [map_add]
          abel
      map_smul' := by
        intro c x
        apply Prod.ext
        · exact L.map_smul c x
        · apply Subtype.ext
          simp [smul_sub] }
  let b := Module.finBasis ℝ (LinearMap.ker L)
  let e := e₀.trans ((LinearEquiv.refl ℝ F).prodCongr b.equivFun)
  exact ⟨_, e.toContinuousLinearEquiv, fun _ ↦ rfl⟩
end Decomposition

section Marginal
variable {E F : Type*} [MeasureSpace E] [MeasureSpace F]
  [SFinite (volume : Measure F)]

/-- The actual pushforward under first projection is the actual fibre integral. -/
theorem map_fst_withDensity {f : E × F → ℝ}
    (hf : ∀ p, 0 ≤ f p) (hm : Measurable f)
    (hi : ∀ x, Integrable (fun y ↦ f (x, y))) :
    Measure.map Prod.fst ((volume : Measure E).prod volume |>.withDensity
      (fun p ↦ ENNReal.ofReal (f p))) =
    volume.withDensity (fun x ↦ ENNReal.ofReal (∫ y, f (x, y))) := by
  ext s hs
  rw [Measure.map_apply measurable_fst hs, withDensity_apply _ (measurable_fst hs),
    withDensity_apply _ hs]
  rw [← lintegral_indicator (measurable_fst hs), lintegral_prod _
    ((hm.ennreal_ofReal.indicator (measurable_fst hs)).aemeasurable),
    ← lintegral_indicator hs]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ s
  · simp only [indicator_of_mem hx, mem_preimage, hx, indicator_of_mem]
    exact (ofReal_integral_eq_lintegral_ofReal (hi x) (Eventually.of_forall (fun y ↦ hf (x,y)))).symm
  · simp [hx]
end Marginal


/-- Replace an almost-everywhere compact density by a pointwise compact
logconcave representative without changing the measure. -/
theorem exists_compact_density {n : ℕ} {μ : Measure (Reference.Space n)}
    (hc : Reference.compactlySupported μ) (hl : Reference.logconcave μ) :
    ∃ (f : Reference.Space n → ℝ) (R : ℝ),
      IsLogConcave f ∧ Measurable f ∧
      (∀ x, R < ‖x‖ → f x = 0) ∧
      μ = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)) := by
  obtain ⟨f, ⟨hn, hm, hl⟩, hμ⟩ := hl
  obtain ⟨K, hK, hzero⟩ := hc
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Reference.Space n)
  let S := Metric.closedBall (0 : Reference.Space n) R
  have hSm : MeasurableSet S := Metric.isClosed_closedBall.measurableSet
  have hSae : ∀ᵐ x ∂μ, x ∈ S :=
    (ae_iff.mpr hzero).mono (fun x hx ↦ hR hx)
  refine ⟨S.indicator f, R,
    ScalarLogConcaveMoments.logconcave_indicator ⟨hn, hl⟩ (convex_closedBall _ _),
    hm.indicator hSm, ?_, ?_⟩
  · intro x hx
    apply indicator_of_notMem
    simpa only [S, Metric.mem_closedBall, dist_zero_right, not_le] using hx
  · have hfun : (fun x ↦ ENNReal.ofReal (S.indicator f x)) =
        S.indicator (fun x ↦ ENNReal.ofReal (f x)) := by
      funext x
      by_cases hx : x ∈ S <;> simp [hx]
    rw [hfun, withDensity_indicator hSm, ← restrict_withDensity hSm, ← hμ,
      Measure.restrict_eq_self_of_ae_mem hSae]


section LinearImages
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasureSpace F] [BorelSpace F] [(volume : Measure F).IsAddHaarMeasure]
  [SecondCountableTopology F]

/-- A surjective linear image has a genuine compact logconcave density.
The same constructed density is even whenever the original density is even. -/
theorem exists_compact_density_map_surjective (L : E →ₗ[ℝ] F)
    (hL : Function.Surjective L) {f : E → ℝ} {R : ℝ}
    (hf : IsLogConcave f) (hm : Measurable f)
    (hs : ∀ x, R < ‖x‖ → f x = 0) :
    ∃ (g : F → ℝ) (S : ℝ), IsLogConcave g ∧ Measurable g ∧
      (∀ y, S < ‖y‖ → g y = 0) ∧
      Measure.map L (volume.withDensity (fun x ↦ ENNReal.ofReal (f x))) =
        volume.withDensity (fun y ↦ ENNReal.ofReal (g y)) ∧
      ((∀ x, f (-x) = f x) → ∀ y, g (-y) = g y) := by
  obtain ⟨k, e, he⟩ := exists_linearEquiv_fst L hL
  obtain ⟨c, hc, hh, hhm, hmap⟩ :=
    LinearImageDensity.exists_density_map_linearEquiv e volume
      ((volume : Measure F).prod volume) hf hm
  let H : F × (Fin k → ℝ) → ℝ := fun p ↦ c * f (e.symm p)
  let S : ℝ := ‖e.toContinuousLinearMap‖ * R
  have hHs : ∀ p : F × (Fin k → ℝ), S < ‖p‖ → H p = 0 :=
    LinearImageDensity.transported_support_bound e hs
  have hHy : ∀ x y, S < ‖y‖ → H (x, y) = 0 :=
    fun x y hy ↦ hHs (x,y) (hy.trans_le (norm_snd_le (x,y)))
  obtain ⟨hg, hgi⟩ := BlockPrekopa.logconcave_marginal_and_fibres hh hhm hHy
  refine ⟨fun y ↦ ∫ z, H (y, z), S, hg,
    BlockPrekopa.marginal_measurable hhm, ?_, ?_, ?_⟩
  · intro y hy
    apply integral_eq_zero_of_ae
    exact Eventually.of_forall fun z ↦ hHs (y,z) (hy.trans_le (norm_fst_le (y,z)))
  · rw [← map_fst_withDensity hh.1 hhm hgi, ← hmap,
      Measure.map_map measurable_fst e.continuous.measurable]
    congr 1
    funext x
    exact (he x).symm
  · intro heven y
    have hHeven (p : F × (Fin k → ℝ)) : H (-p) = H p := by
      simp only [H, map_neg, heven]
    calc
      (∫ z, H (-y, z)) = ∫ z, H (-y, -z) :=
        (integral_neg_eq_self (fun z ↦ H (-y,z)) volume).symm
      _ = ∫ z, H (y,z) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun z ↦ hHeven (y,z)
end LinearImages


/-- Compact support survives every continuous linear image. -/
theorem compactlySupported_map {n m : ℕ} {μ : Measure (Reference.Space n)}
    (hc : Reference.compactlySupported μ) (L : Reference.Space n →ₗ[ℝ] Reference.Space m) :
    Reference.compactlySupported (Measure.map L μ) := by
  obtain ⟨K, hK, hzero⟩ := hc
  have hLc := L.continuous_of_finiteDimensional
  refine ⟨L '' K, hK.image hLc, ?_⟩
  rw [Measure.map_apply hLc.measurable (hK.image hLc).measurableSet.compl]
  apply measure_mono_null _ hzero
  intro x hx hxK
  exact hx ⟨x, hxK, rfl⟩

/-- Genuine full-dimensional density closure under surjective linear maps,
for the compact specialization of the reference definition. -/
theorem logconcave_map_surjective {n m : ℕ} {μ : Measure (Reference.Space n)}
    (hc : Reference.compactlySupported μ) (hl : Reference.logconcave μ)
    (L : Reference.Space n →ₗ[ℝ] Reference.Space m) (hL : Function.Surjective L) :
    Reference.logconcave (Measure.map L μ) := by
  obtain ⟨f, R, hf, hm, hs, rfl⟩ := exists_compact_density hc hl
  obtain ⟨g, S, hg, hgm, hgs, hmap, heven⟩ :=
    exists_compact_density_map_surjective L hL hf hm hs
  exact ⟨g, ⟨hg.1, hgm, hg.2⟩, hmap⟩

/-- The compact logconcave image theorem includes the probability law. -/
theorem compact_probability_logconcave_map_surjective {n m : ℕ}
    {μ : Measure (Reference.Space n)} [IsProbabilityMeasure μ]
    (hc : Reference.compactlySupported μ) (hl : Reference.logconcave μ)
    (L : Reference.Space n →ₗ[ℝ] Reference.Space m) (hL : Function.Surjective L) :
    IsProbabilityMeasure (Measure.map L μ) ∧
      Reference.compactlySupported (Measure.map L μ) ∧
      Reference.logconcave (Measure.map L μ) :=
  ⟨Measure.isProbabilityMeasure_map L.continuous_of_finiteDimensional.measurable.aemeasurable,
    compactlySupported_map hc L, logconcave_map_surjective hc hl L hL⟩

/-- The scalar image has an actual measurable compact logconcave density. -/
theorem exists_scalar_density {n : ℕ} {μ : Measure (Reference.Space n)}
    (hc : Reference.compactlySupported μ) (hl : Reference.logconcave μ)
    (L : Reference.Space n →ₗ[ℝ] ℝ) (hL : Function.Surjective L) :
    ∃ (g : ℝ → ℝ) (R : ℝ), IsLogConcave g ∧ Measurable g ∧
      (∀ x, R < ‖x‖ → g x = 0) ∧
      Measure.map L μ = volume.withDensity (fun x ↦ ENNReal.ofReal (g x)) := by
  obtain ⟨f, R, hf, hm, hs, rfl⟩ := exists_compact_density hc hl
  obtain ⟨g, S, hg, hgm, hgs, hmap, heven⟩ :=
    exists_compact_density_map_surjective L hL hf hm hs
  exact ⟨g, S, hg, hgm, hgs, hmap⟩

/-- A non-surjective map has a genuine unit annihilating target direction. -/
theorem exists_unit_annihilator {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (L : E →ₗ[ℝ] F) (hL : ¬ Function.Surjective L) :
    ∃ t : F, ‖t‖ = 1 ∧ ∀ x, ⟪t, L x⟫_ℝ = 0 := by
  have hproper : LinearMap.range L ≠ ⊤ := fun h ↦ hL (LinearMap.range_eq_top.mp h)
  have hne : (LinearMap.range L)ᗮ ≠ ⊥ := by
    exact fun h ↦ hproper (Submodule.orthogonal_eq_bot_iff.mp h)
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hne
  refine ⟨‖v‖⁻¹ • v, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)]
  · intro x
    rw [real_inner_smul_left, real_inner_comm (L x) v,
      (Submodule.mem_orthogonal _ _).mp hv (L x) ⟨x, rfl⟩, mul_zero]

end GaussianTilt.LogConcaveLinearImages
