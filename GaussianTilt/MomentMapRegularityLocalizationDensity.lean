import GaussianTilt.MomentMapRegularityLocalizationMeasure

/-! # The literal Alexandrov Monge--Ampère density

The compact-set Alexandrov measure is identified with the actual density
exp(V(∇φ)-φ). This is a nonsmooth statement proved from moment transport and
the constructed reciprocal gradient, not from a classical Jacobian formula.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators Gradient NNReal ENNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

lemma ae_preimage_subgradientImage_eq_of_target_density {φ V : E n → ℝ}
    (hφ : Continuous φ) (hc : ConvexOn ℝ univ φ)
    {K : Set (E n)} (hK : IsOpen K) (hKc : Convex ℝ K) (hV : ContinuousOn V K)
    (hmap : (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x)))).map
      (gradient φ) = volume.withDensity (fun x => ENNReal.ofReal
        (K.indicator (fun y => Real.exp (-V y)) x))) (A : Set (E n)) :
    gradient φ ⁻¹' subgradientImage φ A =ᵐ[
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x)))] A := by
  have hg : Measurable (gradient φ) :=
    (InnerProductSpace.toDual ℝ (E n)).symm.continuous.measurable.comp (measurable_fderiv ℝ φ)
  have huniq := ae_unique_source_support hφ hc hK hKc hV hmap
  rw [← hmap] at huniq
  have huniq' := ae_of_ae_map hg.aemeasurable huniq
  have hd := (withDensity_absolutelyContinuous volume
    (fun x => ENNReal.ofReal (Real.exp (-φ x)))).ae_le
      (MomentMapCoercivity.convex_ae_differentiable hc)
  filter_upwards [hd, huniq'] with x hdx hux
  apply propext
  constructor
  · rintro ⟨y, hy, hsy⟩
    have he : x = y := hux x y (supportsAt_gradient hc hdx) hsy
    simpa [he] using hy
  · intro hx
    exact ⟨x, hx, supportsAt_gradient hc hdx⟩

lemma measurable_indicator_exp_on_target {K : Set (E n)} (hK : IsOpen K)
    {V : E n → ℝ} (hV : ContinuousOn V K) :
    Measurable (fun x => ENNReal.ofReal (K.indicator (fun y => Real.exp (V y)) x)) := by
  classical
  exact ENNReal.measurable_ofReal.comp
    ((Real.continuous_exp.comp_continuousOn hV).measurable_piecewise
      continuousOn_const hK.measurableSet)

lemma target_withDensity_reciprocal {K : Set (E n)} (hK : IsOpen K)
    {V : E n → ℝ} (hV : ContinuousOn V K) :
    (volume.withDensity (fun x => ENNReal.ofReal
      (K.indicator (fun y => Real.exp (-V y)) x))).withDensity
      (fun x => ENNReal.ofReal (K.indicator (fun y => Real.exp (V y)) x)) =
      volume.restrict K := by
  classical
  rw [← withDensity_mul volume (measurable_indicator_exp_on_target hK hV.neg)
    (measurable_indicator_exp_on_target hK hV)]
  have he : (fun x => ENNReal.ofReal (K.indicator (fun y => Real.exp (-V y)) x)) *
      (fun x => ENNReal.ofReal (K.indicator (fun y => Real.exp (V y)) x)) =
      K.indicator (1 : E n → ℝ≥0∞) := by
    funext p
    by_cases hp : p ∈ K
    · simp only [Pi.mul_apply, Set.indicator_of_mem hp, Pi.one_apply]
      simpa only [neg_neg] using ennreal_exp_mul_exp_neg (-V p)
    · simp [hp]
  rw [he, withDensity_indicator_one hK.measurableSet]

lemma volume_eq_restrict_target_of_subset_closure {K : Set (E n)}
    (hK : IsOpen K) (hKc : Convex ℝ K) {S : Set (E n)}
    (hS : MeasurableSet S) (hSK : S ⊆ closure K) :
    volume S = (volume.restrict K) S := by
  rw [Measure.restrict_apply hS]
  apply measure_congr
  filter_upwards [ae_mem_of_mem_closure_target hK hKc] with p hp
  apply propext
  exact ⟨fun hs => ⟨hs, hp (hSK hs)⟩, And.left⟩

/-- The actual Alexandrov Monge--Ampère equation in its compact-set form:
Lebesgue measure of the full subgradient image equals the integral of
exp(V(∇φ)-φ). This theorem requires no source Hessian or strict convexity. -/
theorem volume_subgradientImage_eq_mongeAmpere_density {φ V : E n → ℝ}
    {L : ℝ≥0} (hL : LipschitzWith L φ) (hc : ConvexOn ℝ univ φ)
    {K : Set (E n)} (hK : IsOpen K) (hKc : Convex ℝ K) (hV : ContinuousOn V K)
    (hmap : (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x)))).map
      (gradient φ) = volume.withDensity (fun x => ENNReal.ofReal
        (K.indicator (fun y => Real.exp (-V y)) x)))
    {A : Set (E n)} (hA : IsCompact A) :
    volume (subgradientImage φ A) =
      (volume.withDensity (fun x => ENNReal.ofReal
        (Real.exp (V (gradient φ x) - φ x)))) A := by
  let f : E n → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (-φ x))
  let g : E n → ℝ≥0∞ := fun x => ENNReal.ofReal
    (K.indicator (fun y => Real.exp (-V y)) x)
  let w : E n → ℝ≥0∞ := fun x => ENNReal.ofReal
    (K.indicator (fun y => Real.exp (V y)) x)
  have hw : Measurable w := measurable_indicator_exp_on_target hK hV
  have hf : Measurable f := (Real.continuous_exp.comp hL.continuous.neg).measurable.ennreal_ofReal
  have hg : Measurable (gradient φ) :=
    (InnerProductSpace.toDual ℝ (E n)).symm.continuous.measurable.comp (measurable_fderiv ℝ φ)
  have hS := (isCompact_subgradientImage hL hA).measurableSet
  have hSK := subgradientImage_subset_closure_of_target_density hL hc hK hKc hV hmap A
  have hpre := ae_preimage_subgradientImage_eq_of_target_density hL.continuous hc hK hKc hV hmap A
  calc
    volume (subgradientImage φ A) = (volume.restrict K) (subgradientImage φ A) :=
      volume_eq_restrict_target_of_subset_closure hK hKc hS hSK
    _ = ((volume.withDensity g).withDensity w) (subgradientImage φ A) := by
      rw [target_withDensity_reciprocal hK hV]
    _ = ∫⁻ p in subgradientImage φ A, w p ∂volume.withDensity g := withDensity_apply w hS
    _ = ∫⁻ x in gradient φ ⁻¹' subgradientImage φ A, w (gradient φ x)
        ∂volume.withDensity f := by
      rw [show volume.withDensity g = (volume.withDensity f).map (gradient φ) from hmap.symm]
      exact setLIntegral_map hS hw hg
    _ = ∫⁻ x in A, w (gradient φ x) ∂volume.withDensity f := by
      rw [Measure.restrict_congr_set hpre]
    _ = ∫⁻ x in A, f x * w (gradient φ x) ∂volume :=
      setLIntegral_withDensity_eq_setLIntegral_mul volume hf (hw.comp hg) hA.measurableSet
    _ = ∫⁻ x in A, ENNReal.ofReal (Real.exp (V (gradient φ x) - φ x)) ∂volume := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_of_ae
        (ae_gradient_mem_of_target_density hL.continuous hK hV hmap)] with x hx
      dsimp [f, w]
      rw [Set.indicator_of_mem hx, ← ENNReal.ofReal_mul (Real.exp_pos (-φ x)).le,
        ← Real.exp_add]
      congr 2
      ring
    _ = (volume.withDensity (fun x => ENNReal.ofReal
          (Real.exp (V (gradient φ x) - φ x)))) A := (withDensity_apply _ hA.measurableSet).symm

end GaussianTilt.MomentMapRegularity
