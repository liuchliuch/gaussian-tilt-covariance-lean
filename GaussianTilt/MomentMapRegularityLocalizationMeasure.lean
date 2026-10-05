import GaussianTilt.MomentMapRegularityLocalization

/-!
# Local Alexandrov density estimates from the genuine moment equation

The measure of the literal subgradient image is locally comparable to
Lebesgue measure. Both bounds are deduced from the actual transport law,
positive exponential densities and the null boundary of a convex target.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators Gradient NNReal ENNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

lemma withDensity_le_const_mul_of_ae {f : E n → ℝ≥0∞} {A : Set (E n)}
    (hA : MeasurableSet A) {c : ℝ≥0∞} (h : ∀ᵐ x ∂volume.restrict A, f x ≤ c) :
    (volume.withDensity f) A ≤ c * volume A := by
  rw [withDensity_apply f hA, ← setLIntegral_const]
  exact lintegral_mono_ae h

lemma const_mul_le_withDensity_of_ae {f : E n → ℝ≥0∞} {A : Set (E n)}
    (hA : MeasurableSet A) {c : ℝ≥0∞} (h : ∀ᵐ x ∂volume.restrict A, c ≤ f x) :
    c * volume A ≤ (volume.withDensity f) A := by
  rw [withDensity_apply f hA, ← setLIntegral_const]
  exact lintegral_mono_ae h

/-- Closure and interior target agree almost everywhere because the target
is convex. Boundary subgradients therefore contribute zero Alexandrov mass. -/
lemma ae_mem_of_mem_closure_target {K : Set (E n)} (hK : IsOpen K)
    (hKc : Convex ℝ K) : ∀ᵐ p ∂volume, p ∈ closure K → p ∈ K := by
  have hb : ∀ᵐ p ∂volume, p ∉ frontier K := by
    apply ae_iff.mpr
    simpa only [not_not] using hKc.addHaar_frontier volume
  filter_upwards [hb] with p hp hpc
  by_contra hpK
  apply hp
  rw [frontier, hK.interior_eq]
  exact ⟨hpc, hpK⟩

lemma exp_neg_mass_bounds {φ : E n → ℝ} {A : Set (E n)}
    (hA : MeasurableSet A) {N : ℝ} (hN : ∀ x ∈ A, |φ x| ≤ N) :
    ENNReal.ofReal (Real.exp (-N)) * volume A ≤
      (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x)))) A ∧
    (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x)))) A ≤
      ENNReal.ofReal (Real.exp N) * volume A := by
  constructor
  · apply const_mul_le_withDensity_of_ae hA
    filter_upwards [ae_restrict_mem hA] with x hx
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have := (le_abs_self (φ x)).trans (hN x hx)
    linarith
  · apply withDensity_le_const_mul_of_ae hA
    filter_upwards [ae_restrict_mem hA] with x hx
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have := (neg_abs_le (φ x)).trans' (neg_le_neg (hN x hx))
    linarith

/-- Uniform upper and lower target-density bounds hold on every measurable
set contained in closure K, since its boundary portion has volume zero. -/
lemma target_mass_bounds {K : Set (E n)} (hK : IsOpen K) (hKc : Convex ℝ K)
    {V : E n → ℝ} {M : ℝ} (hM : ∀ p ∈ closure K, |V p| ≤ M)
    {S : Set (E n)} (hS : MeasurableSet S) (hSK : S ⊆ closure K) :
    ENNReal.ofReal (Real.exp (-M)) * volume S ≤
      (volume.withDensity (fun x => ENNReal.ofReal
        (K.indicator (fun y => Real.exp (-V y)) x))) S ∧
    (volume.withDensity (fun x => ENNReal.ofReal
      (K.indicator (fun y => Real.exp (-V y)) x))) S ≤
      ENNReal.ofReal (Real.exp M) * volume S := by
  have hgood : ∀ᵐ p ∂volume.restrict S, p ∈ K ∧ |V p| ≤ M := by
    filter_upwards [ae_restrict_mem hS,
      ae_restrict_of_ae (ae_mem_of_mem_closure_target hK hKc)] with p hp hg
    exact ⟨hg (hSK hp), hM p (hSK hp)⟩
  constructor
  · apply const_mul_le_withDensity_of_ae hS
    filter_upwards [hgood] with p hp
    rw [Set.indicator_of_mem hp.1]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have := (le_abs_self (V p)).trans hp.2
    linarith
  · apply withDensity_le_const_mul_of_ae hS
    filter_upwards [hgood] with p hp
    rw [Set.indicator_of_mem hp.1]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have := (neg_abs_le (V p)).trans' (neg_le_neg hp.2)
    linarith

lemma ennreal_exp_mul_exp_neg (r : ℝ) :
    ENNReal.ofReal (Real.exp r) * ENNReal.ofReal (Real.exp (-r)) = 1 := by
  rw [← ENNReal.ofReal_mul (Real.exp_pos r).le, ← Real.exp_add]
  simp

/-- Quantitative two-sided Alexandrov-volume estimates, proved from the
literal moment transport and explicit local source/target potential bounds. -/
theorem subgradientImage_volume_bounds_of_target_density {φ V : E n → ℝ}
    {L : ℝ≥0} (hL : LipschitzWith L φ) (hc : ConvexOn ℝ univ φ)
    {K : Set (E n)} (hK : IsOpen K) (hKc : Convex ℝ K) (hV : ContinuousOn V K)
    (hmap : (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x)))).map
      (gradient φ) = volume.withDensity (fun x => ENNReal.ofReal
        (K.indicator (fun y => Real.exp (-V y)) x)))
    {A : Set (E n)} (hA : IsCompact A) {N M : ℝ}
    (hN : ∀ x ∈ A, |φ x| ≤ N) (hM : ∀ p ∈ closure K, |V p| ≤ M) :
    ENNReal.ofReal (Real.exp (-M - N)) * volume A ≤ volume (subgradientImage φ A) ∧
    volume (subgradientImage φ A) ≤ ENNReal.ofReal (Real.exp (M + N)) * volume A := by
  have hs := exp_neg_mass_bounds hA.measurableSet hN
  have ht := target_mass_bounds hK hKc hM (isCompact_subgradientImage hL hA).measurableSet
    (subgradientImage_subset_closure_of_target_density hL hc hK hKc hV hmap A)
  have he := measure_subgradientImage_of_target_density hL hc hK hKc hV hmap hA
  rw [he] at ht
  constructor
  · have h := mul_le_mul_left' (hs.1.trans ht.2) (ENNReal.ofReal (Real.exp (-M)))
    have hcancel : ENNReal.ofReal (Real.exp (-M)) * ENNReal.ofReal (Real.exp M) = 1 := by
      simpa only [neg_neg] using ennreal_exp_mul_exp_neg (-M)
    rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos (-M)).le,
      ← Real.exp_add, show -M + -N = -M - N by ring,
      ← mul_assoc, hcancel, one_mul] at h
    exact h
  · have h := mul_le_mul_left' (ht.1.trans hs.2) (ENNReal.ofReal (Real.exp M))
    rw [← mul_assoc, ennreal_exp_mul_exp_neg, one_mul, ← mul_assoc,
      ← ENNReal.ofReal_mul (Real.exp_pos M).le, ← Real.exp_add] at h
    exact h

/-- On each compact source neighborhood there are positive uniform local
upper/lower Alexandrov density constants. No Monge--Ampère regularity,
strict convexity, or existence of a classical Hessian is assumed. -/
theorem local_subgradientImage_volume_bounds {φ V : E n → ℝ}
    {L : ℝ≥0} (hL : LipschitzWith L φ) (hc : ConvexOn ℝ univ φ)
    {K : Set (E n)} (hK : IsOpen K) (hKc : Convex ℝ K)
    (hKb : Bornology.IsBounded K) (hV : ContinuousOn V (closure K))
    (hmap : (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x)))).map
      (gradient φ) = volume.withDensity (fun x => ENNReal.ofReal
        (K.indicator (fun y => Real.exp (-V y)) x)))
    {B : Set (E n)} (hB : IsCompact B) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ A : Set (E n), IsCompact A → A ⊆ B →
      ENNReal.ofReal c * volume A ≤ volume (subgradientImage φ A) ∧
      volume (subgradientImage φ A) ≤ ENNReal.ofReal C * volume A := by
  obtain ⟨N, hN⟩ := hB.exists_bound_of_continuousOn hL.continuous.continuousOn
  obtain ⟨M, hM⟩ := hKb.isCompact_closure.exists_bound_of_continuousOn hV
  refine ⟨Real.exp (-M - N), Real.exp (M + N), Real.exp_pos _, Real.exp_pos _, ?_⟩
  intro A hA hAB
  apply subgradientImage_volume_bounds_of_target_density hL hc hK hKc
    (hV.mono subset_closure) hmap hA
  · intro x hx
    simpa only [Real.norm_eq_abs] using hN x (hAB hx)
  · intro p hp
    simpa only [Real.norm_eq_abs] using hM p hp

end GaussianTilt.MomentMapRegularity
