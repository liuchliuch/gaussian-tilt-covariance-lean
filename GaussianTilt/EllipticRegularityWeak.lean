import GaussianTilt.NegativeSobolevGenerator

/-! # Actual weak first-order formulation on the closed weighted Sobolev graph -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ContDiff Topology ENNReal InnerProductSpace
namespace GaussianTilt.Letwin

lemma smoothCompactWeightedLaplacian_eq_neg_sum_adjoint {n : ℕ}
    {φ : CoordinateSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ) (v : smoothCompactCore n) :
    smoothCompactWeightedLaplacian hφ v =
      -∑ i, smoothCompactDerivativeAdjoint hφ i (smoothCompactDerivative i v) := by
  apply Subtype.ext
  funext x
  simp only [smoothCompactWeightedLaplacian, LinearMap.coe_mk, AddHom.coe_mk,
    Submodule.coe_neg, Submodule.coe_sum, Pi.neg_apply, Finset.sum_apply]
  change weightedLaplacian φ v.1 x =
    -(∑ i, (coordinateDerivative i φ x * coordinateDerivative i v.1 x -
      coordinateDerivative i (coordinateDerivative i v.1) x))
  rw [weightedLaplacian_apply, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Testing a closed Sobolev function against the actual core generator
is precisely its gradient pairing, by the proved closability/Green identity. -/
theorem weightedSobolev_generator_pairing {n : ℕ}
    {φ : CoordinateSpace n → ℝ} [IsFiniteMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ ∞ φ) (u : weightedSobolev (potentialMeasure φ))
    (v : smoothCompactCore n) :
    (∑ i, inner ℝ (u.1 i.succ)
      (smoothCompactToL2 (potentialMeasure φ) (smoothCompactDerivative i v))) =
      -inner ℝ (u.1 0) (weightedLaplacianToL2 hφ v) := by
  simp_rw [weightedSobolev_integration_by_parts hφ]
  rw [← inner_sum, ← map_sum]
  have he : (∑ i, smoothCompactDerivativeAdjoint hφ i (smoothCompactDerivative i v)) =
      -smoothCompactWeightedLaplacian hφ v := by
    rw [smoothCompactWeightedLaplacian_eq_neg_sum_adjoint, neg_neg]
  rw [he, map_neg, inner_neg_right]
  rfl

lemma weightedLaplacian_eq_zero_of_notMem_tsupport {n : ℕ}
    (φ f : CoordinateSpace n → ℝ) {x : CoordinateSpace n} (hx : x ∉ tsupport f) :
    weightedLaplacian φ f x = 0 := by
  unfold weightedLaplacian divergenceDiffusion weightedCoordinateDivergence
  apply Finset.sum_eq_zero
  intro i _
  have hni : x ∉ tsupport (diffusionFlux (fun _ => 1) f i) :=
    fun hi => hx (tsupport_diffusionFlux_subset (fun _ => 1) f i hi)
  have hz : diffusionFlux (fun _ => 1) f i x = 0 :=
    Function.notMem_support.mp (fun hi => hni (subset_closure hi))
  have hd0 := fderiv_of_notMem_tsupport ℝ hni
  simp only [diffusionFlux_one_fun] at hd0
  simp only [diffusionFlux_one] at hz
  simp only [diffusionFlux_one, diffusionFlux_one_fun, hz, mul_zero, sub_zero]
  change (fderiv ℝ (coordinateDerivative i f) x) (Pi.single i 1) = 0
  rw [hd0]
  rfl

/-- The local weighted Sobolev representative of a generator annihilator is
weakly harmonic on every region where its cutoff is identically one. -/
theorem localized_weightedSobolev_weak_harmonic {n : ℕ}
    {φ χ h : CoordinateSpace n → ℝ} [IsFiniteMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ ∞ φ) (u : weightedSobolev (potentialMeasure φ))
    (hval : u.1 0 =ᵐ[potentialMeasure φ] fun x => χ x * h x)
    (horth : ∀ v : CoordinateSpace n → ℝ, ContDiff ℝ ∞ v → HasCompactSupport v →
      (∫ x, h x * weightedLaplacian φ v x ∂potentialMeasure φ) = 0)
    (v : smoothCompactCore n) (hχ : ∀ x ∈ tsupport v.1, χ x = 1) :
    (∑ i, inner ℝ (u.1 i.succ)
      (smoothCompactToL2 (potentialMeasure φ) (smoothCompactDerivative i v))) = 0 := by
  rw [weightedSobolev_generator_pairing hφ, L2.inner_def]
  have hLv := smoothCompactToL2_ae (potentialMeasure φ) (smoothCompactWeightedLaplacian hφ v)
  have he : (∫ x, inner ℝ (u.1 0 x) (weightedLaplacianToL2 hφ v x) ∂potentialMeasure φ) =
      ∫ x, h x * weightedLaplacian φ v.1 x ∂potentialMeasure φ := by
    apply integral_congr_ae
    filter_upwards [hval, hLv] with x hx hv
    change weightedLaplacianToL2 hφ v x = weightedLaplacian φ v.1 x at hv
    simp only [hx, hv, RCLike.inner_apply, conj_trivial]
    by_cases hs : x ∈ tsupport v.1
    · rw [hχ x hs]
      ring
    · rw [weightedLaplacian_eq_zero_of_notMem_tsupport φ v.1 hs]
      ring
  rw [he, horth v.1 v.2.1 v.2.2, neg_zero]

end GaussianTilt.Letwin
