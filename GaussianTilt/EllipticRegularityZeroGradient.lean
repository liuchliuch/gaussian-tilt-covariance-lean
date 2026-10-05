import GaussianTilt.NegativeSobolevMollifierDistribution

/-! # A locally integrable function with zero distributional gradient is constant -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ContDiff Topology ENNReal InnerProductSpace Convolution
namespace GaussianTilt.Letwin

/-- The actual zero distributional gradient, expressed with compact smooth tests. -/
def HasZeroDistributionGradient {n : ℕ} (h : CoordinateSpace n → ℝ) : Prop :=
  ∀ i : Fin n, ∀ ψ : CoordinateSpace n → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
    (∫ x, h x * coordinateDerivative i ψ x) = 0

lemma fderiv_eq_zero_of_coordinateDerivative {n : ℕ} (h : CoordinateSpace n → ℝ)
    (hz : ∀ i x, coordinateDerivative i h x = 0) (x : CoordinateSpace n) :
    fderiv ℝ h x = 0 := by
  ext v
  rw [← Finset.univ_sum_single v, map_sum]
  simp only [ContinuousLinearMap.zero_apply]
  apply Finset.sum_eq_zero
  intro i _
  have he : Pi.single i (v i) = v i • (Pi.single i 1 : CoordinateSpace n) := by
    ext j
    by_cases hj : j = i
    · subst j; simp
    · simp [hj]
  rw [he, map_smul]
  change v i * coordinateDerivative i h x = 0
  rw [hz i x, mul_zero]

lemma HasZeroDistributionGradient.scalarConvolution_derivative_zero {n : ℕ}
    {h ρ : CoordinateSpace n → ℝ} (hz : HasZeroDistributionGradient h)
    (hh : LocallyIntegrable h volume) (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    (i : Fin n) (x : CoordinateSpace n) :
    coordinateDerivative i (scalarConvolution ρ h) x = 0 := by
  rw [coordinateDerivative_scalarConvolution_of_locallyIntegrable hρ hρc hh,
    scalarConvolution_flip_apply]
  have hψ : ContDiff ℝ ∞ (fun y : CoordinateSpace n => ρ (x-y)) :=
    hρ.comp (contDiff_const.sub contDiff_id)
  have hψc : HasCompactSupport (fun y : CoordinateSpace n => ρ (x-y)) :=
    hρc.comp_homeomorph (Homeomorph.subLeft x)
  have he := hz i _ hψ hψc
  have heq (y : CoordinateSpace n) : coordinateDerivative i (fun z => ρ (x-z)) y =
      -coordinateDerivative i ρ (x-y) := coordinateDerivative_const_sub_comp hρ x i y
  simp_rw [heq, mul_neg] at he
  rw [integral_neg] at he
  linarith

/-- Almost-everywhere convergence of the fixed actual mollifiers for every
locally integrable function, from Lebesgue differentiation. -/
theorem ae_mollify_tendsto_of_locallyIntegrable {n : ℕ} {h : CoordinateSpace n → ℝ}
    (hh : LocallyIntegrable h volume) :
    ∀ᵐ x ∂volume, Tendsto (fun k => mollify k h x) atTop (𝓝 (h x)) := by
  apply ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (φ := canonicalMollifierBump n) (K := 2) ?_ ?_ hh
  · change Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) atTop (𝓝 0)
    simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat
  · filter_upwards with k
    change ((k : ℝ) + 1)⁻¹ ≤ 2 * (((k : ℝ) + 1)⁻¹ / 2)
    linarith

/-- The zero distributional gradient forces a single actual almost-everywhere
constant, proved using smooth mollification and its Lebesgue-point limit. -/
theorem HasZeroDistributionGradient.ae_eq_const {n : ℕ} {h : CoordinateSpace n → ℝ}
    (hz : HasZeroDistributionGradient h) (hh : LocallyIntegrable h volume) :
    ∃ c : ℝ, h =ᵐ[volume] fun _ => c := by
  have hc (k : ℕ) (x y : CoordinateSpace n) : mollify k h x = mollify k h y := by
    have hs : ContDiff ℝ ∞ (mollify k h) :=
      (canonicalMollifier_compact n k).contDiff_convolution_left
        (ContinuousLinearMap.lsmul ℝ ℝ) (canonicalMollifier_smooth n k) hh
    apply is_const_of_fderiv_eq_zero (hs.differentiable (by simp)) _ x y
    exact fderiv_eq_zero_of_coordinateDerivative _ (fun i z =>
      hz.scalarConvolution_derivative_zero hh (canonicalMollifier_smooth n k)
        (canonicalMollifier_compact n k) i z)
  have hlim := ae_mollify_tendsto_of_locallyIntegrable hh
  obtain ⟨x, hx⟩ := hlim.exists
  refine ⟨h x, ?_⟩
  filter_upwards [hlim] with y hy
  exact tendsto_nhds_unique hy (hx.congr' (Eventually.of_forall fun k => hc k x y))

end GaussianTilt.Letwin
