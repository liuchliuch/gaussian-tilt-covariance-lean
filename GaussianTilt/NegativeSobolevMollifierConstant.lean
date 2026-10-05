import GaussianTilt.NegativeSobolevMollifierDistribution

/-! # Zero distributional gradient means almost-everywhere constancy -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ContDiff Topology ENNReal Convolution
namespace GaussianTilt.Letwin

/-- The explicitly constructed mollifiers recover every locally integrable
function almost everywhere, by the actual Lebesgue differentiation theorem. -/
theorem ae_mollify_tendsto {n : ℕ} {h : CoordinateSpace n → ℝ}
    (hh : LocallyIntegrable h volume) :
    ∀ᵐ x ∂volume, Tendsto (fun k => mollify k h x) atTop (𝓝 (h x)) := by
  apply ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (φ := canonicalMollifierBump n) (K := 2)
  · change Tendsto (fun k : ℕ => ((k : ℝ)+1)⁻¹) atTop (𝓝 0)
    exact tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  · exact Filter.Eventually.of_forall fun k => by
      change ((k : ℝ)+1)⁻¹ ≤ 2*(((k : ℝ)+1)⁻¹/2)
      linarith
  · exact hh

/-- A zero distributional coordinate derivative becomes a genuinely zero
classical derivative after actual mollification. -/
theorem coordinateDerivative_mollify_eq_zero {n : ℕ} {h : CoordinateSpace n → ℝ}
    (hh : LocallyIntegrable h volume) (i : Fin n)
    (hz : ∀ ψ : CoordinateSpace n → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ x, h x * coordinateDerivative i ψ x) = 0)
    (k : ℕ) (x : CoordinateSpace n) : coordinateDerivative i (mollify k h) x = 0 := by
  let ρ := canonicalMollifier n k
  have hρ : ContDiff ℝ ∞ ρ := canonicalMollifier_smooth n k
  have hρc : HasCompactSupport ρ := canonicalMollifier_compact n k
  have hψ : ContDiff ℝ ∞ (fun y => ρ (x-y)) := hρ.comp (contDiff_const.sub contDiff_id)
  have hψc : HasCompactSupport (fun y => ρ (x-y)) := hρc.comp_homeomorph (Homeomorph.subLeft x)
  have ht := hz (fun y => ρ (x-y)) hψ hψc
  simp only [coordinateDerivative_const_sub_comp hρ, mul_neg, integral_neg] at ht
  change coordinateDerivative i (scalarConvolution ρ h) x = 0
  rw [coordinateDerivative_scalarConvolution_of_locallyIntegrable hρ hρc hh i,
    scalarConvolution_flip_apply]
  linarith

/-- Every locally integrable function whose distributional gradient
vanishes is almost everywhere constant. The proof constructs actual smooth
constant mollifications and passes to their actual AE limit. -/
theorem ae_eq_const_of_distribution_gradient_zero {n : ℕ} {h : CoordinateSpace n → ℝ}
    (hh : LocallyIntegrable h volume)
    (hz : ∀ i : Fin n, ∀ ψ : CoordinateSpace n → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ x, h x * coordinateDerivative i ψ x) = 0) :
    ∃ c : ℝ, h =ᵐ[volume] fun _ => c := by
  have hd (k : ℕ) (x : CoordinateSpace n) : fderiv ℝ (mollify k h) x = 0 := by
    ext v
    rw [fderiv_apply_eq_sum_coordinates]
    simp only [coordinateDerivative_mollify_eq_zero hh _ (hz _) k x, mul_zero,
      Finset.sum_const_zero, ContinuousLinearMap.zero_apply]
  have hc (k : ℕ) (x y : CoordinateSpace n) : mollify k h x = mollify k h y :=
    is_const_of_fderiv_eq_zero ((mollify_smooth_of_locallyIntegrable hh k).differentiable (by simp))
      (hd k) x y
  have hlim := ae_mollify_tendsto hh
  obtain ⟨x₀, hx₀⟩ := hlim.exists
  refine ⟨h x₀, ?_⟩
  filter_upwards [hlim] with x hx
  have hx' : Tendsto (fun k => mollify k h x₀) atTop (𝓝 (h x)) :=
    hx.congr (fun k => hc k x x₀)
  exact tendsto_nhds_unique hx' hx₀

end GaussianTilt.Letwin
