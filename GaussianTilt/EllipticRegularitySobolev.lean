import GaussianTilt.EllipticRegularityCompactness
import GaussianTilt.EllipticRegularityMollifiedEnergy
import GaussianTilt.NegativeSobolevMollifierFamily
import GaussianTilt.NegativeSobolevMollifierDistribution

/-! # From the actual elliptic energy bounds to the closed Sobolev graph -/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set
open scoped BigOperators ContDiff Topology ENNReal InnerProductSpace
namespace GaussianTilt.Letwin

lemma norm_smoothCompactJet_sq {n : ℕ} (μ : Measure (CoordinateSpace n))
    [IsFiniteMeasureOnCompacts μ] (u : smoothCompactCore n) :
    ‖smoothCompactJet μ u‖^2 = (∫ x, u.1 x^2 ∂μ) + ∫ x, gradientSquare u.1 x ∂μ := by
  rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply, Fin.sum_univ_succ]
  simp only [smoothCompactJet_zero, smoothCompactJet_succ, inner_smoothCompactToL2]
  have hI (i : Fin n) : Integrable (fun x => (coordinateDerivative i u.1 x)^2) μ :=
    (smooth_compact_memLp (smooth_coordinateDerivative u.2.1 i)
      (u.2.2.fderiv_apply (𝕜 := ℝ) (Pi.single i 1))).integrable_sq
  simp only [smoothCompactDerivative, pow_two, gradientSquare]
  rw [integral_finset_sum _ (fun i _ => by simpa only [pow_two] using hI i)]
  rfl

/-- The actual smooth compact mollified functions as elements of the core. -/
def mollifiedCore {n : ℕ} {f : CoordinateSpace n → ℝ}
    (hf : MemLp f 2 volume) (hfc : HasCompactSupport f) (k : ℕ) : smoothCompactCore n :=
  ⟨mollify k f, mollify_smooth hf k, mollify_compact hfc k⟩

/-- Strong convergence of the actual L² equivalence classes of the
constructed smooth compact mollifications. -/
theorem smoothCompactToL2_mollifiedCore_tendsto {n : ℕ} {f : CoordinateSpace n → ℝ}
    (hf : MemLp f 2 volume) (hfc : HasCompactSupport f) :
    Tendsto (fun k => smoothCompactToL2 volume (mollifiedCore hf hfc k)) atTop
      (𝓝 (hf.toLp f)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have he (k : ℕ) : ‖smoothCompactToL2 volume (mollifiedCore hf hfc k) - hf.toLp f‖^2 =
      ∫ x, (mollify k f x - f x)^2 := by
    change ‖(mollify_memLp hf k).toLp (mollify k f) - hf.toLp f‖^2 = _
    rw [← MemLp.toLp_sub]
    exact norm_toLp_sq_eq_integral ((mollify_memLp hf k).sub hf)
  have ht := (integral_mollify_sub_sq_tendsto hf).sqrt
  simp_rw [← he, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at ht
  exact ht

/-- Local elliptic regularity in the actual Hilbert space: a compact L²
solution of Δf=div F+g with L² data has genuine weak L² first derivatives.
The proof mollifies the equation, proves the energy bound, and applies
proved Hilbert weak compactness to the actual value/gradient jets. -/
theorem distributionLaplacian_hasSobolev {n : ℕ}
    {f g : CoordinateSpace n → ℝ} {F : Fin n → CoordinateSpace n → ℝ}
    (hf : MemLp f 2 volume) (hfc : HasCompactSupport f)
    (hF : ∀ i, MemLp (F i) 2 volume) (hg : MemLp g 2 volume)
    (heq : HasDistributionLaplacian f F g) :
    ∃ u : weightedSobolev (volume : Measure (CoordinateSpace n)),
      weightedSobolevValue (volume : Measure (CoordinateSpace n)) u = hf.toLp f := by
  let C := 2 * (∫ x, f x^2) + (∑ i, ∫ x, (F i x)^2) + ∫ x, g x^2
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hc {v : CoordinateSpace n → ℝ} (hv : MemLp v 2 volume) (k : ℕ) :
      (∫ x, (mollify k v x)^2) ≤ ∫ x, v x^2 :=
    integral_scalarConvolution_sq_le (canonicalMollifier_smooth n k).continuous
      (canonicalMollifier_compact n k) (canonicalMollifier_nonneg n k)
      (canonicalMollifier_integral n k) hv
  have hb (k : ℕ) : ‖smoothCompactJet volume (mollifiedCore hf hfc k)‖ ≤ Real.sqrt C := by
    have he := distributionLaplacian_gradient_energy_le (mollify_smooth hf k)
      (mollify_compact hfc k) (fun i => mollify_memLp (hF i) k) (mollify_memLp hg k)
      (heq.mollify hf hF hg k)
    have hs : (∑ i, ∫ x, (mollify k (F i) x)^2) ≤ ∑ i, ∫ x, (F i x)^2 :=
      Finset.sum_le_sum fun i _ => hc (hF i) k
    have hsq : ‖smoothCompactJet volume (mollifiedCore hf hfc k)‖^2 ≤ C := by
      rw [norm_smoothCompactJet_sq]
      change (∫ x, (mollify k f x)^2) + ∫ x, gradientSquare (mollify k f) x ≤ C
      dsimp [C]
      linarith [hc hf k, hc hg k]
    nlinarith [Real.sq_sqrt hC, Real.sqrt_nonneg C,
      norm_nonneg (smoothCompactJet volume (mollifiedCore hf hfc k))]
  obtain ⟨u, hu, -⟩ := exists_weightedSobolev_of_bounded_smooth_jets (n := n)
    (volume : Measure (CoordinateSpace n)) (mollifiedCore hf hfc)
    (f := hf.toLp f) (B := Real.sqrt C) hb (smoothCompactToL2_mollifiedCore_tendsto hf hfc)
  exact ⟨u, hu⟩

/-- The required local H¹ regularity for every actual weighted-generator
annihilator. No smoothness of h, weak derivative, or elliptic regularity is
assumed: every compact localization is proved to lie in the closed H¹ graph. -/
theorem weighted_generator_orthogonal_local_H1 {n : ℕ}
    {φ h χ : CoordinateSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hh : MemLp h 2 (potentialMeasure φ))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (horth : ∀ v : CoordinateSpace n → ℝ, ContDiff ℝ ∞ v → HasCompactSupport v →
      (∫ x, h x * weightedLaplacian φ v x ∂potentialMeasure φ) = 0) :
    ∃ u : weightedSobolev (volume : Measure (CoordinateSpace n)),
      weightedSobolevValue (volume : Measure (CoordinateSpace n)) u =
        (memLp_compact_mul_of_potential hφ.continuous hh hχ.continuous hχc).toLp
          (fun x => χ x * h x) := by
  have hdata := localizedElliptic_memLp hφ hχ hχc hh
  exact distributionLaplacian_hasSobolev hdata.1 hχc.mul_right hdata.2.1 hdata.2.2
    (weighted_generator_orthogonal_localized hφ hχ hχc horth)

end GaussianTilt.Letwin
