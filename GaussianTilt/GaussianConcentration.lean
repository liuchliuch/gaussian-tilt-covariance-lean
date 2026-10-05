import GaussianTilt.GaussianConcentrationApproximation

/-!
# Dimension-free concentration for the actual standard Gaussian law

Pisier's smooth rotation estimate passes to all globally Lipschitz functions
through normalized compactly supported mollifiers. No concentration, Poincaré,
logarithmic Sobolev or comparison inequality is assumed.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators InnerProductSpace
namespace GaussianTilt.Paouris
variable {n : ℕ}

lemma integral_exp_center_le_of_uniform_approximation
    {f g : Reference.Space n → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hg : LipschitzWith K g)
    {ε : ℝ} (hε : ∀ x, dist (g x) (f x) ≤ ε) (s : ℝ) :
    (∫ x, Real.exp (s * (f x - ∫ y, f y ∂standardGaussian n)) ∂standardGaussian n) ≤
      Real.exp (2 * |s| * ε) *
        ∫ x, Real.exp (s * (g x - ∫ y, g y ∂standardGaussian n)) ∂standardGaussian n := by
  have hEf : |(∫ y, g y ∂standardGaussian n) - ∫ y, f y ∂standardGaussian n| ≤ ε := by
    rw [← integral_sub (standardGaussian_lipschitz_integrable hg)
      (standardGaussian_lipschitz_integrable hf)]
    simpa only [measureReal_univ_eq_one, mul_one, Real.norm_eq_abs] using
      norm_integral_le_of_norm_le_const (μ := standardGaussian n)
        (f := fun x ↦ g x - f x) (Filter.Eventually.of_forall fun x ↦ by
          simpa only [dist_eq_norm] using hε x)
  rw [← integral_const_mul]
  apply integral_mono (standardGaussian_exp_center_integrable hf s)
    ((standardGaussian_exp_center_integrable hg s).const_mul _)
  intro x
  dsimp only
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hx : |f x - g x| ≤ ε := by simpa only [Real.dist_eq, abs_sub_comm] using hε x
  have hEf' : |(∫ y, f y ∂standardGaussian n) - ∫ y, g y ∂standardGaussian n| ≤ ε := by
    rwa [abs_sub_comm]
  have hab : |(f x - g x) -
      ((∫ y, f y ∂standardGaussian n) - ∫ y, g y ∂standardGaussian n)| ≤ 2 * ε :=
    (abs_sub _ _).trans (by linarith)
  have hab' := mul_le_mul_of_nonneg_left hab (abs_nonneg s)
  have hs := le_abs_self (s * ((f x - g x) -
    ((∫ y, f y ∂standardGaussian n) - ∫ y, g y ∂standardGaussian n)))
  rw [abs_mul] at hs
  nlinarith

/-- Dimension-free Gaussian Lipschitz concentration, in MGF form. The variance
proxy is `(π L / 2)²`, a universal factor from the quarter-circle argument. -/
theorem standardGaussian_integral_exp_center_le {f : Reference.Space n → ℝ}
    {K : ℝ≥0} (hf : LipschitzWith K f) (s : ℝ) :
    (∫ x, Real.exp (s * (f x - ∫ y, f y ∂standardGaussian n)) ∂standardGaussian n) ≤
      Real.exp ((s * (Real.pi / 2) * K) ^ 2 / 2) := by
  let C := (s * (Real.pi / 2) * K) ^ 2 / 2
  have he (ε : ℝ) (hε : 0 < ε) :
      (∫ x, Real.exp (s * (f x - ∫ y, f y ∂standardGaussian n)) ∂standardGaussian n) ≤
        Real.exp (2 * |s| * ε + C) := by
    obtain ⟨g, hgc, hgl, hclose⟩ := exists_contDiff_lipschitz_uniform_approximation hf hε
    calc
      _ ≤ Real.exp (2 * |s| * ε) *
          ∫ x, Real.exp (s * (g x - ∫ y, g y ∂standardGaussian n)) ∂standardGaussian n :=
        integral_exp_center_le_of_uniform_approximation hf hgl hclose s
      _ ≤ Real.exp (2 * |s| * ε) * Real.exp C :=
        mul_le_mul_of_nonneg_left
          (standardGaussian_integral_exp_center_le_of_contDiff hgc hgl s) (Real.exp_nonneg _)
      _ = _ := (Real.exp_add _ _).symm
  have hc : Continuous (fun ε : ℝ ↦ Real.exp (2 * |s| * ε + C)) := by fun_prop
  have ht : Tendsto (fun ε : ℝ ↦ Real.exp (2 * |s| * ε + C))
      (𝓝[>] 0) (𝓝 (Real.exp C)) := by
    simpa only [mul_zero, zero_add] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  exact le_of_tendsto_of_tendsto tendsto_const_nhds ht
    (eventually_mem_nhdsWithin.mono fun ε hε ↦ he ε hε)

end GaussianTilt.Paouris
