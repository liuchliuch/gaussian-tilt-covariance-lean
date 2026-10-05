import GaussianTilt.MomentMapApproximation
import GaussianTilt.PaourisGaussian

/-!
# Gaussian perturbation: fourth moments and explicit polynomial convergence

The normalized Gaussian used here has its density and normalization proved in
`PaourisGaussian`. Its fourth moment is proved finite below. Applying the
constructed perturbation and conditioning therefore gives actual convergence
of all coordinate monomials of degree at most four.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal BigOperators
namespace GaussianTilt.MomentMapApproximation
open Paouris

instance standardGaussian_isOpenPosMeasure (n : ℕ) : (standardGaussian n).IsOpenPosMeasure := by
  have hac : (volume : Measure (Reference.Space n)) ≪ standardGaussian n := by
    apply withDensity_absolutelyContinuous'
      (standardGaussianDensity_continuous n).measurable.ennreal_ofReal.aemeasurable
    exact ae_of_all _ (fun x => (ENNReal.ofReal_pos.mpr (standardGaussianDensity_pos x)).ne')
  exact hac.isOpenPosMeasure

instance gaussianTruncation_probability {n : ℕ}
    (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ] (k : ℕ) :
    IsProbabilityMeasure (perturbedTruncation μ (standardGaussian n) k) :=
  perturbedTruncation_probability μ (standardGaussian n) k

lemma norm_fourth_mul_gaussianKernel_le {n : ℕ} (x : Reference.Space n) :
    ‖x‖ ^ 4 * gaussianKernel n x ≤
      64 * Real.exp (-(1 / 4 : ℝ) * ‖x‖ ^ 2) := by
  have he : ‖x‖ ^ 2 / 8 ≤ Real.exp (‖x‖ ^ 2 / 8) := by
    linarith [Real.add_one_le_exp (‖x‖ ^ 2 / 8)]
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ ‖x‖ ^ 2 / 8) he 2
  rw [← Real.exp_nat_mul] at hs
  have hm := mul_le_mul_of_nonneg_right hs
    (Real.exp_nonneg (-(1 / 2 : ℝ) * ‖x‖ ^ 2))
  rw [← Real.exp_add] at hm
  have heq : 2 * (‖x‖ ^ 2 / 8) + -(1 / 2 : ℝ) * ‖x‖ ^ 2 =
      -(1 / 4 : ℝ) * ‖x‖ ^ 2 := by ring
  norm_num only [Nat.cast_ofNat] at hm
  rw [heq] at hm
  dsimp [gaussianKernel]
  nlinarith

/-- The fourth moment of the actual standard Gaussian density is finite. -/
theorem standardGaussian_norm_fourth_integrable (n : ℕ) :
    Integrable (fun x : Reference.Space n => ‖x‖ ^ 4) (standardGaussian n) := by
  apply (integrable_standardGaussian_iff _).mpr
  apply ((exp_neg_norm_sq_integrable (n := n) (by norm_num : (0 : ℝ) < 1 / 4)).const_mul 64).mono'
    (by unfold gaussianKernel; fun_prop)
  apply ae_of_all
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (by unfold gaussianKernel; positivity)]
  exact norm_fourth_mul_gaussianKernel_le x

/-- An arbitrary coordinate monomial, including the empty product. -/
def coordinateMonomial {n d : ℕ} (a : Fin d → Fin n) (x : Reference.Space n) : ℝ :=
  ∏ i, x (a i)

lemma continuous_coordinateMonomial {n d : ℕ} (a : Fin d → Fin n) :
    Continuous (coordinateMonomial a) := by
  unfold coordinateMonomial
  fun_prop

lemma coordinateMonomial_norm_le {n d : ℕ} (a : Fin d → Fin n) (x : Reference.Space n) :
    ‖coordinateMonomial a x‖ ≤ ‖x‖ ^ d := by
  calc
    _ = ∏ i : Fin d, ‖x (a i)‖ := by simp [coordinateMonomial, norm_prod]
    _ ≤ ∏ _i : Fin d, ‖x‖ := by
      apply Finset.prod_le_prod (fun i _ => norm_nonneg _)
      intro i _
      exact PiLp.norm_apply_le x (a i)
    _ = _ := by simp

lemma pow_le_one_add_fourth {r : ℝ} (hr : 0 ≤ r) {d : ℕ} (hd : d ≤ 4) :
    r ^ d ≤ 1 + r ^ 4 := by
  by_cases hr1 : r ≤ 1
  · have h := pow_le_pow_left₀ hr hr1 d
    simp only [one_pow] at h
    exact h.trans (by linarith [pow_nonneg hr 4])
  · exact (pow_le_pow_right₀ (le_of_not_ge hr1) hd).trans (by linarith)

theorem coordinateMonomial_fourth_growth {n d : ℕ} (a : Fin d → Fin n) (hd : d ≤ 4)
    (x : Reference.Space n) : ‖coordinateMonomial a x‖ ≤ 1 * (1 + ‖x‖ ^ 4) := by
  rw [one_mul]
  exact (coordinateMonomial_norm_le a x).trans (pow_le_one_add_fourth (norm_nonneg _) hd)

/-- All moments of degree at most four converge for these explicitly
constructed Gaussian-perturbed, conditioned laws. -/
theorem gaussianTruncation_monomial_moment_tendsto {n d : ℕ}
    (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : Reference.Space n => ‖x‖ ^ 4) μ)
    (a : Fin d → Fin n) (hd : d ≤ 4) :
    Tendsto (fun k => ∫ x, coordinateMonomial a x
      ∂perturbedTruncation μ (standardGaussian n) k)
      atTop (𝓝 (∫ x, coordinateMonomial a x ∂μ)) :=
  tendsto_integral_perturbedTruncation μ (standardGaussian n) hμ
    (standardGaussian_norm_fourth_integrable n) (continuous_coordinateMonomial a)
    (by norm_num) (coordinateMonomial_fourth_growth a hd)

theorem polynomial_fourth_growth {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : p.totalDegree ≤ 4) (x : Reference.Space n) :
    ‖MvPolynomial.eval (fun i => x i) p‖ ≤
      (∑ a ∈ p.support, ‖p.coeff a‖) * (1 + ‖x‖ ^ 4) := by
  rw [MvPolynomial.eval_eq, Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro a ha
  rw [norm_mul, norm_prod]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    (∏ i ∈ a.support, ‖x i ^ a i‖) ≤ ∏ i ∈ a.support, ‖x‖ ^ a i := by
      apply Finset.prod_le_prod (fun i _ => norm_nonneg _)
      intro i _
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le x i) _
    _ = ‖x‖ ^ (a.sum fun _ e => e) := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ 1 + ‖x‖ ^ 4 :=
      pow_le_one_add_fourth (norm_nonneg _) ((MvPolynomial.le_totalDegree ha).trans hp)

/-- The complete polynomial-moment assertion of the perturbation and
conditioning step, for actual multivariate polynomials of degree at most four. -/
theorem gaussianTruncation_polynomial_moment_tendsto {n : ℕ}
    (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : Reference.Space n => ‖x‖ ^ 4) μ)
    (p : MvPolynomial (Fin n) ℝ) (hp : p.totalDegree ≤ 4) :
    Tendsto (fun k => ∫ x, MvPolynomial.eval (fun i => x i) p
      ∂perturbedTruncation μ (standardGaussian n) k)
      atTop (𝓝 (∫ x, MvPolynomial.eval (fun i => x i) p ∂μ)) := by
  apply tendsto_integral_perturbedTruncation μ (standardGaussian n) hμ
    (standardGaussian_norm_fourth_integrable n)
    (p.continuous_eval.comp (by fun_prop))
    (Finset.sum_nonneg (fun a _ => norm_nonneg (p.coeff a)))
  exact polynomial_fourth_growth p hp

end GaussianTilt.MomentMapApproximation
