import GaussianTilt.EuclideanBrascampLieb
import GaussianTilt.OperatorDynamics

/-! # Actual Gaussian-tilt covariance from the proved nonsmooth density inequality -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal Matrix.Norms.L2Operator
namespace GaussianTilt.CompactProbability
variable {n : ℕ} (P : CompactProbability n)

lemma integral_of_lebesgue_density {f : Point n → ℝ} (hf : Measurable f)
    (hfn : ∀ x, 0 ≤ f x) (hμ : P.measure = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)))
    (g : Point n → ℝ) : (∫ x, g x ∂P.measure) = ∫ x, g x * f x := by
  rw [hμ, integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hfn _), smul_eq_mul]
  congr 1
  funext x
  ring

lemma integral_lebesgue_density {f : Point n → ℝ} (hf : Measurable f)
    (hfn : ∀ x, 0 ≤ f x) (hμ : P.measure = volume.withDensity (fun x ↦ ENNReal.ofReal (f x))) :
    (∫ x, f x) = 1 := by
  have h := P.integral_of_lebesgue_density hf hfn hμ (fun _ ↦ (1 : ℝ))
  simpa only [one_mul, integral_const, measureReal_univ_eq_one, smul_eq_mul] using h.symm

lemma covariance_quadratic_eq_densityVariance {f : Point n → ℝ} (hf : Measurable f)
    (hfn : ∀ x, 0 ≤ f x) (hμ : P.measure = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)))
    (u : Point n) :
    matrixQuadratic (Reference.covariance P.measure) (fun i ↦ u i) =
      EuclideanBrascampLieb.densityDirectionalVariance f u := by
  have hX (i : Fin n) : MemLp (fun x : Point n ↦ x i) 2 P.measure := by
    simpa only [P.tilt_zero] using P.memLp_continuous_tilt (f := fun x : Point n ↦ x i) (by fun_prop) 0 2
  have hlin : MemLp (fun x : Point n ↦ inner ℝ u x) 2 P.measure := by
    simpa only [P.tilt_zero] using P.memLp_continuous_tilt (f := fun x : Point n ↦ inner ℝ u x) (by fun_prop) 0 2
  have hc := P.reference_covariance_eq_covarianceMatrix 0
  rw [P.tilt_zero] at hc
  rw [hc, ← variance_linear_eq_covariance hX]
  have he : (fun x : Point n ↦ (fun i ↦ u i) ⬝ᵥ (fun i ↦ x i)) = (fun x ↦ inner ℝ u x) := by
    funext x
    simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
    exact dotProduct_comm _ _
  rw [he, variance_eq_sub hlin, EuclideanBrascampLieb.densityDirectionalVariance,
    P.integral_lebesgue_density hf hfn hμ]
  simp only [div_one, P.integral_of_lebesgue_density hf hfn hμ, Pi.pow_apply]

/-- The proved Brascamp--Lieb bound for an actual compact probability law,
allowing measurable densities that vanish on arbitrary convex support sets. -/
theorem covariance_opNorm_le_inv_of_strong_density {f : Point n → ℝ} {κ : ℝ}
    (hκ : 0 < κ) (hf : LogConcaveMarginal.IsStronglyLogConcave (fun x ↦ ‖x‖ ^ 2) κ f)
    (hm : Measurable f)
    (hμ : P.measure = volume.withDensity (fun x ↦ ENNReal.ofReal (f x))) :
    ‖Reference.covariance P.measure‖ ≤ κ⁻¹ := by
  have hZ := P.integral_lebesgue_density hm hf.nonneg hμ
  have hi : Integrable f := integrable_of_integral_eq_one hZ
  have hpsd := P.covariance_posSemidef 0
  rw [P.tilt_zero] at hpsd
  apply symmetric_opNorm_le_of_quadratic hpsd.1 (inv_nonneg.mpr hκ.le)
  intro u hu
  have hnon : 0 ≤ matrixQuadratic (Reference.covariance P.measure) (fun i ↦ u i) := by
    simpa only [matrixQuadratic, star_trivial] using hpsd.2 (fun i ↦ u i)
  rw [abs_of_nonneg hnon, P.covariance_quadratic_eq_densityVariance hm hf.nonneg hμ]
  have h := EuclideanBrascampLieb.directional_variance_le_inv_of_integrable
    hκ hf hm hi (by rw [hZ]; norm_num) u
  simpa only [hu, one_pow, mul_one] using h

/-- The actual Gaussian-tilt covariance bound, obtained from proved nonsmooth
Brascamp--Lieb and the initial logconcave density. No covariance bound is an input. -/
theorem gaussianTilt_covariance_opNorm_le_inv {t : ℝ} (ht : 0 < t)
    (hlog : Reference.logconcave P.measure) :
    ‖Reference.covariance (P.tilt t)‖ ≤ 1 / (2 * t) := by
  obtain ⟨f, hf, hμ⟩ := hlog
  let g : Point n → ℝ := fun x ↦ f x * P.density t x
  have hgm : Measurable g := hf.2.1.mul (P.continuous_density t).measurable
  have hk := Reference.logconcaveDensity_mul hf
    (Reference.gaussian_logconcaveDensity (n := n) 0 (P.logPartition t) (by norm_num))
  have hk' : LogConcaveMarginal.IsLogConcave (fun x ↦ f x * Real.exp (-P.logPartition t)) := by
    exact ⟨by simpa only [neg_zero, zero_mul, zero_sub] using hk.1,
      by simpa only [neg_zero, zero_mul, zero_sub] using hk.2.2⟩
  have hstrong : LogConcaveMarginal.IsStronglyLogConcave (fun x ↦ ‖x‖ ^ 2) (2 * t) g := by
    have heq : (fun x ↦ g x * Real.exp ((2 * t) / 2 * ‖x‖ ^ 2)) =
        (fun x ↦ f x * Real.exp (-P.logPartition t)) := by
      funext x
      dsimp only [g]
      rw [P.density_eq_exp, mul_assoc, ← Real.exp_add]
      congr 2
      dsimp only [energy]
      ring
    unfold LogConcaveMarginal.IsStronglyLogConcave
    rw [heq]
    exact hk'
  have htilt : P.tilt t = volume.withDensity (fun x ↦ ENNReal.ofReal (g x)) := by
    rw [tilt, hμ, ← withDensity_mul volume hf.2.1.ennreal_ofReal
      (P.continuous_density t).measurable.ennreal_ofReal]
    congr 1
    funext x
    exact (ENNReal.ofReal_mul (hf.1 x)).symm
  obtain ⟨Q, hQ⟩ := exists_compactProbability_of_compactlySupported (P.tilt t)
    (P.reference_tilt_compactlySupported t)
  have h := Q.covariance_opNorm_le_inv_of_strong_density (by positivity : 0 < 2 * t)
    hstrong hgm (hQ.trans htilt)
  simpa only [hQ, one_div] using h

end GaussianTilt.CompactProbability
