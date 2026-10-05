import GaussianTilt.GaussianConcentrationMoments

/-!
# Lower bounds for scalar Gaussian moments

The actual normalized radial Gaussian in dimension one has moments at least
of order `sqrt p`.  The proof integrates its density over `[sqrt p, 2 sqrt p]`.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators InnerProductSpace
namespace GaussianTilt.Paouris

/-- The canonical isometry from the real line to one-dimensional Euclidean space. -/
def scalarGaussianIsometry : ℝ ≃ₗᵢ[ℝ] Reference.Space 1 :=
  (OrthonormalBasis.singleton (Fin 1) ℝ).repr

lemma integral_scalarGaussian_norm (p : ℝ) :
    (∫ x : Reference.Space 1, ‖x‖ ^ p ∂standardGaussian 1) =
      (∫ t : ℝ, |t| ^ p * Real.exp (-(1 / 2 : ℝ) * t ^ 2)) /
        (2 * Real.pi) ^ ((1 : ℝ) / 2) := by
  rw [integral_standardGaussian, integral_gaussianKernel]
  norm_num only [Nat.cast_one]
  congr 1
  have h := MeasureTheory.integral_comp scalarGaussianIsometry
    (fun x ↦ ‖x‖ ^ p * gaussianKernel 1 x)
  simpa only [gaussianKernel, LinearIsometryEquiv.norm_map, Real.norm_eq_abs, sq_abs] using h.symm

lemma scalarGaussian_rpow_density_integrable {p : ℝ} (hp : 0 ≤ p) :
    Integrable (fun t : ℝ ↦ |t| ^ p * Real.exp (-(1 / 2 : ℝ) * t ^ 2)) := by
  have h := standardGaussian_lipschitz_abs_rpow_integrable
    (lipschitzWith_one_norm : LipschitzWith 1 (fun x : Reference.Space 1 ↦ ‖x‖)) hp
  simp only [abs_norm] at h
  have hi := (integrable_standardGaussian_iff _).mp h
  have hh := (MeasureTheory.integrable_comp scalarGaussianIsometry _).mpr hi
  change Integrable (fun t : ℝ ↦ ‖scalarGaussianIsometry t‖ ^ p *
    gaussianKernel 1 (scalarGaussianIsometry t)) at hh
  simpa only [Function.comp_apply, gaussianKernel, LinearIsometryEquiv.norm_map,
    Real.norm_eq_abs, sq_abs] using hh

lemma scalarGaussian_density_moment_lower {p : ℝ} (hp : 2 ≤ p) :
    Real.sqrt p ^ p * Real.exp (-2 * p) ≤
      ∫ t : ℝ, |t| ^ p * Real.exp (-(1 / 2 : ℝ) * t ^ 2) := by
  have hp0 : 0 ≤ p := by linarith
  have hs : 0 ≤ Real.sqrt p := Real.sqrt_nonneg p
  have hs1 : 1 ≤ Real.sqrt p := by
    have h := Real.sq_sqrt hp0
    nlinarith
  have hsi : Integrable (fun t : ℝ ↦ |t| ^ p * Real.exp (-(1 / 2 : ℝ) * t ^ 2)) :=
    scalarGaussian_rpow_density_integrable hp0
  have hpoint (t : ℝ) (ht : t ∈ Icc (Real.sqrt p) (2 * Real.sqrt p)) :
      Real.sqrt p ^ p * Real.exp (-2 * p) ≤
        |t| ^ p * Real.exp (-(1 / 2 : ℝ) * t ^ 2) := by
    have ht0 : 0 ≤ t := hs.trans ht.1
    have ht2 : t ^ 2 ≤ 4 * p := by
      have hm := mul_self_le_mul_self ht0 ht.2
      nlinarith [Real.sq_sqrt hp0]
    apply mul_le_mul
    · exact Real.rpow_le_rpow hs (ht.1.trans (le_abs_self _)) hp0
    · exact Real.exp_le_exp.mpr (by linarith)
    · positivity
    · positivity
  have hbound := setIntegral_ge_of_const_le measurableSet_Icc
    (measure_Icc_lt_top : volume (Icc (Real.sqrt p) (2 * Real.sqrt p)) < ⊤).ne
    hpoint hsi.integrableOn
  rw [Real.volume_real_Icc_of_le (by linarith : Real.sqrt p ≤ 2 * Real.sqrt p)] at hbound
  have hnonneg : 0 ≤ Real.sqrt p ^ p * Real.exp (-2 * p) := by positivity
  calc
    _ ≤ (Real.sqrt p ^ p * Real.exp (-2 * p)) * Real.sqrt p :=
      le_mul_of_one_le_right hnonneg hs1
    _ ≤ ∫ t in Icc (Real.sqrt p) (2 * Real.sqrt p),
        |t| ^ p * Real.exp (-(1 / 2 : ℝ) * t ^ 2) := by
      convert hbound using 1; ring
    _ ≤ _ := setIntegral_le_integral hsi (Eventually.of_forall fun t ↦ by positivity)

lemma scalarGaussian_normalizer_le_four :
    (2 * Real.pi) ^ ((1 : ℝ) / 2) ≤ 4 := by
  rw [← Real.sqrt_eq_rpow]
  have h := Real.sq_sqrt (show 0 ≤ 2 * Real.pi by positivity)
  have hpi := Real.pi_lt_four
  nlinarith [Real.sqrt_nonneg (2 * Real.pi)]

/-- A universal positive constant for the scalar Gaussian moment lower bound. -/
def scalarGaussianLowerConstant : ℝ := Real.exp (-2) / 4

lemma scalarGaussianLowerConstant_pos : 0 < scalarGaussianLowerConstant := by
  unfold scalarGaussianLowerConstant
  positivity

/-- All real scalar Gaussian moments of order at least two dominate `sqrt p`.
The law is the normalized radial Gaussian used throughout the Paouris proof. -/
theorem standardGaussian_scalar_moment_lower {p : ℝ} (hp : 2 ≤ p) :
    scalarGaussianLowerConstant * Real.sqrt p ≤
      (∫ x : Reference.Space 1, ‖x‖ ^ p ∂standardGaussian 1) ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  have hs : 0 ≤ Real.sqrt p := Real.sqrt_nonneg p
  have hfour : (4 : ℝ) ≤ 4 ^ p := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 4) (by linarith : (1 : ℝ) ≤ p)
  have hden : 0 < (2 * Real.pi) ^ ((1 : ℝ) / 2) := by positivity
  have hpower : (scalarGaussianLowerConstant * Real.sqrt p) ^ p ≤
      ∫ x : Reference.Space 1, ‖x‖ ^ p ∂standardGaussian 1 := by
    rw [integral_scalarGaussian_norm]
    calc
      _ = (Real.sqrt p ^ p * Real.exp (-2 * p)) / (4 : ℝ) ^ p := by
        rw [scalarGaussianLowerConstant, Real.mul_rpow (by positivity) hs,
          Real.div_rpow (by positivity) (by norm_num), ← Real.exp_mul]
        ring
      _ ≤ (Real.sqrt p ^ p * Real.exp (-2 * p)) /
          (2 * Real.pi) ^ ((1 : ℝ) / 2) :=
        div_le_div_of_nonneg_left (by positivity) hden
          (scalarGaussian_normalizer_le_four.trans hfour)
      _ ≤ _ := div_le_div_of_nonneg_right (scalarGaussian_density_moment_lower hp) hden.le
  have hr := Real.rpow_le_rpow (Real.rpow_nonneg
    (mul_nonneg scalarGaussianLowerConstant_pos.le hs) p) hpower (by positivity : 0 ≤ 1 / p)
  rw [← Real.rpow_mul (mul_nonneg scalarGaussianLowerConstant_pos.le hs),
    mul_one_div_cancel hp0.ne', Real.rpow_one] at hr
  exact hr

end GaussianTilt.Paouris
