import GaussianTilt.LetwinNoncompactApproximation

/-!
# Moments of nondegenerate noncompact logconcave laws

Positive-definite reference covariance forces finite second moments despite
Bochner integral totalization. Actual whitening and the proved Paouris bound
then give fourth moments, and every centered quadratic is genuinely in L².
-/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix Set Filter
open scoped Topology BigOperators Matrix.Norms.L2Operator

namespace GaussianTilt.Reference
variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
lemma posDef_covariance_diagonal (hC : (covariance μ).PosDef) (i : Fin n) :
    0 < covariance μ i i := by
  have hne : (Pi.single i (1 : ℝ) : Fin n → ℝ) ≠ 0 := by
    intro hz
    have hh := congrFun hz i
    simp only [Pi.single_eq_same, Pi.zero_apply, one_ne_zero] at hh
  have h := hC.2 (Pi.single i (1 : ℝ)) hne
  simpa only [star_trivial, Matrix.mulVec_single_one, single_dotProduct,
    one_mul, Matrix.col_apply] using h

/-- Nondegeneracy forces each coordinate second moment to be finite. -/
lemma posDef_coordinate_sq_integrable (hC : (covariance μ).PosDef) (i : Fin n) :
    Integrable (fun x : Space n ↦ (x i) ^ 2) μ := by
  by_contra h
  have hz : (∫ x : Space n, x i * x i ∂μ) = 0 := by
    simpa only [pow_two] using integral_undef h
  have hp := posDef_covariance_diagonal hC i
  simp only [covariance, hz] at hp
  nlinarith [sq_nonneg (∫ x : Space n, x i ∂μ)]

lemma posDef_coordinate_memLp (hC : (covariance μ).PosDef) (i : Fin n) :
    MemLp (fun x : Space n ↦ x i) 2 μ :=
  (memLp_two_iff_integrable_sq
    (PiLp.continuous_apply 2 (fun _ : Fin n ↦ ℝ) i).aestronglyMeasurable).mpr
      (posDef_coordinate_sq_integrable hC i)

lemma posDef_whitening_covariance (hC : (covariance μ).PosDef) :
    (Whitening.covariance μ).PosDef := by
  rw [show Whitening.covariance μ = covariance μ from
    (covariance_eq_covarianceMatrix (posDef_coordinate_memLp hC)).symm]
  exact hC

/-- Affine inverse whitening restores the fourth moment of the original law. -/
theorem logconcave_norm_fourth_integrable_of_posDef
    (hl : logconcave μ) (hC : (covariance μ).PosDef) :
    Integrable (fun x : Space n ↦ ‖x‖ ^ 4) μ := by
  let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (Whitening.root (Whitening.covariance μ))
  let m := Whitening.center μ
  have hC' := posDef_whitening_covariance hC
  have hX := posDef_coordinate_memLp hC
  have h4 := Whitening.isotropic_logconcave_norm_fourth_integrable (Whitening.law μ)
    (Whitening.law_logconcave hl hC') (Whitening.law_isotropic hX hC')
  have hcont : Continuous (fun y : Space n ↦ ‖R y + m‖ ^ 4) := by fun_prop
  have hf : Integrable (fun y : Space n ↦ ‖R y + m‖ ^ 4) (Whitening.law μ) := by
    apply ((h4.const_mul (‖R‖ ^ 4)).add (integrable_const (‖m‖ ^ 4))).const_mul 8 |>.mono'
      hcont.aestronglyMeasurable
    apply ae_of_all
    intro y
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) 4)]
    have ha := norm_add_le (R y) m
    have hb := R.le_opNorm y
    have hp := pow_le_pow_left₀ (norm_nonneg _) (ha.trans (add_le_add_right hb _)) 4
    have hs := add_pow_le (mul_nonneg (norm_nonneg R) (norm_nonneg y)) (norm_nonneg m) 4
    norm_num only [Nat.reduceSub, Nat.reducePow] at hs
    rw [mul_pow] at hs
    exact hp.trans hs
  have hmap := (integrable_map_measure hcont.aestronglyMeasurable
    (Whitening.continuous_whitenMap μ).measurable.aemeasurable).mp hf
  have heq : (fun x : Space n ↦ ‖R (Whitening.whitenMap μ x) + m‖ ^ 4) =
      (fun x : Space n ↦ ‖x‖ ^ 4) := by
    funext x
    dsimp only [R, m]
    rw [Whitening.root_whitenMap hC', sub_add_cancel]
  simpa only [Function.comp_def, heq] using hmap

/-- Centered quadratic L² is obtained directly by pulling back the genuine
isotropic whitened law, with no moment assumption added. -/
theorem centered_quadratic_memLp_of_logconcave_posDef
    (hl : logconcave μ) (hC : (covariance μ).PosDef)
    (B : Matrix (Fin n) (Fin n) ℝ) :
    MemLp (fun x : Space n ↦ matrixQuadratic B
      ((fun i ↦ x i) - meanVector μ (fun x ↦ fun i ↦ x i))) 2 μ := by
  have hC' := posDef_whitening_covariance hC
  let A := Whitening.root (Whitening.covariance μ) * B * Whitening.root (Whitening.covariance μ)
  have h4 := Whitening.isotropic_logconcave_norm_fourth_integrable (Whitening.law μ)
    (Whitening.law_logconcave hl hC')
    (Whitening.law_isotropic (posDef_coordinate_memLp hC) hC')
  have hq := Whitening.quadratic_memLp_of_fourth h4 A
  have hcont : Continuous (fun x : Space n ↦ matrixQuadratic A (Whitening.coordinates x)) := by
    unfold matrixQuadratic Matrix.mulVec dotProduct Whitening.coordinates
    fun_prop
  have hp := (memLp_map_measure_iff hcont.aestronglyMeasurable
    (Whitening.continuous_whitenMap μ).measurable.aemeasurable).mp hq
  have heq : (fun x : Space n ↦ matrixQuadratic A
      (Whitening.coordinates (Whitening.whitenMap μ x))) =
      (fun x : Space n ↦ matrixQuadratic B
        (Whitening.coordinates x - meanVector μ Whitening.coordinates)) := by
    funext x
    exact Whitening.quadratic_whitenMap hC' B x
  simpa only [Function.comp_def, heq] using hp

end GaussianTilt.Reference
