import GaussianTilt.LetwinTraceEnergy

/-! # Actual variance and mean identities for the Hessian sandwich -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ContDiff
namespace GaussianTilt.Letwin

section MatrixProbability
variable {κ Ω : Type*} [Fintype κ] [DecidableEq κ] [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]

def matrixExpectation (μ : Measure Ω) (F : Ω → Matrix κ κ ℝ) : Matrix κ κ ℝ :=
  fun i j => ∫ x, F x i j ∂μ

lemma integral_matrix_conjugate (R : Matrix κ κ ℝ) {H : Ω → Matrix κ κ ℝ}
    (hH : ∀ a b, Integrable (fun x => H x a b) μ) (i j : κ) :
    (∫ x, (R * H x * R) i j ∂μ) = (R * matrixExpectation μ H * R) i j := by
  simp_rw [matrix_conjugate_entry]
  rw [integral_finset_sum _ (fun a _ => integrable_finset_sum _ (fun b _ =>
    (hH a b).const_mul (R i a * R b j)))]
  apply Finset.sum_congr rfl
  intro a _
  rw [integral_finset_sum _ (fun b _ => (hH a b).const_mul (R i a * R b j))]
  simp only [integral_const_mul, matrixExpectation]

lemma sum_variance_matrix_entries {F : Ω → Matrix κ κ ℝ}
    (hF : ∀ i j, MemLp (fun x => F x i j) 2 μ) :
    (∑ i, ∑ j, variance (fun x => F x i j) μ) =
      (∫ x, hsSquare (F x) ∂μ) - hsSquare (matrixExpectation μ F) := by
  simp_rw [variance_eq_sub (hF _ _), Pi.pow_apply, Finset.sum_sub_distrib]
  unfold hsSquare matrixExpectation
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => (hF i j).integrable_sq))]
  simp_rw [integral_finset_sum _ (fun j _ => (hF _ j).integrable_sq)]

end MatrixProbability

lemma le_double_sum_of_nonneg {κ : Type*} [Fintype κ] [DecidableEq κ]
    {f : κ → κ → ℝ} (hf : ∀ i j, 0 ≤ f i j) (i j : κ) : f i j ≤ ∑ a, ∑ b, f a b := by
  exact (Finset.single_le_sum (fun b _ => hf i b) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun a _ => Finset.sum_nonneg (fun b _ => hf a b)) (Finset.mem_univ i))

lemma abs_entry_le_hsSquare_add_one {κ : Type*} [Fintype κ] [DecidableEq κ]
    (M : Matrix κ κ ℝ) (i j : κ) : |M i j| ≤ hsSquare M + 1 := by
  have h := le_double_sum_of_nonneg (fun a b => sq_nonneg (M a b)) i j
  change (M i j)^2 ≤ hsSquare M at h
  have habs := sq_abs (M i j)
  nlinarith [sq_nonneg (|M i j| - 1 / 2)]

lemma hessian_conjugate_entry_bounded {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (R : Matrix (Fin n) (Fin n) ℝ) (S : ℝ)
    (hH : ∀ x i j, |coordinateHessian φ x i j| ≤ S) :
    ∃ C : ℝ, ∀ x i j, |(R * coordinateHessian φ x * R) i j| ≤ C := by
  obtain ⟨C, hC⟩ := hessianSandwichSquare_bounded R S hH
  refine ⟨C + 1, fun x i j => ?_⟩
  calc
    _ ≤ hsSquare (R * coordinateHessian φ x * R) + 1 := abs_entry_le_hsSquare_add_one _ _ _
    _ ≤ |hessianSandwichSquare R φ x| + 1 := add_le_add_right (le_abs_self _) 1
    _ ≤ C + 1 := add_le_add_right (hC x) 1

/-- The Hessian sandwich mean is R²; it follows from the proved score/Hessian
integration identity and actual isotropy of the gradient law. -/
theorem matrixExpectation_hessian_conjugate {n : ℕ} {φ : CoordinateSpace n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ ∞ φ) (Rg S : ℝ)
    (hgb : ∀ x i, |coordinateGradient φ x i| ≤ Rg)
    (hHb : ∀ x i j, |coordinateHessian φ x i j| ≤ S)
    (hiso : covarianceMatrix (potentialMeasure φ) (coordinateGradient φ) = 1)
    (R : Matrix (Fin n) (Fin n) ℝ) :
    matrixExpectation (potentialMeasure φ) (fun x => R * coordinateHessian φ x * R) = R * R := by
  have hmean : matrixExpectation (potentialMeasure φ) (coordinateHessian φ) = 1 :=
    integral_hessian_eq_one_of_isotropic (contDiff_infty.mp hφ 2) Rg S hgb hHb hiso
  have hHi (a b : Fin n) : Integrable (fun x => coordinateHessian φ x a b) (potentialMeasure φ) :=
    Integrable.of_bound (smooth_coordinateHessian hφ a b).continuous.aestronglyMeasurable S
      (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hHb x a b)
  ext i j
  change (∫ x, (R * coordinateHessian φ x * R) i j ∂potentialMeasure φ) = _
  rw [integral_matrix_conjugate R hHi i j, hmean, Matrix.mul_one]

/-- The genuine functional Brascamp--Lieb estimate, summed over the Hessian
sandwich entries, with actual variance and mean identities. This is equation
(2.16) in the form used to finish the trace estimate. -/
theorem hessian_sandwich_variance_le_energy {n : ℕ} {φ : CoordinateSpace n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ ∞ φ) (hH : ∀ x, (coordinateHessian φ x).PosDef)
    (Rg S : ℝ) (hgb : ∀ x i, |coordinateGradient φ x i| ≤ Rg)
    (hHb : ∀ x i j, |coordinateHessian φ x i j| ≤ S)
    (hiso : covarianceMatrix (potentialMeasure φ) (coordinateGradient φ) = 1)
    (R : Matrix (Fin n) (Fin n) ℝ)
    (hEi : Integrable (hessianSandwichEnergy R φ) (potentialMeasure φ)) :
    (∫ x, hessianSandwichSquare R φ x ∂potentialMeasure φ) - hsSquare (R * R) ≤
      ∫ x, hessianSandwichEnergy R φ x ∂potentialMeasure φ := by
  let F := fun x => R * coordinateHessian φ x * R
  have hdet : ∀ x, (coordinateHessian φ x).det ≠ 0 := fun x => (hH x).det_pos.ne'
  have hFc (i j : Fin n) : ContDiff ℝ ∞ (fun x => F x i j) :=
    contDiff_matrix_conjugate R (smooth_coordinateHessian hφ) i j
  obtain ⟨C, hC⟩ := hessian_conjugate_entry_bounded R S hHb
  have hFlp (i j : Fin n) : MemLp (fun x => F x i j) 2 (potentialMeasure φ) :=
    MemLp.of_bound (hFc i j).continuous.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hC x i j)
  have hγ0 (x : CoordinateSpace n) (i j : Fin n) :
      0 ≤ diffusionGamma (inverseHessian φ) (fun y => F y i j) (fun y => F y i j) x :=
    diffusionGamma_nonneg _ x (hH x).posSemidef.inv
  have hγi (i j : Fin n) : Integrable
      (diffusionGamma (inverseHessian φ) (fun x => F x i j) (fun x => F x i j)) (potentialMeasure φ) := by
    apply hEi.mono' (smooth_inverseHessian_energy hφ (hFc i j) hdet).continuous.aestronglyMeasurable
    filter_upwards with x
    rw [Real.norm_of_nonneg (hγ0 x i j)]
    exact le_double_sum_of_nonneg (hγ0 x) i j
  have hBL (i j : Fin n) : variance (fun x => F x i j) (potentialMeasure φ) ≤
      ∫ x, diffusionGamma (inverseHessian φ) (fun x => F x i j) (fun x => F x i j) x ∂potentialMeasure φ :=
    GaussianTilt.FunctionalBrascampLieb.variance_le_inverseHessian_energy hφ (hFc i j) hH
      ⟨C, fun x => hC x i j⟩ (hγi i j)
  have hsum : (∑ i, ∑ j, variance (fun x => F x i j) (potentialMeasure φ)) ≤
      ∫ x, hessianSandwichEnergy R φ x ∂potentialMeasure φ := by
    calc
      _ ≤ ∑ i, ∑ j, ∫ x, diffusionGamma (inverseHessian φ) (fun x => F x i j) (fun x => F x i j) x ∂potentialMeasure φ :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hBL i j))
      _ = _ := by
        unfold hessianSandwichEnergy
        rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hγi i j))]
        simp_rw [integral_finset_sum _ (fun j _ => hγi _ j)]
  rw [sum_variance_matrix_entries hFlp,
    matrixExpectation_hessian_conjugate hφ Rg S hgb hHb hiso R] at hsum
  exact hsum

end GaussianTilt.Letwin
