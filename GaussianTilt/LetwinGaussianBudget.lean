import GaussianTilt.LetwinGaussianDuality

/-! # Exact vanishing error in the Gaussian-smoothed quadratic dual budget -/
noncomputable section
open MeasureTheory Matrix Set
open scoped BigOperators ContDiff ENNReal
namespace GaussianTilt.Letwin

lemma hsSquare_add_smul_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (s : ℝ) :
    hsSquare (A + s • 1) = hsSquare A + 2*s*Matrix.trace A + s^2*(Fintype.card ι : ℝ) := by
  have hp (i j : ι) : (A + s • 1) i j ^ 2 = A i j ^ 2 + if i=j then 2*s*A i i+s^2 else 0 := by
    by_cases h : i=j
    · subst j
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, if_true]
      ring
    · simp [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, h]
  simp only [hsSquare, hp, Finset.sum_add_distrib, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Finset.mul_sum, Matrix.trace, Matrix.diag_apply]
  ring

set_option maxHeartbeats 600000 in
lemma sum_noisySteinDualConstant_sq_orthogonal {n : ℕ} {φ : CoordinateSpace n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)] (hφ : ContDiff ℝ ∞ φ)
    (S : ℝ) (hHb : ∀ x i j, |coordinateHessian φ x i j| ≤ S)
    (T U : Matrix (Fin n) (Fin n) ℝ) (hU : Uᵀ*U=1) (r c : ℝ) :
    (∑ i, noisySteinDualConstant φ T r (fun j => c*U i j)^2) =
      c^2 * ∫ x, hsSquare (noisySteinMatrix φ T r x) ∂potentialMeasure φ := by
  simp only [noisySteinDualConstant_sq, transpose_mulVec_scaled_row, mul_pow]
  have hi (i : Fin n) : Integrable (fun x => ∑ j, c^2 * (U * noisySteinMatrix φ T r x) i j ^ 2)
      (potentialMeasure φ) := by
    exact (memLp_continuous_hessian_function hφ S hHb
      (F := fun M => ∑ j, c^2 * (U * (T*M*Tᵀ+r^2 • (1 : Matrix (Fin n) (Fin n) ℝ))) i j ^ 2)
      (by simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.add_apply, Matrix.smul_apply]; fun_prop) 1).integrable le_rfl
  rw [← integral_finset_sum _ (fun i _ => hi i), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  change (∑ i, ∑ j, c^2 * (U * noisySteinMatrix φ T r x) i j ^2) = _
  simp_rw [← Finset.mul_sum]
  change c^2 * hsSquare (U * noisySteinMatrix φ T r x) = _
  rw [hsSquare_mul_orthogonal U _ hU]

lemma integral_hessianSandwich_trace {n : ℕ} {φ : CoordinateSpace n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)] (hφ : ContDiff ℝ ∞ φ)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (hgrad : ∀ x, coordinateGradient φ x ∈ K)
    (S : ℝ) (hHb : ∀ x i j, |coordinateHessian φ x i j| ≤ S)
    (hiso : covarianceMatrix (potentialMeasure φ) (coordinateGradient φ)=1)
    (T : Matrix (Fin n) (Fin n) ℝ) :
    (∫ x, Matrix.trace (T * coordinateHessian φ x * T) ∂potentialMeasure φ) = Matrix.trace (T*T) := by
  obtain ⟨Rg,hRg⟩ := hK.exists_bound_of_continuousOn continuous_id.continuousOn
  have hgb : ∀ x i, |coordinateGradient φ x i| ≤ Rg := by
    intro x i
    exact (show |coordinateGradient φ x i| ≤ ‖coordinateGradient φ x‖ by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (coordinateGradient φ x) i).trans (hRg _ (hgrad x))
  have hm := matrixExpectation_hessian_conjugate hφ Rg S hgb hHb hiso T
  have hi (i : Fin n) : Integrable (fun x => (T * coordinateHessian φ x * T) i i) (potentialMeasure φ) :=
    (memLp_continuous_hessian_function hφ S hHb (F := fun M => (T*M*T) i i)
      (by simp only [Matrix.mul_apply]; fun_prop) 1).integrable le_rfl
  simp only [Matrix.trace, Matrix.diag_apply]
  rw [integral_finset_sum _ (fun i _ => hi i)]
  change (∑ i, matrixExpectation (potentialMeasure φ) (fun x => T*coordinateHessian φ x*T) i i) = _
  rw [hm]

set_option maxHeartbeats 1200000 in
/-- Exact quantitative Gaussian error: it tends to zero with the noise
scale, leaving the sharp 8 Tr(B²) budget on the original compact law. -/
theorem regular_noisy_quadratic_dual_budget {n : ℕ} {φ V : CoordinateSpace n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ ∞ φ) (hc : ConvexOn ℝ univ φ)
    (hH : ∀ x, (coordinateHessian φ x).PosDef)
    {K U : Set (CoordinateSpace n)} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hgrad : ∀ x, coordinateGradient φ x ∈ K)
    (hV : ContDiffOn ℝ 2 V U) (hVc : ConvexOn ℝ U V)
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x+V (coordinateGradient φ x))
    (S : ℝ) (hHb : ∀ x i j, |coordinateHessian φ x i j| ≤ S)
    (hiso : covarianceMatrix (potentialMeasure φ) (coordinateGradient φ)=1)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsHermitian) (r : ℝ) :
    (∑ i, noisySteinDualConstant φ (spectralMagnitudeRoot hB) r
      (fun j => 2*spectralSign hB i j)^2) ≤
      8*Matrix.trace (B^2) + 8*r^2*Matrix.trace (spectralAbsolute hB) + 4*r^4*(n : ℝ) := by
  let T := spectralMagnitudeRoot hB
  have hsign : (spectralSign hB)ᵀ*spectralSign hB=1 := by
    rw [(spectralSign_isSymm hB).eq, spectralSign_mul_self]
  rw [sum_noisySteinDualConstant_sq_orthogonal hφ S hHb _ _ hsign]
  have hiq : Integrable (fun x => hsSquare (T*coordinateHessian φ x*T)) (potentialMeasure φ) :=
    (memLp_continuous_hessian_function hφ S hHb (F := fun M => hsSquare (T*M*T))
      (by simp only [hsSquare, Matrix.mul_apply]; fun_prop) 1).integrable le_rfl
  have hit : Integrable (fun x => Matrix.trace (T*coordinateHessian φ x*T)) (potentialMeasure φ) :=
    (memLp_continuous_hessian_function hφ S hHb (F := fun M => Matrix.trace (T*M*T))
      (by simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]; fun_prop) 1).integrable le_rfl
  have htrace := integral_hessianSandwich_trace hφ hK hgrad S hHb hiso T
  rw [spectralMagnitudeRoot_mul_self] at htrace
  have hbase := regular_quadratic_dual_budget hφ hc hH hK hU hKU hgrad hV hVc hMA S hHb hiso hB
  rw [sum_steinDualConstant_sq_orthogonal hφ S hHb _ _ hsign] at hbase
  rw [(spectralMagnitudeRoot_isSymm hB).eq] at hbase
  have heq : (fun x => hsSquare (noisySteinMatrix φ (spectralMagnitudeRoot hB) r x)) =
      (fun x => hsSquare (T*coordinateHessian φ x*T) + 2*r^2*Matrix.trace (T*coordinateHessian φ x*T) + r^4*(n : ℝ)) := by
    funext x
    rw [noisySteinMatrix, (spectralMagnitudeRoot_isSymm hB).eq, hsSquare_add_smul_one]
    simp only [Fintype.card_fin]
    ring
  rw [heq]
  have hsplit := integral_add (hiq.add (hit.const_mul (2*r^2))) (integrable_const (r^4*(n : ℝ)))
  simp only [Pi.add_apply] at hsplit
  rw [hsplit, integral_add hiq (hit.const_mul (2*r^2)), integral_const_mul,
    integral_const, measureReal_univ_eq_one, one_smul, htrace]
  dsimp only [T] at *
  nlinarith

/-- Each actual derivative of the sign quadratic has its corresponding
Gaussian-smoothed H⁻¹ test constant. -/
theorem regular_noisy_quadratic_gradient_dual_bounds {n : ℕ} {φ : CoordinateSpace n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)] (hφ : ContDiff ℝ ∞ φ)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (hgrad : ∀ x, coordinateGradient φ x∈K)
    (S : ℝ) (hHb : ∀ x i j, |coordinateHessian φ x i j| ≤ S)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsHermitian) (r : ℝ) (i : Fin n) :
    CompactNegativeSobolevBound (noisyMomentMeasure φ (spectralMagnitudeRoot hB) r)
      (coordinateDerivative i (matrixQuadratic (spectralSign hB)))
      (noisySteinDualConstant φ (spectralMagnitudeRoot hB) r (fun j => 2*spectralSign hB i j)) := by
  have heq : coordinateDerivative i (matrixQuadratic (spectralSign hB)) =
      (fun z => (fun j => 2*spectralSign hB i j) ⬝ᵥ z) := by
    funext z
    rw [coordinateDerivative_matrixQuadratic _ (spectralSign_isSymm hB)]
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  rw [heq]
  exact noisyMomentMeasure_compactNegativeSobolevBound hφ hK hgrad S hHb _ r _

end GaussianTilt.Letwin
