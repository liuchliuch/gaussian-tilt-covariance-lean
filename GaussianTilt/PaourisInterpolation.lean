import GaussianTilt.PaourisGaussian

/-!
# Differentiating Gaussian linear-image expectations

The derivative is obtained by genuine dominated differentiation under the
normalized Gaussian integral. Together with the Stein identity, this is the
analytic starting point for Gaussian covariance comparison.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators InnerProductSpace

namespace GaussianTilt.Paouris

variable {n m : ℕ}

local instance : ContinuousENorm ((Reference.Space n →L[ℝ] Reference.Space m) →L[ℝ] ℝ) :=
  @SeminormedAddGroup.toContinuousENorm
    ((Reference.Space n →L[ℝ] Reference.Space m) →L[ℝ] ℝ) inferInstance

/-- Gaussian expectation of a function under a specified linear image. -/
def gaussianExpectation (f : Reference.Space m → ℝ)
    (A : Reference.Space n →L[ℝ] Reference.Space m) : ℝ :=
  ∫ x, f (A x) ∂standardGaussian n

lemma gaussian_linear_image_integrable {f : Reference.Space m → ℝ}
    {K : ℝ≥0} (hf : LipschitzWith K f)
    (A : Reference.Space n →L[ℝ] Reference.Space m) :
    Integrable (fun x ↦ f (A x)) (standardGaussian n) := by
  apply (((standardGaussian_norm_integrable n).const_mul ((K : ℝ) * ‖A‖)).add
    (integrable_const ‖f 0‖)).mono' (hf.continuous.comp A.continuous).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  have h₁ := hf.norm_sub_le (A x) 0
  rw [sub_zero] at h₁
  have h₂ := A.le_opNorm x
  have h₃ := norm_le_norm_sub_add (f (A x)) (f 0)
  have h₄ := mul_le_mul_of_nonneg_left h₂ K.coe_nonneg
  dsimp only [Pi.add_apply, Function.comp_apply]
  nlinarith

/-- The derivative integrand as a continuous linear functional on the space
of matrices (continuous linear maps). -/
def gaussianExpectationDerivativeIntegrand (f : Reference.Space m → ℝ)
    (A : Reference.Space n →L[ℝ] Reference.Space m) (x : Reference.Space n) :
    (Reference.Space n →L[ℝ] Reference.Space m) →L[ℝ] ℝ :=
  (fderiv ℝ f (A x)).comp (ContinuousLinearMap.apply ℝ (Reference.Space m) x)

/-- Fréchet differentiation under a Gaussian integral for an arbitrary
`C¹` Lipschitz observable. Neither compact support nor boundedness of the
observable is assumed. -/
theorem gaussianExpectation_hasFDerivAt {f : Reference.Space m → ℝ}
    (hf : ContDiff ℝ 1 f) {K : ℝ≥0} (hlip : LipschitzWith K f)
    (A : Reference.Space n →L[ℝ] Reference.Space m) :
    Integrable (gaussianExpectationDerivativeIntegrand f A) (standardGaussian n) ∧
    HasFDerivAt (gaussianExpectation f)
      (∫ x, gaussianExpectationDerivativeIntegrand f A x ∂standardGaussian n) A := by
  apply hasFDerivAt_integral_of_dominated_loc_of_lip' (μ := standardGaussian n)
    (F := fun B x ↦ f (B x)) (F' := gaussianExpectationDerivativeIntegrand f A)
    (bound := fun x ↦ (K : ℝ) * ‖x‖) (ε := 1) (by norm_num)
  · intro B _
    exact (hf.continuous.comp B.continuous).aestronglyMeasurable
  · exact gaussian_linear_image_integrable hlip A
  · apply Continuous.aestronglyMeasurable
    unfold gaussianExpectationDerivativeIntegrand
    exact ((hf.continuous_fderiv le_rfl).comp A.continuous).clm_comp
      (ContinuousLinearMap.apply ℝ (Reference.Space m)).continuous
  · apply Filter.Eventually.of_forall
    intro x B _
    have h₁ := hlip.norm_sub_le (B x) (A x)
    have h₂ := (B - A).le_opNorm x
    change ‖B x - A x‖ ≤ ‖B - A‖ * ‖x‖ at h₂
    have h₃ := mul_le_mul_of_nonneg_left h₂ K.coe_nonneg
    nlinarith
  · exact (standardGaussian_norm_integrable n).const_mul K
  · apply Filter.Eventually.of_forall
    intro x
    exact ((hf.differentiable le_rfl (A x)).hasFDerivAt).comp A
      (ContinuousLinearMap.apply ℝ (Reference.Space m) x).hasFDerivAt

/-- Evaluation of the genuine matrix derivative under the integral. -/
theorem gaussianExpectation_fderiv_apply {f : Reference.Space m → ℝ}
    (hf : ContDiff ℝ 1 f) {K : ℝ≥0} (hlip : LipschitzWith K f)
    (A B : Reference.Space n →L[ℝ] Reference.Space m) :
    fderiv ℝ (gaussianExpectation f) A B =
      ∫ x, fderiv ℝ f (A x) (B x) ∂standardGaussian n := by
  obtain ⟨hi, hd⟩ := gaussianExpectation_hasFDerivAt hf hlip A
  rw [hd.fderiv, ContinuousLinearMap.integral_apply hi]
  rfl

/-- Directional Gaussian integration by parts for the derivative of a
linear-image observable. -/
theorem gaussian_inner_derivative_eq_hessian {f : Reference.Space m → ℝ}
    (hf : ContDiff ℝ 2 f) {K H : ℝ≥0} (hlip : LipschitzWith K f)
    (hH : ∀ y, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ H)
    (A : Reference.Space n →L[ℝ] Reference.Space m)
    (v : Reference.Space n) (b : Reference.Space m) :
    (∫ x, ⟪x, v⟫_ℝ * fderiv ℝ f (A x) b ∂standardGaussian n) =
      ∫ x, fderiv ℝ (fderiv ℝ f) (A x) (A v) b ∂standardGaussian n := by
  let g : Reference.Space n → ℝ := fun x ↦ fderiv ℝ f (A x) b
  have hdf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hgc : Continuous g :=
    ((hf.continuous_fderiv (by norm_num)).comp A.continuous).clm_apply continuous_const
  have hgd (x : Reference.Space n) : DifferentiableAt ℝ g x :=
    (((hdf.differentiable le_rfl (A x)).hasFDerivAt.comp x A.hasFDerivAt).clm_apply
      (hasFDerivAt_const b x)).differentiableAt
  have hformula (x : Reference.Space n) :
      fderiv ℝ g x v = fderiv ℝ (fderiv ℝ f) (A x) (A v) b := by
    have hd := (((hdf.differentiable le_rfl (A x)).hasFDerivAt.comp x A.hasFDerivAt).clm_apply
      (hasFDerivAt_const b x)).fderiv
    have hh := congrArg (fun L ↦ L v) hd
    simpa only [g, Function.comp_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply, map_zero,
      zero_add, ContinuousLinearMap.flip_apply] using hh
  have hgbound (x : Reference.Space n) : |g x| ≤ (K : ℝ) * ‖b‖ := by
    exact (fderiv ℝ f (A x)).le_opNorm b |>.trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hlip) (norm_nonneg _))
  have hhbound (x : Reference.Space n) :
      |fderiv ℝ (fderiv ℝ f) (A x) (A v) b| ≤ (H : ℝ) * ‖A v‖ * ‖b‖ := by
    exact ((fderiv ℝ (fderiv ℝ f) (A x) (A v)).le_opNorm b).trans
      (mul_le_mul_of_nonneg_right
        (((fderiv ℝ (fderiv ℝ f) (A x)).le_opNorm (A v)).trans
          (mul_le_mul_of_nonneg_right (hH _) (norm_nonneg _))) (norm_nonneg _))
  have hdgi : Integrable (fun x ↦ fderiv ℝ g x v) (standardGaussian n) := by
    simp_rw [hformula]
    apply standardGaussian_integrable_of_bound _ hhbound
    exact (((hdf.continuous_fderiv le_rfl).comp A.continuous).clm_apply
      continuous_const).clm_apply continuous_const
  have h := standardGaussian_integration_by_parts hgd v
    (standardGaussian_integrable_of_bound hgc hgbound) hdgi
    (standardGaussian_inner_mul_integrable_of_bound hgc hgbound v)
  simp_rw [hformula] at h
  exact h.symm

/-- The derivative of a Gaussian linear-image expectation is the exact
Hessian contraction against the infinitesimal covariance change. This is
proved by summing Stein identities in an actual orthonormal basis. -/
theorem gaussianExpectation_fderiv_eq_hessian_contraction {f : Reference.Space m → ℝ}
    (hf : ContDiff ℝ 2 f) {K H : ℝ≥0} (hlip : LipschitzWith K f)
    (hH : ∀ y, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ H)
    (A B : Reference.Space n →L[ℝ] Reference.Space m) :
    fderiv ℝ (gaussianExpectation f) A B =
      ∑ i : Fin n, ∫ x, fderiv ℝ (fderiv ℝ f) (A x)
        (A ((EuclideanSpace.basisFun (Fin n) ℝ) i))
        (B ((EuclideanSpace.basisFun (Fin n) ℝ) i)) ∂standardGaussian n := by
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  have hsum (x : Reference.Space n) :
      fderiv ℝ f (A x) (B x) =
        ∑ i : Fin n, ⟪x, e i⟫_ℝ * fderiv ℝ f (A x) (B (e i)) := by
    calc
      _ = fderiv ℝ f (A x) (B (∑ i, e.repr x i • e i)) := by rw [e.sum_repr]
      _ = _ := by
        simp only [map_sum, map_smul, smul_eq_mul, OrthonormalBasis.repr_apply_apply,
          real_inner_comm]
  have hint (i : Fin n) : Integrable
      (fun x ↦ ⟪x, e i⟫_ℝ * fderiv ℝ f (A x) (B (e i))) (standardGaussian n) := by
    apply standardGaussian_inner_mul_integrable_of_bound
      (((hf.continuous_fderiv (by norm_num)).comp A.continuous).clm_apply continuous_const)
      (C := (K : ℝ) * ‖B (e i)‖) _ (e i)
    intro x
    exact ((fderiv ℝ f (A x)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hlip) (norm_nonneg _))
  rw [gaussianExpectation_fderiv_apply (hf.of_le (by norm_num)) hlip A B]
  simp_rw [hsum]
  rw [integral_finset_sum _ (fun i _ ↦ hint i)]
  apply Finset.sum_congr rfl
  intro i _
  exact gaussian_inner_derivative_eq_hessian hf hlip hH A (e i) (B (e i))

/-- Bounded Hessians have integrable fixed-direction evaluations under every
linear image of the Gaussian law. -/
lemma gaussian_hessian_integrable {f : Reference.Space m → ℝ}
    (hf : ContDiff ℝ 2 f) {H : ℝ≥0}
    (hH : ∀ y, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ H)
    (A : Reference.Space n →L[ℝ] Reference.Space m) (u v : Reference.Space m) :
    Integrable (fun x ↦ fderiv ℝ (fderiv ℝ f) (A x) u v) (standardGaussian n) := by
  have hdf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  apply standardGaussian_integrable_of_bound
    ((((hdf.continuous_fderiv le_rfl).comp A.continuous).clm_apply
      continuous_const).clm_apply continuous_const)
    (C := (H : ℝ) * ‖u‖ * ‖v‖)
  intro x
  exact ((fderiv ℝ (fderiv ℝ f) (A x) u).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right
      (((fderiv ℝ (fderiv ℝ f) (A x)).le_opNorm u).trans
        (mul_le_mul_of_nonneg_right (hH _) (norm_nonneg _))) (norm_nonneg _))

/-- Square-root interpolation of independent blocks of Gaussian columns. -/
def gaussianCovariancePath (A B : Reference.Space n →L[ℝ] Reference.Space m) (t : ℝ) :
    Reference.Space n →L[ℝ] Reference.Space m :=
  Real.sqrt t • A + Real.sqrt (1 - t) • B

lemma gaussianCovariancePath_continuous
    (A B : Reference.Space n →L[ℝ] Reference.Space m) :
    Continuous (gaussianCovariancePath A B) := by
  unfold gaussianCovariancePath
  fun_prop

lemma gaussianCovariancePath_hasDerivAt
    (A B : Reference.Space n →L[ℝ] Reference.Space m)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (gaussianCovariancePath A B)
      ((1 / (2 * Real.sqrt t)) • A + (-1 / (2 * Real.sqrt (1 - t))) • B) t := by
  have ha := (Real.hasDerivAt_sqrt ht.1.ne').smul_const A
  have hb := (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).sqrt
    (show 1 - t ≠ 0 by linarith [ht.2])).smul_const B
  simpa only [zero_sub] using ha.add hb

lemma gaussianCovariancePath_hessian_column
    (A B : Reference.Space n →L[ℝ] Reference.Space m)
    (Q : Reference.Space m →L[ℝ] Reference.Space m →L[ℝ] ℝ)
    (v : Reference.Space n) (hsep : A v = 0 ∨ B v = 0)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    Q (gaussianCovariancePath A B t v)
      (((1 / (2 * Real.sqrt t)) • A + (-1 / (2 * Real.sqrt (1 - t))) • B) v) =
      (1 / 2 : ℝ) * (Q (A v) (A v) - Q (B v) (B v)) := by
  have hs : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht.1).ne'
  have hs' : Real.sqrt (1 - t) ≠ 0 := (Real.sqrt_pos.mpr (by linarith [ht.2])).ne'
  rcases hsep with h | h
  · simp only [gaussianCovariancePath, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, h, smul_zero, zero_add, map_smul,
      ContinuousLinearMap.smul_apply, smul_eq_mul, map_zero, zero_sub]
    field_simp
  · simp only [gaussianCovariancePath, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, h, smul_zero, add_zero, map_smul,
      ContinuousLinearMap.smul_apply, smul_eq_mul, map_zero, sub_zero]
    field_simp

/-- Exact Gaussian covariance interpolation formula for independent column
blocks. The Hessian and all derivatives are the genuine Fréchet derivatives
of the observable. -/
theorem gaussian_covariance_interpolation_hasDerivAt {f : Reference.Space m → ℝ}
    (hf : ContDiff ℝ 2 f) {K H : ℝ≥0} (hlip : LipschitzWith K f)
    (hH : ∀ y, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ H)
    (A B : Reference.Space n →L[ℝ] Reference.Space m)
    (hsep : ∀ i : Fin n, A ((EuclideanSpace.basisFun (Fin n) ℝ) i) = 0 ∨
      B ((EuclideanSpace.basisFun (Fin n) ℝ) i) = 0)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun s ↦ gaussianExpectation f (gaussianCovariancePath A B s))
      ((1 / 2 : ℝ) * ∫ x, ∑ i : Fin n,
        (fderiv ℝ (fderiv ℝ f) (gaussianCovariancePath A B t x)
          (A ((EuclideanSpace.basisFun (Fin n) ℝ) i))
          (A ((EuclideanSpace.basisFun (Fin n) ℝ) i)) -
        fderiv ℝ (fderiv ℝ f) (gaussianCovariancePath A B t x)
          (B ((EuclideanSpace.basisFun (Fin n) ℝ) i))
          (B ((EuclideanSpace.basisFun (Fin n) ℝ) i))) ∂standardGaussian n) t := by
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  let C := gaussianCovariancePath A B t
  let D := (1 / (2 * Real.sqrt t)) • A + (-1 / (2 * Real.sqrt (1 - t))) • B
  have hF := (gaussianExpectation_hasFDerivAt (hf.of_le (by norm_num)) hlip C).2
  have hd := hF.comp_hasDerivAt t (gaussianCovariancePath_hasDerivAt A B ht)
  rw [← hF.fderiv, gaussianExpectation_fderiv_eq_hessian_contraction hf hlip hH] at hd
  have hpoint (x : Reference.Space n) (i : Fin n) :
      fderiv ℝ (fderiv ℝ f) (C x) (C (e i)) (D (e i)) =
        (1 / 2 : ℝ) * (fderiv ℝ (fderiv ℝ f) (C x) (A (e i)) (A (e i)) -
          fderiv ℝ (fderiv ℝ f) (C x) (B (e i)) (B (e i))) :=
    gaussianCovariancePath_hessian_column A B _ _ (hsep i) ht
  have hi (i : Fin n) : Integrable
      (fun x ↦ fderiv ℝ (fderiv ℝ f) (C x) (C (e i)) (D (e i))) (standardGaussian n) :=
    gaussian_hessian_integrable hf hH C _ _
  have heq : (∑ i : Fin n, ∫ x,
      fderiv ℝ (fderiv ℝ f) (C x) (C (e i)) (D (e i)) ∂standardGaussian n) =
      (1 / 2 : ℝ) * ∫ x, ∑ i : Fin n,
        (fderiv ℝ (fderiv ℝ f) (C x) (A (e i)) (A (e i)) -
          fderiv ℝ (fderiv ℝ f) (C x) (B (e i)) (B (e i))) ∂standardGaussian n := by
    rw [← integral_finset_sum _ (fun i _ ↦ hi i)]
    simp_rw [hpoint, ← Finset.mul_sum]
    exact integral_const_mul _ _
  change HasDerivAt _ (∑ i : Fin n, ∫ x,
    fderiv ℝ (fderiv ℝ f) (C x) (C (e i)) (D (e i)) ∂standardGaussian n) t at hd
  rw [heq] at hd
  exact hd

/-- Smooth Gaussian comparison from a deterministic Hessian/covariance sign
condition. This is the proved analytic comparison principle to which the
finite soft-min/max Hessian calculation must be applied for Gordon's theorem. -/
theorem gaussian_smooth_comparison {f : Reference.Space m → ℝ}
    (hf : ContDiff ℝ 2 f) {K H : ℝ≥0} (hlip : LipschitzWith K f)
    (hH : ∀ y, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ H)
    (A B : Reference.Space n →L[ℝ] Reference.Space m)
    (hsep : ∀ i : Fin n, A ((EuclideanSpace.basisFun (Fin n) ℝ) i) = 0 ∨
      B ((EuclideanSpace.basisFun (Fin n) ℝ) i) = 0)
    (hsign : ∀ y, 0 ≤ ∑ i : Fin n,
      (fderiv ℝ (fderiv ℝ f) y (A ((EuclideanSpace.basisFun (Fin n) ℝ) i))
        (A ((EuclideanSpace.basisFun (Fin n) ℝ) i)) -
      fderiv ℝ (fderiv ℝ f) y (B ((EuclideanSpace.basisFun (Fin n) ℝ) i))
        (B ((EuclideanSpace.basisFun (Fin n) ℝ) i)))) :
    gaussianExpectation f B ≤ gaussianExpectation f A := by
  have hFc : Continuous (gaussianExpectation (n := n) f) :=
    continuous_iff_continuousAt.mpr fun C ↦
      (gaussianExpectation_hasFDerivAt (hf.of_le (by norm_num)) hlip C).2.continuousAt
  have hc : Continuous (fun s ↦ gaussianExpectation f (gaussianCovariancePath A B s)) :=
    hFc.comp (gaussianCovariancePath_continuous A B)
  have hm : MonotoneOn (fun s ↦ gaussianExpectation f (gaussianCovariancePath A B s))
      (Icc (0 : ℝ) 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _) hc.continuousOn
      (f' := fun t ↦ (1 / 2 : ℝ) * ∫ x, ∑ i : Fin n,
        (fderiv ℝ (fderiv ℝ f) (gaussianCovariancePath A B t x)
          (A ((EuclideanSpace.basisFun (Fin n) ℝ) i))
          (A ((EuclideanSpace.basisFun (Fin n) ℝ) i)) -
        fderiv ℝ (fderiv ℝ f) (gaussianCovariancePath A B t x)
          (B ((EuclideanSpace.basisFun (Fin n) ℝ) i))
          (B ((EuclideanSpace.basisFun (Fin n) ℝ) i))) ∂standardGaussian n)
    · intro t ht
      rw [interior_Icc] at ht
      exact (gaussian_covariance_interpolation_hasDerivAt hf hlip hH A B hsep ht).hasDerivWithinAt
    · intro t _
      exact mul_nonneg (by norm_num) (integral_nonneg fun x ↦ hsign _)
  have h := hm (by norm_num : (0 : ℝ) ∈ Icc 0 1)
    (by norm_num : (1 : ℝ) ∈ Icc 0 1) (by norm_num : (0 : ℝ) ≤ 1)
  have hzero : gaussianCovariancePath A B 0 = B := by
    ext x i
    simp [gaussianCovariancePath]
  have hone : gaussianCovariancePath A B 1 = A := by
    ext x i
    simp [gaussianCovariancePath]
  change gaussianExpectation f (gaussianCovariancePath A B 0) ≤
    gaussianExpectation f (gaussianCovariancePath A B 1) at h
  rwa [hzero, hone] at h

end GaussianTilt.Paouris
