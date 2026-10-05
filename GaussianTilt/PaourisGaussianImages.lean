import GaussianTilt.PaourisGaussianBlocks
import GaussianTilt.GaussianConcentrationMoments

/-!
# Gaussian linear-image laws for Paouris

Scalar laws are identified by their proved exponential moments and uniqueness
of the complex moment-generating function. Vector image laws then follow by
characteristic-function uniqueness, rather than an assumed rotation rule.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators InnerProductSpace

namespace GaussianTilt.Paouris

variable {n m q : ℕ}

lemma standardGaussian_inner_integrableExpSet (a : Reference.Space n) :
    integrableExpSet (fun x ↦ ⟪a, x⟫_ℝ) (standardGaussian n) = univ := by
  ext s
  simp only [integrableExpSet, mem_setOf_eq, mem_univ, iff_true]
  simpa only [real_inner_smul_left] using standardGaussian_exp_inner_integrable (s • a)

/-- Equal Euclidean coefficient norms give equal scalar Gaussian image laws,
even when the ambient dimensions are different. -/
theorem standardGaussian_inner_map_eq (a : Reference.Space n) (b : Reference.Space m)
    (hab : ‖a‖ = ‖b‖) :
    (standardGaussian n).map (fun x ↦ ⟪a, x⟫_ℝ) =
      (standardGaussian m).map (fun y ↦ ⟪b, y⟫_ℝ) := by
  have hmgf : mgf (fun x ↦ ⟪a, x⟫_ℝ) (standardGaussian n) =
      mgf (fun y ↦ ⟪b, y⟫_ℝ) (standardGaussian m) := by
    funext s
    have ha := standardGaussian_integral_exp_inner (s • a)
    have hb := standardGaussian_integral_exp_inner (s • b)
    simp only [real_inner_smul_left, norm_smul, hab] at ha hb
    exact ha.trans hb.symm
  have hcomplex := eqOn_complexMGF_of_mgf hmgf
  apply Measure.ext_of_complexMGF_eq (by fun_prop) (by fun_prop)
  funext z
  apply hcomplex
  simp only [standardGaussian_inner_integrableExpSet, interior_univ, mem_univ, mem_setOf_eq]

lemma integral_standardGaussian_inner_eq (a : Reference.Space n) (b : Reference.Space m)
    (hab : ‖a‖ = ‖b‖) {g : ℝ → ℝ} (hg : Continuous g) :
    (∫ x, g ⟪a, x⟫_ℝ ∂standardGaussian n) =
      ∫ y, g ⟪b, y⟫_ℝ ∂standardGaussian m := by
  calc
    _ = ∫ t, g t ∂(standardGaussian n).map (fun x ↦ ⟪a, x⟫_ℝ) :=
      (integral_map (by fun_prop) hg.aestronglyMeasurable).symm
    _ = ∫ t, g t ∂(standardGaussian m).map (fun y ↦ ⟪b, y⟫_ℝ) := by
      rw [standardGaussian_inner_map_eq a b hab]
    _ = _ := integral_map (by fun_prop) hg.aestronglyMeasurable

lemma scalarGaussian_norm_eq_abs_coordinate (x : Reference.Space 1) : ‖x‖ = |x 0| := by
  have heq : x = EuclideanSpace.single (0 : Fin 1) (x 0) := by
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp
  calc
    ‖x‖ = ‖EuclideanSpace.single (0 : Fin 1) (x 0)‖ := congrArg norm heq
    _ = |x 0| := by rw [EuclideanSpace.norm_single, Real.norm_eq_abs]

/-- Exact scalar Gaussian moment identity in every direction. -/
theorem standardGaussian_inner_abs_moment (a : Reference.Space n) {p : ℝ} (hp : 0 ≤ p) :
    (∫ x, |⟪a, x⟫_ℝ| ^ p ∂standardGaussian n) =
      ‖a‖ ^ p * ∫ t : Reference.Space 1, ‖t‖ ^ p ∂standardGaussian 1 := by
  let b : Reference.Space 1 := EuclideanSpace.single 0 ‖a‖
  have hnorm : ‖a‖ = ‖b‖ := by simp [b]
  have h := integral_standardGaussian_inner_eq a b hnorm
    ((Real.continuous_rpow_const hp).comp continuous_abs)
  dsimp only [Function.comp_apply] at h
  rw [h, ← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  simp only [b, EuclideanSpace.inner_single_left, RCLike.conj_to_real,
    abs_mul, abs_norm, ← scalarGaussian_norm_eq_abs_coordinate,
    Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]

/-- Transpose action of the actual Gaussian matrix coordinate block. -/
def gaussianMatrixTransposeAction (W : Reference.Space (n * q)) (x : Reference.Space n) :
    Reference.Space q :=
  WithLp.toLp 2 (fun j ↦ ∑ i : Fin n, W (finProdFinEquiv (i, j)) * x i)

lemma gaussianMatrixTransposeAction_continuous (x : Reference.Space n) :
    Continuous (fun W : Reference.Space (n * q) ↦ gaussianMatrixTransposeAction W x) := by
  unfold gaussianMatrixTransposeAction
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro j
  fun_prop

lemma tensorVector_inner_transposeAction (x : Reference.Space n) (t : Reference.Space q)
    (W : Reference.Space (n * q)) :
    ⟪tensorVector x t, W⟫_ℝ = ⟪t, gaussianMatrixTransposeAction W x⟫_ℝ := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, RCLike.conj_to_real]
  rw [← Equiv.sum_comp finProdFinEquiv]
  simp only [Fintype.sum_prod_type, tensorVector_apply, gaussianMatrixTransposeAction,
    PiLp.toLp_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma tensorVector_norm (x : Reference.Space n) (t : Reference.Space q) :
    ‖tensorVector x t‖ = ‖x‖ * ‖t‖ := by
  have h := tensorVector_norm_sq x t
  nlinarith [norm_nonneg (tensorVector x t), mul_nonneg (norm_nonneg x) (norm_nonneg t)]

/-- The exact law of a Gaussian matrix applied to a fixed vector. In
particular, `Γᵀx` is `‖x‖` times a standard `q`-dimensional Gaussian. -/
theorem standardGaussian_transposeAction_map (x : Reference.Space n) :
    (standardGaussian (n * q)).map (fun W ↦ gaussianMatrixTransposeAction W x) =
      (standardGaussian q).map (fun t : Reference.Space q ↦ ‖x‖ • t) := by
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_eq_charFun_map_one, charFunDual_eq_charFun_map_one]
  congr 1
  rw [Measure.map_map L.measurable (gaussianMatrixTransposeAction_continuous x).measurable,
    Measure.map_map L.measurable (by fun_prop)]
  let u : Reference.Space q := (InnerProductSpace.toDual ℝ (Reference.Space q)).symm L
  have hLu (t : Reference.Space q) : L t = ⟪u, t⟫_ℝ :=
    InnerProductSpace.toDual_symm_apply.symm
  have hleft : (L ∘ (fun W ↦ gaussianMatrixTransposeAction W x)) =
      (fun W ↦ ⟪tensorVector x u, W⟫_ℝ) := by
    funext W
    rw [Function.comp_apply, hLu, tensorVector_inner_transposeAction]
  have hright : (L ∘ (fun t : Reference.Space q ↦ ‖x‖ • t)) =
      (fun t ↦ ⟪‖x‖ • u, t⟫_ℝ) := by
    funext t
    rw [Function.comp_apply, hLu, real_inner_smul_left, real_inner_smul_right]
  rw [hleft, hright]
  apply standardGaussian_inner_map_eq
  rw [tensorVector_norm, norm_smul, Real.norm_eq_abs, abs_norm]

/-- The vector-law identity as an equality of actual expectations. -/
theorem integral_standardGaussian_transposeAction (x : Reference.Space n)
    {g : Reference.Space q → ℝ} (hg : Continuous g) :
    (∫ W : Reference.Space (n * q), g (gaussianMatrixTransposeAction W x) ∂standardGaussian (n * q)) =
      ∫ t : Reference.Space q, g (‖x‖ • t) ∂standardGaussian q := by
  rw [← integral_map (gaussianMatrixTransposeAction_continuous x).measurable.aemeasurable hg.aestronglyMeasurable,
    standardGaussian_transposeAction_map,
    integral_map (by fun_prop) hg.aestronglyMeasurable]

/-- Exact first moment of `Γᵀx`, not just an upper estimate. -/
theorem standardGaussian_transposeAction_norm_integral (x : Reference.Space n) :
    (∫ W : Reference.Space (n * q), ‖gaussianMatrixTransposeAction W x‖ ∂standardGaussian (n * q)) =
      ‖x‖ * ∫ t : Reference.Space q, ‖t‖ ∂standardGaussian q := by
  rw [integral_standardGaussian_transposeAction x continuous_norm]
  simp_rw [norm_smul, Real.norm_eq_abs, abs_norm]
  exact integral_const_mul _ _

/-- Exact positive moments of a fixed Gaussian matrix image. -/
theorem standardGaussian_transposeAction_norm_moment (x : Reference.Space n)
    {p : ℝ} (hp : 0 ≤ p) :
    (∫ W : Reference.Space (n * q), ‖gaussianMatrixTransposeAction W x‖ ^ p ∂standardGaussian (n * q)) =
      ‖x‖ ^ p * ∫ t : Reference.Space q, ‖t‖ ^ p ∂standardGaussian q := by
  have hg : Continuous (fun y : Reference.Space q ↦ ‖y‖ ^ p) :=
    (Real.continuous_rpow_const hp).comp continuous_norm
  rw [integral_standardGaussian_transposeAction x hg]
  simp_rw [norm_smul, Real.norm_eq_abs, abs_norm, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  exact integral_const_mul _ _

def gaussianMatrixLinearMap (W : Reference.Space (n * q)) : Reference.Space q →ₗ[ℝ] Reference.Space n where
  toFun := gaussianMatrixAction W
  map_add' t s := by
    ext i
    simp [gaussianMatrixAction, Finset.sum_add_distrib, mul_add]
  map_smul' c t := by
    ext i
    simp only [gaussianMatrixAction, PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

def gaussianMatrixCLM (W : Reference.Space (n * q)) : Reference.Space q →L[ℝ] Reference.Space n :=
  LinearMap.toContinuousLinearMap (gaussianMatrixLinearMap W)

def gaussianMatrixTransposeLinearMap (W : Reference.Space (n * q)) : Reference.Space n →ₗ[ℝ] Reference.Space q where
  toFun := gaussianMatrixTransposeAction W
  map_add' x y := by
    ext j
    simp [gaussianMatrixTransposeAction, Finset.sum_add_distrib, mul_add]
  map_smul' c x := by
    ext j
    simp only [gaussianMatrixTransposeAction, PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

def gaussianMatrixTransposeCLM (W : Reference.Space (n * q)) : Reference.Space n →L[ℝ] Reference.Space q :=
  LinearMap.toContinuousLinearMap (gaussianMatrixTransposeLinearMap W)

@[simp] lemma gaussianMatrixCLM_apply (W : Reference.Space (n * q)) (t : Reference.Space q) :
    gaussianMatrixCLM W t = gaussianMatrixAction W t := rfl

@[simp] lemma gaussianMatrixTransposeCLM_apply (W : Reference.Space (n * q)) (x : Reference.Space n) :
    gaussianMatrixTransposeCLM W x = gaussianMatrixTransposeAction W x := rfl

lemma gaussianMatrix_inner_adjoint (W : Reference.Space (n * q))
    (t : Reference.Space q) (x : Reference.Space n) :
    ⟪gaussianMatrixAction W t, x⟫_ℝ = ⟪t, gaussianMatrixTransposeAction W x⟫_ℝ := by
  rw [real_inner_comm, ← tensorVector_inner_matrixAction, tensorVector_inner_transposeAction]

lemma gaussianMatrixTransposeAction_joint_continuous :
    Continuous (fun z : Reference.Space (n * q) × Reference.Space n ↦
      gaussianMatrixTransposeAction z.1 z.2) := by
  unfold gaussianMatrixTransposeAction
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro j
  fun_prop

lemma gaussianMatrixTransposeAction_norm_le (W : Reference.Space (n * q)) (x : Reference.Space n) :
    ‖gaussianMatrixTransposeAction W x‖ ≤ ‖W‖ * ‖x‖ := by
  let y := gaussianMatrixTransposeAction W x
  have h := real_inner_le_norm (tensorVector x y) W
  rw [tensorVector_inner_transposeAction, tensorVector_norm] at h
  change ⟪y, y⟫_ℝ ≤ (‖x‖ * ‖y‖) * ‖W‖ at h
  rw [real_inner_self_eq_norm_sq] at h
  have hy : 0 ≤ ‖y‖ := norm_nonneg _
  change ‖y‖ ≤ ‖W‖ * ‖x‖
  by_cases hh : ‖y‖ = 0
  · rw [hh]
    positivity
  · have hpos : 0 < ‖y‖ := lt_of_le_of_ne hy (Ne.symm hh)
    nlinarith

lemma gaussianMatrixAction_norm_le (W : Reference.Space (n * q)) (t : Reference.Space q) :
    ‖gaussianMatrixAction W t‖ ≤ ‖W‖ * ‖t‖ := by
  let y := gaussianMatrixAction W t
  have h := real_inner_le_norm (tensorVector y t) W
  rw [tensorVector_inner_matrixAction, tensorVector_norm] at h
  change ⟪y, y⟫_ℝ ≤ (‖y‖ * ‖t‖) * ‖W‖ at h
  rw [real_inner_self_eq_norm_sq] at h
  have hy : 0 ≤ ‖y‖ := norm_nonneg _
  change ‖y‖ ≤ ‖W‖ * ‖t‖
  by_cases hh : ‖y‖ = 0
  · rw [hh]
    positivity
  · have hpos : 0 < ‖y‖ := lt_of_le_of_ne hy (Ne.symm hh)
    nlinarith

end GaussianTilt.Paouris
