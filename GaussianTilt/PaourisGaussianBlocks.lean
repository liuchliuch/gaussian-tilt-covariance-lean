import GaussianTilt.PaourisNormGordon

/-!
# Gaussian block marginals

The product and dimension-splitting identities are proved directly from the
normalized densities and Haar uniqueness. They identify the concrete blocks
in Gordon's theorem with the lower-dimensional standard Gaussian laws.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators InnerProductSpace

namespace GaussianTilt.Paouris

variable {n q : ℕ}

def appendVectorEquiv (n q : ℕ) :
    (Reference.Space n × Reference.Space q) ≃L[ℝ] Reference.Space (n + q) where
  toFun z := appendVector z.1 z.2
  invFun w := (vectorLeft w, vectorRight w)
  left_inv z := by
    apply Prod.ext <;> ext i <;> simp [vectorLeft, vectorRight]
  right_inv := appendVector_left_right
  map_add' z w := by
    ext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;> simp
  map_smul' a z := by
    ext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;> simp
  continuous_toFun := appendVector_continuous
  continuous_invFun := vectorLeft_continuous.prodMk vectorRight_continuous

lemma gaussianKernel_append (x : Reference.Space n) (y : Reference.Space q) :
    gaussianKernel (n + q) (appendVector x y) = gaussianKernel n x * gaussianKernel q y := by
  unfold gaussianKernel
  rw [appendVector_norm_sq, ← Real.exp_add]
  congr 1
  ring

/-- Haar-coordinate change for the append map, with a positive scale that
will cancel upon probability normalization. -/
lemma exists_append_haar_factor (n q : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ g : Reference.Space (n + q) → ℝ,
      (∫ z : Reference.Space n × Reference.Space q, g (appendVector z.1 z.2) ∂(volume.prod volume)) =
        c * ∫ w, g w := by
  let e := appendVectorEquiv n q
  let μ : Measure (Reference.Space n × Reference.Space q) := volume.prod volume
  let ν : Measure (Reference.Space (n + q)) := μ.map e
  haveI : ν.IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  have hν := Measure.isAddLeftInvariant_eq_smul ν volume
  let c : ℝ := ν.addHaarScalarFactor volume
  have hi (g : Reference.Space (n + q) → ℝ) :
      (∫ z : Reference.Space n × Reference.Space q, g (appendVector z.1 z.2) ∂μ) = c * ∫ w, g w := by
    have hh := integral_map_equiv e.toHomeomorph.toMeasurableEquiv g (μ := μ)
    change (∫ w, g w ∂ν) = _ at hh
    rw [hν, integral_smul_nnreal_measure] at hh
    simpa only [ENNReal.coe_toReal, smul_eq_mul, e, appendVectorEquiv] using hh.symm
  have hZ := hi (gaussianKernel (n + q))
  simp_rw [gaussianKernel_append] at hZ
  rw [integral_prod_mul] at hZ
  have hc : 0 < c := by
    have hp := mul_pos (gaussianKernel_integral_pos n) (gaussianKernel_integral_pos q)
    rw [hZ] at hp
    exact (mul_pos_iff_of_pos_right (gaussianKernel_integral_pos (n + q))).mp hp
  exact ⟨c, hc, hi⟩

lemma integral_standardGaussian_prod_dims (f : Reference.Space n × Reference.Space q → ℝ) :
    (∫ z, f z ∂((standardGaussian n).prod (standardGaussian q))) =
      (∫ z, f z * (gaussianKernel n z.1 * gaussianKernel q z.2) ∂(volume.prod volume)) /
        ((∫ x, gaussianKernel n x) * ∫ y, gaussianKernel q y) := by
  rw [standardGaussian, standardGaussian, prod_withDensity
    ((standardGaussianDensity_continuous n).measurable.ennreal_ofReal)
    ((standardGaussianDensity_continuous q).measurable.ennreal_ofReal)]
  have hm : Measurable (fun z : Reference.Space n × Reference.Space q ↦
      ENNReal.ofReal (standardGaussianDensity n z.1) *
      ENNReal.ofReal (standardGaussianDensity q z.2)) :=
    ((standardGaussianDensity_continuous n).measurable.comp measurable_fst).ennreal_ofReal.mul
      ((standardGaussianDensity_continuous q).measurable.comp measurable_snd).ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul hm
    (Filter.Eventually.of_forall (fun _ ↦ ENNReal.mul_lt_top
      ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (standardGaussianDensity_pos _).le]
  rw [← integral_div]
  congr 1
  ext z
  simp only [smul_eq_mul, standardGaussianDensity]
  ring

/-- Appending independent standard Gaussian vectors gives the standard
Gaussian law in the sum dimension. -/
theorem integral_standardGaussian_append (f : Reference.Space (n + q) → ℝ) :
    (∫ z : Reference.Space n × Reference.Space q, f (appendVector z.1 z.2)
      ∂((standardGaussian n).prod (standardGaussian q))) =
      ∫ w, f w ∂standardGaussian (n + q) := by
  obtain ⟨c, hc, hhaar⟩ := exists_append_haar_factor n q
  have hZ := hhaar (gaussianKernel (n + q))
  simp_rw [gaussianKernel_append] at hZ
  rw [integral_prod_mul] at hZ
  rw [integral_standardGaussian_prod_dims, integral_standardGaussian]
  have hnum := hhaar (fun w ↦ f w * gaussianKernel (n + q) w)
  simp_rw [gaussianKernel_append] at hnum
  rw [hnum, hZ]
  field_simp

/-- The first coordinate block has its own normalized standard Gaussian law. -/
theorem integral_standardGaussian_vectorLeft (f : Reference.Space n → ℝ) :
    (∫ w : Reference.Space (n + q), f (vectorLeft w) ∂standardGaussian (n + q)) =
      ∫ x, f x ∂standardGaussian n := by
  rw [← integral_standardGaussian_append]
  have heq : (fun z : Reference.Space n × Reference.Space q ↦ f (vectorLeft (appendVector z.1 z.2))) =
      (fun z ↦ f z.1 * (1 : ℝ)) := by
    ext z
    rw [mul_one]
    congr 1
    ext i
    simp [vectorLeft]
  rw [heq, integral_prod_mul f (fun _ : Reference.Space q ↦ (1 : ℝ))]
  simp

/-- The second coordinate block has its own normalized standard Gaussian law. -/
theorem integral_standardGaussian_vectorRight (f : Reference.Space q → ℝ) :
    (∫ w : Reference.Space (n + q), f (vectorRight w) ∂standardGaussian (n + q)) =
      ∫ x, f x ∂standardGaussian q := by
  rw [← integral_standardGaussian_append]
  have heq : (fun z : Reference.Space n × Reference.Space q ↦ f (vectorRight (appendVector z.1 z.2))) =
      (fun z ↦ (1 : ℝ) * f z.2) := by
    ext z
    rw [one_mul]
    congr 1
    ext i
    simp [vectorRight]
  rw [heq, integral_prod_mul (fun _ : Reference.Space n ↦ (1 : ℝ)) f]
  simp

/-- Gordon's minimax theorem in its usual separate-dimensional Gaussian
integral form, including the actual standard Gaussian matrix-entry law. -/
theorem norm_gordon_marginals [NeZero q] (p : AddGroupNorm (Reference.Space n))
    (hp : ∀ (a : ℝ) x, p (a • x) = |a| * p x)
    {L : ℝ≥0} (hbound : ∀ x, p x ≤ (L : ℝ) * ‖x‖) :
    (∫ x, p x ∂standardGaussian n) ≤
      (∫ W : Reference.Space (n * q), ⨅ t : UnitSphere q, p (gaussianMatrixAction W t)
        ∂standardGaussian (n * q)) + (L : ℝ) * ∫ h : Reference.Space q, ‖h‖ ∂standardGaussian q := by
  have h := norm_gordon (q := q) p hp hbound
  change (∫ w, p (vectorLeft (vectorLeft w)) ∂standardGaussian ((n + q) + n * q)) ≤
    (∫ w, (⨅ t : UnitSphere q, p (gaussianMatrixAction (vectorRight w) t))
      ∂standardGaussian ((n + q) + n * q)) +
    (L : ℝ) * ∫ w, ‖vectorRight (vectorLeft w)‖ ∂standardGaussian ((n + q) + n * q) at h
  rw [integral_standardGaussian_vectorLeft (fun z : Reference.Space (n + q) ↦ p (vectorLeft z)),
    integral_standardGaussian_vectorLeft p,
    integral_standardGaussian_vectorRight (fun W : Reference.Space (n * q) ↦
      ⨅ t : UnitSphere q, p (gaussianMatrixAction W t)),
    integral_standardGaussian_vectorLeft (fun z : Reference.Space (n + q) ↦ ‖vectorRight z‖),
    integral_standardGaussian_vectorRight (fun z : Reference.Space q ↦ ‖z‖)] at h
  exact h

lemma coordinateVector_inner_right (x : Reference.Space n) (i : Fin n) :
    ⟪x, coordinateVector i⟫_ℝ = x i := by
  simp [coordinateVector, EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_right]

lemma standardGaussian_coordinate_integrable (i : Fin n) :
    Integrable (fun x : Reference.Space n ↦ x i) (standardGaussian n) := by
  apply (standardGaussian_norm_integrable n).mono'
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n ↦ ℝ) i).continuous.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x ↦ PiLp.norm_apply_le x i

lemma standardGaussian_coordinate_sq_integrable (i : Fin n) :
    Integrable (fun x : Reference.Space n ↦ (x i) ^ 2) (standardGaussian n) := by
  apply (standardGaussian_norm_sq_integrable n).mono'
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n ↦ ℝ) i).continuous.pow 2).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h := pow_le_pow_left₀ (abs_nonneg (x i)) (PiLp.norm_apply_le x i) 2
  simpa only [sq_abs] using h

/-- Standard Gaussian coordinate variance is proved by the actual Stein
identity, not assumed as an isotropy axiom. -/
theorem standardGaussian_coordinate_sq_integral (i : Fin n) :
    (∫ x : Reference.Space n, (x i) ^ 2 ∂standardGaussian n) = 1 := by
  let g : Reference.Space n → ℝ := fun x ↦ x i
  have hg : Differentiable ℝ g := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n ↦ ℝ) i).differentiable
  have hderiv (x : Reference.Space n) : fderiv ℝ g x (coordinateVector i) = 1 := by
    change fderiv ℝ (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n ↦ ℝ) i) x (coordinateVector i) = 1
    rw [ContinuousLinearMap.fderiv]
    simp [PiLp.proj_apply, coordinateVector_apply]
  have hdint : Integrable (fun x ↦ fderiv ℝ g x (coordinateVector i)) (standardGaussian n) := by
    simp_rw [hderiv]
    exact integrable_const _
  have hxg : Integrable (fun x ↦ ⟪x, coordinateVector i⟫_ℝ * g x) (standardGaussian n) := by
    simpa only [coordinateVector_inner_right, g, pow_two] using standardGaussian_coordinate_sq_integrable i
  have h := standardGaussian_integration_by_parts hg (coordinateVector i)
    (standardGaussian_coordinate_integrable i) hdint hxg
  simp only [hderiv, integral_const, measureReal_univ_eq_one, smul_eq_mul, mul_one,
    coordinateVector_inner_right, g] at h
  simpa only [pow_two] using h.symm

/-- Exact second moment of the actual `n`-dimensional Gaussian law. -/
theorem standardGaussian_norm_sq_integral (n : ℕ) :
    (∫ x : Reference.Space n, ‖x‖ ^ 2 ∂standardGaussian n) = n := by
  simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
  rw [integral_finset_sum _ (fun i _ ↦ standardGaussian_coordinate_sq_integrable i)]
  simp only [standardGaussian_coordinate_sq_integral, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- The Gaussian mean-norm bound required by Gordon's norm inequality. -/
theorem standardGaussian_norm_integral_le_sqrt (n : ℕ) :
    (∫ x : Reference.Space n, ‖x‖ ∂standardGaussian n) ≤ Real.sqrt (n : ℝ) := by
  have h := (even_two.convexOn_pow (𝕜 := ℝ)).map_integral_le
    (μ := standardGaussian n) (f := fun x : Reference.Space n ↦ ‖x‖)
    (by fun_prop) isClosed_univ (Filter.Eventually.of_forall fun _ ↦ mem_univ _)
    (standardGaussian_norm_integrable n) (standardGaussian_norm_sq_integrable n)
  rw [standardGaussian_norm_sq_integral] at h
  exact (Real.le_sqrt (integral_nonneg (fun x ↦ norm_nonneg x)) (Nat.cast_nonneg n)).mpr h

/-- Gordon's norm bound with the universal `sqrt q` error term, exactly the
minimax form needed by the Paouris short proof. -/
theorem norm_gordon_sqrt [NeZero q] (p : AddGroupNorm (Reference.Space n))
    (hp : ∀ (a : ℝ) x, p (a • x) = |a| * p x)
    {L : ℝ≥0} (hbound : ∀ x, p x ≤ (L : ℝ) * ‖x‖) :
    (∫ x, p x ∂standardGaussian n) ≤
      (∫ W : Reference.Space (n * q), ⨅ t : UnitSphere q, p (gaussianMatrixAction W t)
        ∂standardGaussian (n * q)) + (L : ℝ) * Real.sqrt (q : ℝ) := by
  exact (norm_gordon_marginals (q := q) p hp hbound).trans
    (add_le_add_left (mul_le_mul_of_nonneg_left (standardGaussian_norm_integral_le_sqrt q)
      L.coe_nonneg) _)

end GaussianTilt.Paouris
