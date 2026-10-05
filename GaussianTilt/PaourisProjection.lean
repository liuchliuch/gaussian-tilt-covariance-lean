import GaussianTilt.PaourisSymmetrization

/-!
# Compact projected Paouris moments

An orthogonal projection is viewed in its actual range, using an orthonormal
coordinate isometry. The coordinate pushforward is proved isotropic and
logconcave before the Paouris moment theorem is applied.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators InnerProductSpace Matrix.Norms.L2Operator

namespace GaussianTilt.Paouris
variable {n : ℕ}

lemma isotropic_inner_product_integral (μ : Measure (Reference.Space n))
    [IsProbabilityMeasure μ] (hc : Reference.compactlySupported μ)
    (hi : Reference.isotropic μ) (a b : Reference.Space n) :
    (∫ x, ⟪a, x⟫_ℝ * ⟪b, x⟫_ℝ ∂μ) = ⟪a, b⟫_ℝ := by
  have ha := isotropic_inner_sq_integral μ hc hi a
  have hb := isotropic_inner_sq_integral μ hc hi b
  have hab := isotropic_inner_sq_integral μ hc hi (a + b)
  have hI (u v : Reference.Space n) : Integrable (fun x ↦ ⟪u, x⟫_ℝ * ⟪v, x⟫_ℝ) μ :=
    compact_continuous_integrable μ hc (by fun_prop)
  have hexpand : (∫ x, ⟪a + b, x⟫_ℝ ^ 2 ∂μ) =
      (∫ x, ⟪a, x⟫_ℝ ^ 2 ∂μ) + 2 * (∫ x, ⟪a, x⟫_ℝ * ⟪b, x⟫_ℝ ∂μ) +
        (∫ x, ⟪b, x⟫_ℝ ^ 2 ∂μ) := by
    simp_rw [inner_add_left, add_sq, mul_assoc]
    have hsum : Integrable (fun x ↦ ⟪a, x⟫_ℝ ^ 2 + 2 * (⟪a, x⟫_ℝ * ⟪b, x⟫_ℝ)) μ :=
      (compact_continuous_integrable μ hc (by fun_prop)).add ((hI a b).const_mul 2)
    rw [integral_add hsum (compact_continuous_integrable μ hc (by fun_prop)),
      integral_add (compact_continuous_integrable μ hc (by fun_prop)) ((hI a b).const_mul 2),
      integral_const_mul]
  rw [ha, hb, hab, norm_add_sq_real] at hexpand
  linarith

/-- Euclidean coordinates of the orthogonal projection onto `F`. -/
def projectionCoordinates (F : Submodule ℝ (Reference.Space n)) :
    Reference.Space n →L[ℝ] Reference.Space (Module.finrank ℝ F) :=
  (stdOrthonormalBasis ℝ F).repr.toContinuousLinearEquiv.toContinuousLinearMap.comp
    F.orthogonalProjection

lemma projectionCoordinates_apply (F : Submodule ℝ (Reference.Space n)) (x : Reference.Space n)
    (i : Fin (Module.finrank ℝ F)) :
    projectionCoordinates F x i = ⟪((stdOrthonormalBasis ℝ F) i : Reference.Space n), x⟫_ℝ := by
  change (stdOrthonormalBasis ℝ F).repr (F.orthogonalProjection x) i = _
  rw [OrthonormalBasis.repr_apply_apply, Submodule.inner_orthogonalProjection_eq_of_mem_left]

lemma projectionCoordinates_surjective (F : Submodule ℝ (Reference.Space n)) :
    Function.Surjective (projectionCoordinates F) := by
  intro y
  refine ⟨((stdOrthonormalBasis ℝ F).repr.symm y : F), ?_⟩
  change (stdOrthonormalBasis ℝ F).repr (F.orthogonalProjection _) = y
  rw [Submodule.orthogonalProjection_mem_subspace_eq_self, LinearIsometryEquiv.apply_symm_apply]

lemma projectionCoordinates_norm (F : Submodule ℝ (Reference.Space n)) (x : Reference.Space n) :
    ‖projectionCoordinates F x‖ = ‖F.starProjection x‖ := by
  change ‖(stdOrthonormalBasis ℝ F).repr (F.orthogonalProjection x)‖ = _
  rw [LinearIsometryEquiv.norm_map, F.starProjection_apply]
  rfl

lemma projectionCoordinatesLaw_isotropic (μ : Measure (Reference.Space n))
    [IsProbabilityMeasure μ] (hc : Reference.compactlySupported μ)
    (hi : Reference.isotropic μ) (F : Submodule ℝ (Reference.Space n)) :
    Reference.isotropic (μ.map (projectionCoordinates F)) := by
  let L := projectionCoordinates F
  haveI : IsProbabilityMeasure (μ.map L) := Measure.isProbabilityMeasure_map L.measurable.aemeasurable
  have hc' : Reference.compactlySupported (μ.map L) :=
    LogConcaveLinearImages.compactlySupported_map hc L.toLinearMap
  have hmean : Reference.mean (μ.map L) = 0 := by
    unfold Reference.mean
    rw [integral_map L.measurable.aemeasurable (show AEStronglyMeasurable (fun x ↦ x) _ from
      continuous_id.aestronglyMeasurable), L.integral_comp_comm (compact_vector_integrable μ hc)]
    change L (Reference.mean μ) = 0
    rw [hi.1, map_zero]
  have hm (i : Fin (Module.finrank ℝ F)) : (∫ x, x i ∂μ.map L) = 0 := by
    obtain ⟨P, hP⟩ := GaussianTilt.exists_compactProbability_of_compactlySupported (μ.map L) hc'
    have h := P.integral_coordinate_eq_mean i
    rw [hP] at h
    change (∫ x, x i ∂μ.map L) = (Reference.mean (μ.map L)) i at h
    rw [hmean] at h
    exact h
  refine ⟨hmean, ?_⟩
  ext i j
  change Reference.covariance (μ.map L) i j = (1 : Matrix _ _ ℝ) i j
  simp only [Reference.covariance, hm, zero_mul, sub_zero, Matrix.one_apply]
  rw [integral_map L.measurable.aemeasurable (by fun_prop)]
  simp only [L, projectionCoordinates_apply]
  rw [isotropic_inner_product_integral μ hc hi]
  exact (stdOrthonormalBasis ℝ F).inner_eq_ite i j

/-- The compact projected Paouris bound, stated intrinsically on an arbitrary
subspace without an extra full-dimensional-density hypothesis on its ambient law. -/
theorem compact_subspace_moment_le
    (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hc : Reference.compactlySupported μ) (hl : Reference.logconcave μ)
    (hi : Reference.isotropic μ) (F : Submodule ℝ (Reference.Space n))
    {p : ℝ} (hp : 2 ≤ p) :
    (∫ x, ‖F.starProjection x‖ ^ p ∂μ) ^ (1 / p) ≤
      generalCompactPaourisMomentConstant * (Real.sqrt (Module.finrank ℝ F : ℝ) + p) := by
  let L := projectionCoordinates F
  haveI : IsProbabilityMeasure (μ.map L) := Measure.isProbabilityMeasure_map L.measurable.aemeasurable
  have h := compact_isotropic_moment_le (μ.map L)
    (LogConcaveLinearImages.compactlySupported_map hc L.toLinearMap)
    (LogConcaveLinearImages.logconcave_map_surjective hc hl L.toLinearMap
      (projectionCoordinates_surjective F))
    (projectionCoordinatesLaw_isotropic μ hc hi F) hp
  rw [integral_map L.measurable.aemeasurable
    (show AEStronglyMeasurable (fun x : Reference.Space (Module.finrank ℝ F) ↦ ‖x‖ ^ p) _ from
      ((Real.continuous_rpow_const (by linarith : 0 ≤ p)).comp continuous_norm).aestronglyMeasurable)] at h
  simpa only [L, projectionCoordinates_norm] using h

/-- The genuine Euclidean range of a matrix. -/
def matrixRange (P : Matrix (Fin n) (Fin n) ℝ) : Submodule ℝ (Reference.Space n) :=
  LinearMap.range (Matrix.toEuclideanLin P)

lemma matrixRange_finrank (P : Matrix (Fin n) (Fin n) ℝ) :
    Module.finrank ℝ (matrixRange P) = P.rank := by
  symm
  simpa only [matrixRange, Matrix.toEuclideanLin_eq_toLin] using
    P.rank_eq_finrank_range_toLin (PiLp.basisFun 2 ℝ (Fin n)) (PiLp.basisFun 2 ℝ (Fin n))

/-- A Hermitian idempotent matrix is exactly the orthogonal projection onto
its genuine range. -/
lemma matrixRange_starProjection (P : Matrix (Fin n) (Fin n) ℝ)
    (hH : P.IsHermitian) (hP : P * P = P) (x : Reference.Space n) :
    (matrixRange P).starProjection x = Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) P x := by
  let A : Reference.Space n →L[ℝ] Reference.Space n := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) P
  have hAA : A * A = A := by
    dsimp only [A]
    rw [← map_mul, hP]
  have hAAx (y : Reference.Space n) : A (A y) = A y :=
    congrArg (fun T : Reference.Space n →L[ℝ] Reference.Space n ↦ T y) hAA
  have hsym (u v : Reference.Space n) : ⟪A u, v⟫_ℝ = ⟪u, A v⟫_ℝ :=
    (Matrix.isHermitian_iff_isSymmetric.mp hH) u v
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact ⟨x, rfl⟩
  · rintro w ⟨v, rfl⟩
    change ⟪x - A x, A v⟫_ℝ = 0
    rw [← hsym, map_sub, hAAx, sub_self, inner_zero_left]

/-- Actual orthonormal range coordinates for a Hermitian-idempotent matrix,
with exact rank and projection-norm identities. -/
theorem matrix_projection_range_bridge (P : Matrix (Fin n) (Fin n) ℝ)
    (hH : P.IsHermitian) (hP : P * P = P) :
    Module.finrank ℝ (matrixRange P) = P.rank ∧
      Function.Surjective (projectionCoordinates (matrixRange P)) ∧
      ∀ x, ‖projectionCoordinates (matrixRange P) x‖ = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) P x‖ := by
  refine ⟨matrixRange_finrank P, projectionCoordinates_surjective _, ?_⟩
  intro x
  rw [projectionCoordinates_norm, matrixRange_starProjection P hH hP]

/-- The projected Paouris moment estimate for any actual orthogonal matrix
projection of rank `k`, for compact isotropic logconcave laws. -/
theorem compact_projected_moment_le
    (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hc : Reference.compactlySupported μ) (hl : Reference.logconcave μ)
    (hi : Reference.isotropic μ) (P : Matrix (Fin n) (Fin n) ℝ)
    (hH : P.IsHermitian) (hP : P * P = P) {p : ℝ} (hp : 2 ≤ p) :
    (∫ x, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) P x‖ ^ p ∂μ) ^ (1 / p) ≤
      generalCompactPaourisMomentConstant * (Real.sqrt (P.rank : ℝ) + p) := by
  have h := compact_subspace_moment_le μ hc hl hi (matrixRange P) hp
  simpa only [matrixRange_starProjection P hH hP, matrixRange_finrank] using h

/-- Squared-observable form used by the actual Hölder tilt argument. -/
theorem compact_projected_square_moment_le
    (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hc : Reference.compactlySupported μ) (hl : Reference.logconcave μ)
    (hi : Reference.isotropic μ) (P : Matrix (Fin n) (Fin n) ℝ)
    (hH : P.IsHermitian) (hP : P * P = P) {q : ℝ} (hq : 1 ≤ q) :
    (∫ x, (‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) P x‖ ^ 2) ^ q ∂μ) ^ (1 / q) ≤
      (8 * generalCompactPaourisMomentConstant ^ 2) * ((P.rank : ℝ) + q ^ 2) := by
  have hq0 : 0 < q := by linarith
  have hp : 2 ≤ 2 * q := by linarith
  have h := compact_projected_moment_le μ hc hl hi P hH hP hp
  have hI : 0 ≤ ∫ x, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) P x‖ ^ (2 * q) ∂μ :=
    integral_nonneg fun x ↦ by positivity
  have heq : (fun x : Reference.Space n ↦
      (‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) P x‖ ^ 2) ^ q) =
      fun x ↦ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) P x‖ ^ (2 * q) := by
    funext x
    rw [Real.rpow_mul (norm_nonneg _), Real.rpow_two]
  rw [heq]
  have hroot : (∫ x, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) P x‖ ^ (2 * q) ∂μ) ^ (1 / q) =
      ((∫ x, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) P x‖ ^ (2 * q) ∂μ) ^ (1 / (2 * q))) ^ 2 := by
    rw [← Real.rpow_two, ← Real.rpow_mul hI]
    congr 1
    field_simp
  rw [hroot]
  have hsq := pow_le_pow_left₀ (Real.rpow_nonneg hI _) h 2
  have hsqrt := Real.sq_sqrt (Nat.cast_nonneg P.rank)
  have haux : (Real.sqrt (P.rank : ℝ) + 2 * q) ^ 2 ≤ 8 * ((P.rank : ℝ) + q ^ 2) := by
    nlinarith [sq_nonneg (Real.sqrt (P.rank : ℝ) - 2 * q), (show (0 : ℝ) ≤ P.rank from Nat.cast_nonneg P.rank)]
  apply hsq.trans
  rw [mul_pow]
  have hmul := mul_le_mul_of_nonneg_left haux (sq_nonneg generalCompactPaourisMomentConstant)
  nlinarith

end GaussianTilt.Paouris
