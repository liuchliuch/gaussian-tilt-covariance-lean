import GaussianTilt.PaourisProjection
import GaussianTilt.IsotropicIntegrability

/-! # Isotropic projection laws without compact support

The original definition of isotropy itself forces the required second
moments. These identities therefore introduce no additional integrability
hypothesis into the projection step of the general Paouris theorem.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators InnerProductSpace
namespace GaussianTilt.Paouris
variable {n : ℕ}

lemma isotropic_inner_memLp_general (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hi : Reference.isotropic μ) (a : Reference.Space n) :
    MemLp (fun x ↦ ⟪a, x⟫_ℝ) 2 μ := by
  have h := memLp_finset_sum (s := Finset.univ)
    (fun i _ ↦ (Reference.isotropic_coordinate_memLp hi i).const_mul (a i))
  simpa only [PiLp.inner_apply, RCLike.inner_apply, RCLike.conj_to_real, mul_comm] using h

lemma isotropic_inner_product_integrable_general (μ : Measure (Reference.Space n))
    [IsProbabilityMeasure μ] (hi : Reference.isotropic μ) (a b : Reference.Space n) :
    Integrable (fun x ↦ ⟪a, x⟫_ℝ * ⟪b, x⟫_ℝ) μ :=
  (isotropic_inner_memLp_general μ hi a).integrable_mul (isotropic_inner_memLp_general μ hi b)

lemma inner_product_coordinate_expansion (a b x : Reference.Space n) :
    ⟪a, x⟫_ℝ * ⟪b, x⟫_ℝ = ∑ i : Fin n, ∑ j : Fin n, (a i * b j) * (x i * x j) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, RCLike.conj_to_real]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Every pair of linear observables has exactly its Euclidean covariance,
with all integrability proved from the independent isotropy specification. -/
theorem isotropic_inner_product_integral_general (μ : Measure (Reference.Space n))
    [IsProbabilityMeasure μ] (hi : Reference.isotropic μ) (a b : Reference.Space n) :
    (∫ x, ⟪a, x⟫_ℝ * ⟪b, x⟫_ℝ ∂μ) = ⟪a, b⟫_ℝ := by
  have hprod (i j : Fin n) : (∫ x : Reference.Space n, x i * x j ∂μ) =
      if i = j then 1 else 0 := by
    have h := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ ↦ A i j) hi.2
    simpa only [Reference.covariance, Reference.isotropic_coordinate_integral hi,
      zero_mul, sub_zero, Matrix.one_apply] using h
  have hf (i j : Fin n) : Integrable (fun x : Reference.Space n ↦ (a i * b j) * (x i * x j)) μ :=
    ((Reference.isotropic_coordinate_memLp hi i).integrable_mul
      (Reference.isotropic_coordinate_memLp hi j)).const_mul _
  simp_rw [inner_product_coordinate_expansion]
  rw [integral_finset_sum _ (fun i _ ↦ integrable_finset_sum _ (fun j _ ↦ hf i j))]
  simp_rw [integral_finset_sum _ (fun j _ ↦ hf _ j), integral_const_mul, hprod]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [PiLp.inner_apply, RCLike.inner_apply, RCLike.conj_to_real, mul_comm]

lemma isotropic_inner_integral_general (μ : Measure (Reference.Space n))
    [IsProbabilityMeasure μ] (hi : Reference.isotropic μ) (a : Reference.Space n) :
    (∫ x, ⟪a, x⟫_ℝ ∂μ) = 0 := by
  rw [integral_inner (Reference.isotropic_integrable_id hi)]
  change ⟪a, Reference.mean μ⟫_ℝ = 0
  rw [hi.1, inner_zero_right]

/-- Projection onto an arbitrary subspace, in orthonormal range coordinates,
preserves isotropy even for noncompact laws. -/
theorem projectionCoordinatesLaw_isotropic_general (μ : Measure (Reference.Space n))
    [IsProbabilityMeasure μ] (hi : Reference.isotropic μ)
    (F : Submodule ℝ (Reference.Space n)) :
    Reference.isotropic (μ.map (projectionCoordinates F)) := by
  let L := projectionCoordinates F
  have hmean : Reference.mean (μ.map L) = 0 := by
    unfold Reference.mean
    rw [integral_map L.measurable.aemeasurable (show AEStronglyMeasurable (fun x ↦ x) _ from
      continuous_id.aestronglyMeasurable), L.integral_comp_comm (Reference.isotropic_integrable_id hi)]
    change L (Reference.mean μ) = 0
    rw [hi.1, map_zero]
  have hm (i : Fin (Module.finrank ℝ F)) : (∫ x, x i ∂μ.map L) = 0 := by
    rw [integral_map L.measurable.aemeasurable
      (PiLp.continuous_apply 2 (fun _ : Fin (Module.finrank ℝ F) ↦ ℝ) i).aestronglyMeasurable]
    simp only [L, projectionCoordinates_apply]
    exact isotropic_inner_integral_general μ hi _
  refine ⟨hmean, ?_⟩
  ext i j
  change Reference.covariance (μ.map L) i j = (1 : Matrix _ _ ℝ) i j
  simp only [Reference.covariance, hm, zero_mul, sub_zero, Matrix.one_apply]
  rw [integral_map L.measurable.aemeasurable (by fun_prop)]
  simp only [L, projectionCoordinates_apply]
  rw [isotropic_inner_product_integral_general μ hi]
  exact (stdOrthonormalBasis ℝ F).inner_eq_ite i j

end GaussianTilt.Paouris
