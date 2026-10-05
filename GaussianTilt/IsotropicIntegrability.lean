import GaussianTilt.Whitening

/-! # Finite moments forced by the independent isotropy definition

The covariance in the reference specification uses total Bochner integrals.
Its diagonal being one itself forces square integrability, so no hidden
integrability premise is required when passing to noncompact isotropic laws.
-/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
set_option linter.unusedSectionVars false

namespace GaussianTilt.Reference

variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

theorem isotropic_coordinate_sq_integrable (hi : isotropic μ) (i : Fin n) :
    Integrable (fun x : Space n ↦ (x i) ^ 2) μ := by
  by_contra h
  have hz : (∫ x : Space n, x i * x i ∂μ) = 0 := by
    simpa only [pow_two] using integral_undef h
  have hc := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ ↦ A i i) hi.2
  simp only [covariance, Matrix.one_apply_eq, hz] at hc
  nlinarith [sq_nonneg (∫ x : Space n, x i ∂μ)]

theorem isotropic_coordinate_memLp (hi : isotropic μ) (i : Fin n) :
    MemLp (fun x : Space n ↦ x i) 2 μ :=
  (memLp_two_iff_integrable_sq
    (PiLp.continuous_apply 2 (fun _ : Fin n ↦ ℝ) i).aestronglyMeasurable).mpr (isotropic_coordinate_sq_integrable hi i)

theorem isotropic_integrable_id (hi : isotropic μ) :
    Integrable (fun x : Space n ↦ x) μ :=
  Whitening.integrable_id_of_coordinates
    (fun i ↦ (isotropic_coordinate_memLp hi i).integrable (by norm_num))

theorem isotropic_coordinate_integral (hi : isotropic μ) (i : Fin n) :
    (∫ x : Space n, x i ∂μ) = 0 := by
  have hm := congrArg (fun x : Space n ↦ x i) hi.1
  change (∫ x : Space n, x ∂μ) i = 0 at hm
  exact ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n ↦ ℝ) i).integral_comp_comm
    (isotropic_integrable_id hi)).trans hm

theorem isotropic_norm_sq_integrable (hi : isotropic μ) :
    Integrable (fun x : Space n ↦ ‖x‖ ^ 2) μ := by
  have heq (x : Space n) : ‖x‖ ^ 2 = ∑ i : Fin n, (x i) ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using EuclideanSpace.norm_sq_eq x
  simp_rw [heq]
  exact integrable_finset_sum _ (fun i _ ↦ isotropic_coordinate_sq_integrable hi i)

theorem isotropic_norm_sq_integral (hi : isotropic μ) :
    (∫ x : Space n, ‖x‖ ^ 2 ∂μ) = n := by
  have hs (i : Fin n) : (∫ x : Space n, (x i) ^ 2 ∂μ) = 1 := by
    have hc := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ ↦ A i i) hi.2
    simpa only [covariance, Matrix.one_apply_eq, isotropic_coordinate_integral hi,
      zero_mul, sub_zero, pow_two] using hc
  have heq (x : Space n) : ‖x‖ ^ 2 = ∑ i : Fin n, (x i) ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using EuclideanSpace.norm_sq_eq x
  simp_rw [heq]
  rw [integral_finset_sum _ (fun i _ ↦ isotropic_coordinate_sq_integrable hi i)]
  simp [hs]

end GaussianTilt.Reference
