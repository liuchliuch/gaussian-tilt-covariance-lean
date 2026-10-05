import GaussianTilt.Quadratic

/-! # Actual affine moment transport

Affine changes of a random vector transport its genuine integrals and covariance.
These identities need only finite second moments, and assert no variance bound.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace GaussianTilt.Whitening

variable {ι κ Ω : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ι → ℝ}

lemma memLp_mulVec (hX : ∀ i, MemLp (fun ω ↦ X ω i) 2 μ)
    (A : Matrix κ ι ℝ) (i : κ) : MemLp (fun ω ↦ (A *ᵥ X ω) i) 2 μ :=
  memLp_finset_sum _ fun j _ ↦ (hX j).const_mul (A i j)

lemma memLp_center (hX : ∀ i, MemLp (fun ω ↦ X ω i) 2 μ)
    (m : ι → ℝ) (i : ι) : MemLp (fun ω ↦ (X ω - m) i) 2 μ :=
  (hX i).sub (memLp_const _)

lemma meanVector_mulVec (hX : ∀ i, Integrable (fun ω ↦ X ω i) μ)
    (A : Matrix κ ι ℝ) :
    meanVector μ (fun ω ↦ A *ᵥ X ω) = A *ᵥ meanVector μ X := by
  ext i
  simp only [meanVector, mulVec, dotProduct]
  rw [integral_finset_sum _ (fun j _ ↦ (hX j).const_mul _)]
  simp only [integral_const_mul]

lemma meanVector_center (hX : ∀ i, Integrable (fun ω ↦ X ω i) μ) :
    meanVector μ (fun ω ↦ X ω - meanVector μ X) = 0 := by
  ext i
  simp only [meanVector, Pi.sub_apply, Pi.zero_apply]
  rw [integral_sub (hX i) (integrable_const _)]
  simp

lemma covarianceMatrix_center (hX : ∀ i, MemLp (fun ω ↦ X ω i) 2 μ)
    (m : ι → ℝ) :
    covarianceMatrix μ (fun ω ↦ X ω - m) = covarianceMatrix μ X := by
  ext i j
  simp only [covarianceMatrix, Pi.sub_apply]
  rw [covariance_sub_const_left ((hX i).integrable (by norm_num)),
    covariance_sub_const_right ((hX j).integrable (by norm_num))]

lemma covarianceMatrix_mulVec (hX : ∀ i, MemLp (fun ω ↦ X ω i) 2 μ)
    (A : Matrix κ ι ℝ) :
    covarianceMatrix μ (fun ω ↦ A *ᵥ X ω) = A * covarianceMatrix μ X * A.transpose := by
  ext i j
  change covariance (fun ω ↦ ∑ k, A i k * X ω k)
    (fun ω ↦ ∑ k, A j k * X ω k) μ = _
  have hY : MemLp (fun ω ↦ ∑ k, A j k * X ω k) 2 μ :=
    memLp_finset_sum _ fun k _ ↦ (hX k).const_mul (A j k)
  rw [covariance_fun_sum_left (fun k ↦ (hX k).const_mul (A i k)) hY]
  simp_rw [covariance_fun_sum_right (fun k ↦ (hX k).const_mul _)
    ((hX _).const_mul _), covariance_mul_left, covariance_mul_right]
  simp only [Matrix.mul_apply, transpose_apply, Finset.sum_mul, covarianceMatrix]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  ring

lemma covarianceMatrix_affine (hX : ∀ i, MemLp (fun ω ↦ X ω i) 2 μ)
    (A : Matrix κ ι ℝ) (m : ι → ℝ) :
    covarianceMatrix μ (fun ω ↦ A *ᵥ (X ω - m)) =
      A * covarianceMatrix μ X * A.transpose := by
  rw [covarianceMatrix_mulVec (memLp_center hX m), covarianceMatrix_center hX]

lemma meanVector_whiten (hX : ∀ i, MemLp (fun ω ↦ X ω i) 2 μ)
    (A : Matrix κ ι ℝ) :
    meanVector μ (fun ω ↦ A *ᵥ (X ω - meanVector μ X)) = 0 := by
  rw [meanVector_mulVec (fun i ↦ (memLp_center hX _ i).integrable (by norm_num)),
    meanVector_center (fun i ↦ (hX i).integrable (by norm_num)), mulVec_zero]

end GaussianTilt.Whitening
