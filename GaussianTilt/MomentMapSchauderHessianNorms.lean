import GaussianTilt.MomentMapSchauderNewtonianTail
import GaussianTilt.MomentMapEllipticFundamentalSolutionGreen

/-!
# Operator-norm conversion for the actual Euclidean Hessian

Entrywise estimates in the canonical orthonormal basis imply quantitative
operator-norm estimates. The conversion is proved by finite basis expansion,
so it introduces no norm-equivalence or regularity premise.
-/
noncomputable section
open MeasureTheory Set Filter Module
open scoped BigOperators ContDiff
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma euclidean_bilinear_expansion (B : KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ)
    (v w : KernelSpace n) :
    B v w = ∑ i, ∑ j, v i * w j *
      B (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j) := by
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  have hv : (∑ i, v i • e i) = v := by simpa only [EuclideanSpace.basisFun_repr] using e.sum_repr v
  have hw : (∑ j, w j • e j) = w := by simpa only [EuclideanSpace.basisFun_repr] using e.sum_repr w
  calc
    B v w = B (∑ i, v i • e i) (∑ j, w j • e j) := by rw [hv, hw]
    _ = _ := by
      simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- Explicit dimension-squared conversion from literal Hessian entries to
the norm of the bilinear Fréchet derivative. -/
theorem euclidean_bilinear_norm_le_of_entries
    (B : KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hB : ∀ i j, |B (EuclideanSpace.basisFun (Fin n) ℝ i)
      (EuclideanSpace.basisFun (Fin n) ℝ j)| ≤ M) :
    ‖B‖ ≤ (n : ℝ) ^ 2 * M := by
  apply B.opNorm_le_bound (by positivity)
  intro v
  apply (B v).opNorm_le_bound (by positivity)
  intro w
  rw [Real.norm_eq_abs, euclidean_bilinear_expansion]
  calc
    _ ≤ ∑ i, ∑ j, |v i * w j * B (EuclideanSpace.basisFun (Fin n) ℝ i)
        (EuclideanSpace.basisFun (Fin n) ℝ j)| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      exact Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, ‖v‖ * ‖w‖ * M := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      simp only [abs_mul]
      have hv : |v i| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v i
      have hw : |w j| ≤ ‖w‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le w j
      exact mul_le_mul (mul_le_mul hv hw (abs_nonneg _) (norm_nonneg _)) (hB i j)
        (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

lemma directionalHessian_eq_secondFrechet {u : KernelSpace n → ℝ}
    (hu : ContDiff ℝ 2 u) (x v w : KernelSpace n) :
    directionalHessian u x v w = fderiv ℝ (fderiv ℝ u) x w v := by
  have hd := ((hu.fderiv_right (m := 1) (by norm_num)).differentiable le_rfl) x
  unfold directionalHessian
  rw [fderiv_clm_apply hd (differentiableAt_const v)]
  simp

/-- Hölder estimates on the actual Hessian entries upgrade to the norm used
by Taylor interpolation and the interior Schauder seminorm. -/
theorem secondFrechet_holder_of_directionalHessian_entries {u : KernelSpace n → ℝ}
    (hu : ContDiff ℝ 2 u) {S : Set (KernelSpace n)} {C α : ℝ} (hC : 0 ≤ C)
    (hH : ∀ x ∈ S, ∀ y ∈ S, ∀ i j,
      |directionalHessian u x (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j) -
        directionalHessian u y (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)| ≤
          C * ‖x - y‖ ^ α) :
    ∀ x ∈ S, ∀ y ∈ S,
      ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤
        ((n : ℝ) ^ 2 * C) * ‖x - y‖ ^ α := by
  intro x hx y hy
  have hb := euclidean_bilinear_norm_le_of_entries
    (fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y)
    (M := C * ‖x - y‖ ^ α) (by positivity) ?_
  · simpa only [mul_assoc] using hb
  · intro i j
    simpa only [ContinuousLinearMap.sub_apply, directionalHessian_eq_secondFrechet hu] using hH x hx y hy j i

lemma continuous_kernelLaplacian {u : KernelSpace n → ℝ} (hu : ContDiff ℝ 2 u) :
    Continuous (kernelLaplacian u) := by
  apply continuous_finset_sum
  intro i _
  exact continuous_directionalHessian hu _ _

lemma compactSupport_kernelLaplacian {u : KernelSpace n → ℝ} (hs : HasCompactSupport u) :
    HasCompactSupport (kernelLaplacian u) := by
  classical
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  let F : Fin n → KernelSpace n → ℝ := fun i x => directionalHessian u x (e i) (e i)
  have hF (i : Fin n) : HasCompactSupport (F i) :=
    (hs.fderiv_apply (𝕜 := ℝ) (e i)).fderiv_apply (𝕜 := ℝ) (e i)
  have hsum (s : Finset (Fin n)) : HasCompactSupport (∑ i ∈ s, F i) := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using (HasCompactSupport.zero : HasCompactSupport (0 : KernelSpace n → ℝ))
    | @insert i s his ih =>
      rw [Finset.sum_insert his]
      exact (hF i).add ih
  simpa only [Finset.sum_fn] using hsum Finset.univ

end GaussianTilt.MomentMapSchauder
