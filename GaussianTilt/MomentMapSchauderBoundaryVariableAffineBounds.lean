import GaussianTilt.MomentMapSchauderBoundaryVariableAffine
import GaussianTilt.MomentMapSchauderFiniteSums

/-! # Quantitative Hölder transport under the actual boundary normalization -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option maxHeartbeats 2200000
open Matrix Set
open scoped ContDiff BigOperators
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma euclideanEquivMatrix_entry (P : KernelSpace n ≃L[ℝ] KernelSpace n) (i k : Fin n) :
    euclideanEquivMatrix P i k=(P (EuclideanSpace.basisFun (Fin n) ℝ k)) i := by
  have hh := toEuclideanCLM_basis_apply (euclideanEquivMatrix P) k i
  have he : Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (euclideanEquivMatrix P)=P.toContinuousLinearMap :=
    StarAlgEquiv.apply_symm_apply _ _
  rw [he] at hh
  exact hh.symm

lemma abs_euclideanEquivMatrix_entry_le (P : KernelSpace n ≃L[ℝ] KernelSpace n) (i k : Fin n) :
    |euclideanEquivMatrix P i k| ≤ ‖P.toContinuousLinearMap‖ := by
  rw [euclideanEquivMatrix_entry]
  apply (PiLp.norm_apply_le (P (EuclideanSpace.basisFun (Fin n) ℝ k)) i).trans
  simpa only [(EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.norm_eq_one,mul_one] using
    P.toContinuousLinearMap.le_opNorm (EuclideanSpace.basisFun (Fin n) ℝ k)

/-- The actual transformed coefficients have a uniform entrywise Hölder
modulus controlled by the map/inverse norms and the original modulus. -/
theorem boundaryPullbackCoefficient_holder
    (P : KernelSpace n ≃L[ℝ] KernelSpace n) (A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ)
    {S T : Set (KernelSpace n)} (hmap : MapsTo P S T)
    {α K M I : ℝ} (hα : 0 ≤ α) (hK : 0 ≤ K) (hM : 0 ≤ M) (hI : 0 ≤ I)
    (hP : ‖P.toContinuousLinearMap‖ ≤ M) (hPi : ‖P.symm.toContinuousLinearMap‖ ≤ I)
    (hA : ∀ x ∈ T, ∀ y ∈ T, ∀ i k, |A x i k-A y i k| ≤ K*‖x-y‖^α) :
    ∀ x ∈ S, ∀ y ∈ S, ∀ i k,
      |boundaryPullbackCoefficient P A x i k-boundaryPullbackCoefficient P A y i k| ≤
        ((n:ℝ)^2*I^2*K*M^α)*‖x-y‖^α := by
  intro x hx y hy i k
  let N := euclideanEquivMatrix P.symm
  have hN : ∀ a b, |N a b| ≤ I := fun a b => (abs_euclideanEquivMatrix_entry_le P.symm a b).trans hPi
  have hnorm : ‖P x-P y‖ ≤ M*‖x-y‖ := by
    rw [← map_sub]
    exact (P.toContinuousLinearMap.le_opNorm _).trans (mul_le_mul_of_nonneg_right hP (norm_nonneg _))
  have hAH : ∀ a b, |A (P x) a b-A (P y) a b| ≤ (K*M^α)*‖x-y‖^α := by
    intro a b
    have hh := (hA (P x) (hmap hx) (P y) (hmap hy) a b).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hnorm hα) hK)
    rw [Real.mul_rpow hM (norm_nonneg _)] at hh
    exact hh.trans_eq (by ring)
  have hd : boundaryPullbackCoefficient P A x-boundaryPullbackCoefficient P A y=N*(A (P x)-A (P y))*Nᵀ := by
    dsimp [boundaryPullbackCoefficient,N]
    rw [Matrix.mul_sub,Matrix.sub_mul]
  change |(boundaryPullbackCoefficient P A x-boundaryPullbackCoefficient P A y) i k| ≤ _
  rw [hd]
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.sub_apply,Finset.sum_mul]
  have hterm (a b : Fin n) : |N i a*(A (P x) a b-A (P y) a b)*N k b| ≤ I^2*(K*M^α)*‖x-y‖^α := by
    rw [abs_mul,abs_mul]
    exact (mul_le_mul (mul_le_mul (hN i a) (hAH a b) (abs_nonneg _) hI) (hN k b)
      (abs_nonneg _) (by positivity)).trans_eq (by ring)
  exact (abs_finset_sum_bound (fun b => abs_finset_sum_bound (fun a => hterm a b))).trans_eq
    (by simp only [Fintype.card_fin]; ring)

/-- Exact Hölder transport for the covariant Hessian field. -/
theorem boundaryPullbackHessian_holder
    (P : KernelSpace n ≃L[ℝ] KernelSpace n)
    (B : KernelSpace n → KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ)
    {S T : Set (KernelSpace n)} (hmap : MapsTo P S T) {α H M : ℝ}
    (hα : 0 ≤ α) (hH : 0 ≤ H) (hM : 0 ≤ M) (hP : ‖P.toContinuousLinearMap‖ ≤ M)
    (hB : ∀ x ∈ T, ∀ y ∈ T, ‖B x-B y‖ ≤ H*‖x-y‖^α) :
    ∀ x ∈ S, ∀ y ∈ S,
      ‖(B (P x)).bilinearComp P.toContinuousLinearMap P.toContinuousLinearMap-
        (B (P y)).bilinearComp P.toContinuousLinearMap P.toContinuousLinearMap‖ ≤
        (M^2*H*M^α)*‖x-y‖^α := by
  intro x hx y hy
  rw [← bilinearComp_sub]
  have hnorm : ‖P x-P y‖ ≤ M*‖x-y‖ := by
    rw [← map_sub]
    exact (P.toContinuousLinearMap.le_opNorm _).trans (mul_le_mul_of_nonneg_right hP (norm_nonneg _))
  have hh := (hB _ (hmap hx) _ (hmap hy)).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hnorm hα) hH)
  rw [Real.mul_rpow hM (norm_nonneg _)] at hh
  have hP2 : ‖P.toContinuousLinearMap‖^2 ≤ M^2 := sq_le_sq₀ (norm_nonneg _) hM |>.mpr hP
  exact (norm_bilinearComp_same_le _ _).trans ((mul_le_mul hh hP2 (sq_nonneg _) (by positivity)).trans_eq (by ring))

lemma boundaryPullbackHessian_norm_recover (P : KernelSpace n ≃L[ℝ] KernelSpace n)
    (B : KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ) :
    ‖B‖ ≤ ‖B.bilinearComp P.toContinuousLinearMap P.toContinuousLinearMap‖*‖P.symm.toContinuousLinearMap‖^2 := by
  have he : (B.bilinearComp P.toContinuousLinearMap P.toContinuousLinearMap).bilinearComp
      P.symm.toContinuousLinearMap P.symm.toContinuousLinearMap=B := by
    ext v w
    simp only [ContinuousLinearMap.bilinearComp_apply,ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.apply_symm_apply]
  have hh := norm_bilinearComp_same_le (B.bilinearComp P.toContinuousLinearMap P.toContinuousLinearMap) P.symm.toContinuousLinearMap
  rw [he] at hh
  exact hh

end GaussianTilt.MomentMapSchauder
