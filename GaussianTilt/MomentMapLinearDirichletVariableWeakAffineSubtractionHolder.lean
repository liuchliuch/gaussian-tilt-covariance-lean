import GaussianTilt.MomentMapLinearDirichletVariableWeakAffineSubtractionEquation

/-! # Exact Hölder cost of the genuine affine-subtracted vector forcing -/
noncomputable section
open Set MeasureTheory Filter Matrix
open scoped Topology ContDiff ENNReal BigOperators
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic
variable {n : ℕ}
set_option maxHeartbeats 1400000

/-- Subtracting slope p changes the Hölder load constant by at most
n times the actual coefficient modulus times ‖p‖. -/
theorem affine_subtracted_vector_load_holder {S:Set (CoordinateSpace n)}
    (A:CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (G:CoordinateSpace n → CoordinateSpace n) (p:KernelSpace n)
    {H D β:ℝ} (hD:0≤D)
    (hA:∀ x∈S,∀ y∈S,∀ i k,|A x i k-A y i k|≤D*‖x-y‖^β)
    (hG:∀ x∈S,∀ y∈S,∀ i,|G x i-G y i|≤H*‖x-y‖^β) :
    ∀ x∈S,∀ y∈S,∀ i,
      |(G x i-∑ k:Fin n,A x i k*p k)-(G y i-∑ k:Fin n,A y i k*p k)|≤
        (H+(n:ℝ)*D*‖p‖)*‖x-y‖^β := by
  intro x hx y hy i
  have he : (G x i-∑ k:Fin n,A x i k*p k)-(G y i-∑ k:Fin n,A y i k*p k)=
      (G x i-G y i)-∑ k:Fin n,(A x i k-A y i k)*p k := by
    simp only [sub_mul,Finset.sum_sub_distrib]
    ring
  rw [he]
  apply (abs_sub _ _).trans
  have hc : |∑ k:Fin n,(A x i k-A y i k)*p k|≤(n:ℝ)*D*‖p‖*‖x-y‖^β := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _k:Fin n,(D*‖x-y‖^β)*‖p‖ := by
        apply Finset.sum_le_sum
        intro k _
        rw [abs_mul]
        exact mul_le_mul (hA x hx y hy i k) (PiLp.norm_apply_le p k)
          (abs_nonneg _) (mul_nonneg hD (Real.rpow_nonneg (norm_nonneg _) β))
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring
  exact (add_le_add (hG x hx y hy i) hc).trans_eq (by ring)

end GaussianTilt.MomentMapLinearDirichlet
