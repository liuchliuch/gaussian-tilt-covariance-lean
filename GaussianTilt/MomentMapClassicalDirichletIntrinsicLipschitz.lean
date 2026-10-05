import GaussianTilt.MomentMapClassicalDirichletIntrinsicTangentDerivatives

/-! # Uniform intrinsic first-jet Lipschitz estimates on the closed convex body -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 500000
open Set Filter Matrix
open scoped Topology ContDiff BigOperators NNReal
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin GaussianTilt.HolderSpace
variable {n : ℕ}

lemma norm_covector_le_of_coordinate_bound (D : CoordinateSpace n →L[ℝ] ℝ)
    {K : ℝ} (hK : 0 ≤ K) (hD : ∀ i, |D (Pi.single i 1)| ≤ K) : ‖D‖ ≤ (n:ℝ)*K := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Nat.cast_nonneg _) hK)
  intro v
  have hv : (∑ i, v i • (Pi.single i 1 : CoordinateSpace n)) = v := by ext i; simp [Pi.single_apply]
  rw [Real.norm_eq_abs,← hv,map_sum]
  simp only [map_smul,smul_eq_mul]
  calc
    _ ≤ ∑ i, |v i*D (Pi.single i 1)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, (‖v‖*K) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul (norm_le_pi_norm v i) (hD i) (abs_nonneg _) (norm_nonneg _)
    _ = _ := by rw [hv]; simp; ring

/-- The first jet is genuinely Lipschitz on the closed body, including
boundary-to-boundary pairs, directly from its actual within derivative. -/
theorem intrinsicDerivative_lipschitzOn_of_hessian_bound
    {S : Set (CoordinateSpace n)} (hS : Convex ℝ S) {α : ℝ} (hα : 0 < α)
    (j : Jet (CoordinateSpace n) ℝ hS α) {K : ℝ≥0}
    (hH : ∀ x ∈ S, ∀ i l, |intrinsicHessian hS α j x i l| ≤ K) (a : Fin n) :
    LipschitzOnWith ((n:ℝ≥0)*K) (intrinsicDerivative hS α j a) S := by
  apply hS.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
    (fun x hx => intrinsicDerivative_hasFDerivWithinAt hS hα j hx a)
  intro x hx
  exact_mod_cast norm_covector_le_of_coordinate_bound
    ((ContinuousLinearMap.apply ℝ ℝ (Pi.single a 1)).comp (intrinsicSecond hS α j x)) K.coe_nonneg
      (fun l => hH x hx a l)

namespace SmoothInnerDomain
variable {S A : Set (E n)} (d : SmoothInnerDomain S A)

theorem intrinsic_dirichletContinuation_uniform_first_lipschitz [NeZero n] {α : ℝ} (hα : 0 < α) :
    ∃ C : ℝ≥0, ∀ t ∈ Icc (0:ℝ) 1,
      ∀ j : zeroBoundary (CoordinateSpace n) ℝ d.coordinate_body_convex α,
      ContDiffOn ℝ ∞ (intrinsicValue d.coordinate_body_convex α j.1) (interior {y | d.coordinateDefining y ≤ 0}) →
      (∀ y ∈ {z | d.coordinateDefining z ≤ 0}, (intrinsicHessian d.coordinate_body_convex α j.1 y).PosDef) →
      (∀ y ∈ {z | d.coordinateDefining z ≤ 0}, (intrinsicHessian d.coordinate_body_convex α j.1 y).det = dirichletContinuationDensity d.coordinateDefining t y) →
      ∀ a, LipschitzOnWith C (intrinsicDerivative d.coordinate_body_convex α j.1 a)
        {y | d.coordinateDefining y ≤ 0} := by
  obtain ⟨K,hK,hbound⟩ := d.intrinsic_dirichletContinuation_uniform_hessian hα
  refine ⟨(n:ℝ≥0)*⟨K,hK⟩,?_⟩
  intro t ht j hs hp hMA a
  exact intrinsicDerivative_lipschitzOn_of_hessian_bound d.coordinate_body_convex hα j.1 (K := ⟨K,hK⟩)
    (hbound t ht j hs hp hMA) a

end SmoothInnerDomain
end GaussianTilt.MomentMapRegularity
