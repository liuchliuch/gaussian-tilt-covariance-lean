import GaussianTilt.MomentMapHolderChartFields

/-! # Uniform quantitative recovery of the actual curved-chart Hessian -/
noncomputable section
set_option maxHeartbeats 2000000
open Set
open scoped ContDiff
namespace GaussianTilt.HolderSpace
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_chart_second_uniform_bounds
    {T : Set E} {U : Set F} (hTc : IsCompact T) (hT : Convex ℝ T)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (φ : E → F) (hφ : ContDiff ℝ ∞ φ) (hmap : MapsTo φ T U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : F → F →L[ℝ] ℝ) (H : F → F →L[ℝ] F →L[ℝ] ℝ)
      (Z : ℝ), 0 ≤ Z →
      (∀ x ∈ U, ‖D x‖ ≤ Z) → (∀ x ∈ U, ‖H x‖ ≤ Z) →
      (∀ x ∈ U, ∀ y ∈ U, ‖D x-D y‖ ≤ Z*‖x-y‖^α) →
      (∀ x ∈ U, ∀ y ∈ U, ‖H x-H y‖ ≤ Z*‖x-y‖^α) →
      (∀ x ∈ T, ‖chartSecond D H φ x‖ ≤ C*Z) ∧
      (∀ x ∈ T, ∀ y ∈ T, ‖chartSecond D H φ x-chartSecond D H φ y‖ ≤ C*Z*‖x-y‖^α) := by
  obtain ⟨K,hK1,hK⟩ := exists_smoothChartBounds hTc hT hα hα1 φ hφ
  let L := K^α
  have hL : 0 ≤ L := Real.rpow_nonneg hK.nonneg _
  let C := (K*K+K)+(L*K*K+2*K*K+L*K+K)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C,hC,?_⟩
  intro D H Z hZ hD hH hDH hHH
  have hpow (x : E) (hx : x ∈ T) (y : E) (hy : y ∈ T) :
      ‖φ x-φ y‖^α ≤ L*‖x-y‖^α := by
    have hh := Real.rpow_le_rpow (norm_nonneg _) (hK.lipschitz x hx y hy) hα
    rwa [Real.mul_rpow hK.nonneg (norm_nonneg _)] at hh
  have hDcomp : ∀ x ∈ T, ∀ y ∈ T, ‖D (φ x)-D (φ y)‖ ≤ Z*L*‖x-y‖^α := by
    intro x hx y hy
    exact (hDH _ (hmap hx) _ (hmap hy)).trans
      ((mul_le_mul_of_nonneg_left (hpow x hx y hy) hZ).trans_eq (by ring))
  have hHcomp : ∀ x ∈ T, ∀ y ∈ T, ‖H (φ x)-H (φ y)‖ ≤ Z*L*‖x-y‖^α := by
    intro x hx y hy
    exact (hHH _ (hmap hx) _ (hmap hy)).trans
      ((mul_le_mul_of_nonneg_left (hpow x hx y hy) hZ).trans_eq (by ring))
  obtain ⟨hb,hh⟩ := chart_second_bounds hZ hL hK D H
    (fun x hx => hD _ (hmap hx)) (fun x hx => hH _ (hmap hx)) hDcomp hHcomp
  have hCb : K*K+K ≤ C := by
    dsimp only [C]
    nlinarith [hK.nonneg,mul_nonneg hL hK.nonneg,mul_nonneg (mul_nonneg hL hK.nonneg) hK.nonneg,sq_nonneg K]
  have hCh : L*K*K+2*K*K+L*K+K ≤ C := by dsimp only [C]; nlinarith [hK.nonneg,sq_nonneg K]
  constructor
  · intro x hx
    exact (hb x hx).trans (by nlinarith [mul_le_mul_of_nonneg_right hCb hZ])
  · intro x hx y hy
    exact (hh x hx y hy).trans (mul_le_mul_of_nonneg_right
      (by nlinarith [mul_le_mul_of_nonneg_right hCh hZ]) (Real.rpow_nonneg (norm_nonneg _) _))

end GaussianTilt.HolderSpace
