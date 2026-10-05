import GaussianTilt.MomentMapHolderChartFields
import GaussianTilt.MomentMapHolderJetRegularity

/-! # Genuine bounded composition of arbitrary closed Hölder jets

Only the fixed chart is smooth. The unknown is an arbitrary compatible
C²,α jet; its derivative identities and both target FTC laws are proved.
The curvature term in the Hessian is retained explicitly.
-/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 500000
open Set
open scoped ContDiff
namespace GaussianTilt.HolderSpace
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_jet_smooth_chart_composition
    {S : Set F} {T : Set E} (hS : Convex ℝ S) (hT : Convex ℝ T)
    (hTc : IsCompact T) (hTi : (interior T).Nonempty)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (ψ : E → F) (hψ : ContDiff ℝ ∞ ψ)
    (hmap : MapsTo ψ T S) (hmapi : MapsTo ψ (interior T) (interior S)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ J : Jet F ℝ hS α, ∃ j : Jet E ℝ hT α,
      ‖j‖ ≤ C*‖J‖ ∧
      (∀ x : T, value T ℝ α (jetValue E ℝ hT α j) x =
        extendValue α (jetValue F ℝ hS α J) (ψ x)) ∧
      (∀ x : T, value T (E →L[ℝ] ℝ) α (jetFirst E ℝ hT α j) x =
        chartFirst (extendValue α (jetFirst F ℝ hS α J)) ψ x) ∧
      (∀ x : T, value T (E →L[ℝ] E →L[ℝ] ℝ) α (jetSecond E ℝ hT α j) x =
        chartSecond (extendValue α (jetFirst F ℝ hS α J))
          (extendValue α (jetSecond F ℝ hS α J)) ψ x) := by
  obtain ⟨K,hK1,hK⟩ := exists_smoothChartBounds hTc hT hα.le hα1 ψ hψ
  let L := K^α
  have hL : 0 ≤ L := Real.rpow_nonneg hK.nonneg _
  let C := 1+L+K+(L*K+K)+(K*K+K)+(L*K*K+2*K*K+L*K+K)
  have hC : 0 ≤ C := by dsimp only [C]; nlinarith [hK.nonneg, mul_nonneg hL hK.nonneg, mul_nonneg (mul_nonneg hL hK.nonneg) hK.nonneg, sq_nonneg K]
  refine ⟨C,hC,?_⟩
  intro J
  let N := ‖J‖
  have hN : 0 ≤ N := norm_nonneg J
  let u := extendValue α (jetValue F ℝ hS α J)
  let D := extendValue α (jetFirst F ℝ hS α J)
  let H := extendValue α (jetSecond F ℝ hS α J)
  obtain ⟨hu,huH⟩ := holder_field_comp_bounds hα.le hK.nonneg hN ψ hmap hK.lipschitz
    (jetValue F ℝ hS α J) (norm_jetValue_le hS α J)
  obtain ⟨hD,hDH⟩ := holder_field_comp_bounds hα.le hK.nonneg hN ψ hmap hK.lipschitz
    (jetFirst F ℝ hS α J) (norm_jetFirst_le hS α J)
  obtain ⟨hH,hHH⟩ := holder_field_comp_bounds hα.le hK.nonneg hN ψ hmap hK.lipschitz
    (jetSecond F ℝ hS α J) (norm_jetSecond_le hS α J)
  change (∀ x ∈ T, ‖u (ψ x)‖ ≤ N) at hu
  change (∀ x ∈ T, ∀ y ∈ T, ‖u (ψ x)-u (ψ y)‖ ≤ N*L*‖x-y‖^α) at huH
  change (∀ x ∈ T, ‖D (ψ x)‖ ≤ N) at hD
  change (∀ x ∈ T, ∀ y ∈ T, ‖D (ψ x)-D (ψ y)‖ ≤ N*L*‖x-y‖^α) at hDH
  change (∀ x ∈ T, ‖H (ψ x)‖ ≤ N) at hH
  change (∀ x ∈ T, ∀ y ∈ T, ‖H (ψ x)-H (ψ y)‖ ≤ N*L*‖x-y‖^α) at hHH
  obtain ⟨hG,hGH⟩ := chart_first_bounds hN hL hK D hD hDH
  obtain ⟨hB,hBH⟩ := chart_second_bounds hN hL hK D H hD hH hDH hHH
  have hdu : ∀ x ∈ interior T, HasFDerivAt (fun y => u (ψ y)) (chartFirst D ψ x) x := by
    intro x hx
    exact (jet_hasFDerivAt hS hα J (hmapi hx)).comp x
      ((hψ.differentiable (by simp) x).hasFDerivAt)
  have hdD : ∀ x ∈ interior T, HasFDerivAt (chartFirst D ψ) (chartSecond D H ψ x) x := by
    intro x hx
    have hp := (hψ.differentiable (by simp) x).hasFDerivAt
    have hpD : ContDiff ℝ ∞ (fderiv ℝ ψ) := hψ.fderiv_right (by simp)
    have hdp := (hpD.differentiable (by simp) x).hasFDerivAt
    have hh := ((jet_first_hasFDerivAt hS hα J (hmapi hx)).comp x hp).clm_comp hdp
    have he : ((ContinuousLinearMap.compL ℝ E F ℝ) (D (ψ x))).comp
        (fderiv ℝ (fderiv ℝ ψ) x) +
        ((ContinuousLinearMap.compL ℝ E F ℝ).flip (fderiv ℝ ψ x)).comp
          ((H (ψ x)).comp (fderiv ℝ ψ x)) = chartSecond D H ψ x := by
      ext v w
      simp [chartSecond,postcomposeBilinear,add_comm]
    change HasFDerivAt (chartFirst D ψ)
      (((ContinuousLinearMap.compL ℝ E F ℝ) (D (ψ x))).comp (fderiv ℝ (fderiv ℝ ψ) x) +
        ((ContinuousLinearMap.compL ℝ E F ℝ).flip (fderiv ℝ ψ x)).comp ((H (ψ x)).comp (fderiv ℝ ψ x))) x at hh
    rw [he] at hh
    exact hh
  obtain ⟨j,hju,hjD,hjH⟩ := exists_jet_of_continuous_holder_interior_fields hT hTc hTi
    (fun x => u (ψ x)) (chartFirst D ψ) (chartSecond D H ψ)
    (continuousOn_of_holder_bound_general hα huH)
    (continuousOn_of_holder_bound_general hα hGH)
    (continuousOn_of_holder_bound_general (V := E →L[ℝ] E →L[ℝ] ℝ) (G := chartSecond D H ψ) hα hBH)
    (by simpa only [dist_eq_norm] using huH)
    (by simpa only [dist_eq_norm] using hGH)
    (by simpa only [dist_eq_norm] using hBH) hdu hdD
  refine ⟨j,?_,hju,hjD,hjH⟩
  have hc1 : 1 ≤ C := by dsimp only [C]; nlinarith [hK.nonneg, mul_nonneg hL hK.nonneg, mul_nonneg (mul_nonneg hL hK.nonneg) hK.nonneg, sq_nonneg K]
  have hcL : L ≤ C := by dsimp only [C]; nlinarith [hK.nonneg, mul_nonneg hL hK.nonneg, mul_nonneg (mul_nonneg hL hK.nonneg) hK.nonneg, sq_nonneg K]
  have hcK : K ≤ C := by dsimp only [C]; nlinarith [hK.nonneg, mul_nonneg hL hK.nonneg, mul_nonneg (mul_nonneg hL hK.nonneg) hK.nonneg, sq_nonneg K]
  have hcG : L*K+K ≤ C := by dsimp only [C]; nlinarith [hK.nonneg, mul_nonneg hL hK.nonneg, mul_nonneg (mul_nonneg hL hK.nonneg) hK.nonneg, sq_nonneg K]
  have hcB : K*K+K ≤ C := by dsimp only [C]; nlinarith [hK.nonneg, mul_nonneg hL hK.nonneg, mul_nonneg (mul_nonneg hL hK.nonneg) hK.nonneg, sq_nonneg K]
  have hcBH : L*K*K+2*K*K+L*K+K ≤ C := by dsimp only [C]; nlinarith [hK.nonneg, mul_nonneg hL hK.nonneg, mul_nonneg (mul_nonneg hL hK.nonneg) hK.nonneg, sq_nonneg K]
  have hCN : 0 ≤ C*N := mul_nonneg hC hN
  apply norm_jet_le_of_field_norms hT
  · apply norm_le_of_value_bounds hCN
    · intro x; rw [hju x]
      exact (hu x x.2).trans (by nlinarith [mul_le_mul_of_nonneg_right hc1 hN])
    · intro x y; rw [hju x,hju y]
      simpa only [Subtype.dist_eq,dist_eq_norm] using (huH x x.2 y y.2).trans
        (mul_le_mul_of_nonneg_right (by nlinarith [mul_le_mul_of_nonneg_right hcL hN])
          (Real.rpow_nonneg (norm_nonneg ((x:E)-y)) α))
  · apply norm_le_of_value_bounds hCN
    · intro x; rw [hjD x]
      exact (hG x x.2).trans (by nlinarith [mul_le_mul_of_nonneg_right hcK hN])
    · intro x y; rw [hjD x,hjD y]
      simpa only [Subtype.dist_eq,dist_eq_norm] using (hGH x x.2 y y.2).trans
        (mul_le_mul_of_nonneg_right (by nlinarith [mul_le_mul_of_nonneg_right hcG hN])
          (Real.rpow_nonneg (norm_nonneg ((x:E)-y)) α))
  · apply norm_le_of_value_bounds hCN
    · intro x; rw [hjH x]
      exact (hB x x.2).trans (by nlinarith [mul_le_mul_of_nonneg_right hcB hN])
    · intro x y; rw [hjH x,hjH y]
      simpa only [Subtype.dist_eq,dist_eq_norm] using (hBH x x.2 y y.2).trans
        (mul_le_mul_of_nonneg_right (by nlinarith [mul_le_mul_of_nonneg_right hcBH hN])
          (Real.rpow_nonneg (norm_nonneg ((x:E)-y)) α))

end GaussianTilt.HolderSpace
