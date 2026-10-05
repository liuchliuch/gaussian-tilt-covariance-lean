import GaussianTilt.MomentMapRegularityImprovementSectionStep

/-! # The actual section reference retains all of its Taylor data -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal Gradient ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin GaussianTilt.MomentMapSchauder
variable {n : ℕ}

theorem near_quadratic_source_reference_data [NeZero n] {u w f : E n → ℝ}
    (huc : Continuous u) (hc : ConvexOn ℝ univ u) (hu0 : u 0=0)
    (hfc : Continuous f) {σ δ : ℝ} (hσsmall : σ≤1/16) (hδ : 0<δ) (hδ1 : δ<1)
    (hnear : ∀ x, ‖x‖≤1 → |u x-‖x‖^2/2|≤σ)
    (hdensity : ∀ x∈interior (improvementSection u), |f x-1|≤δ)
    (hMA : ∀ A, IsCompact A → A⊆interior (improvementSection u) →
      volume (subgradientImage u A)=(volume.withDensity (fun x=>ENNReal.ofReal (f x))) A)
    (hwc : Continuous w) (hw : ContDiffOn ℝ ∞ w (interior (improvementSection u)))
    (hwconv : ConvexOn ℝ (improvementSection u) w)
    (hwb : ∀ y∈frontier (improvementSection u), w y=0)
    (hwMA : ∀ A, IsCompact A → A⊆interior (improvementSection u) →
      volume (subgradientImageOn (improvementSection u) w A)=volume A) :
    ∃ v : E n → ℝ, ContDiff ℝ ∞ v ∧
      (∀ y, ‖y‖≤1/8 → |u y-v y|≤δ/2) ∧
      (∀ z q, inner ℝ (frechetHessian v 0 z) q=inner ℝ z (frechetHessian v 0 q)) ∧
      ∀ y, ‖y‖≤1/8 →
        |v y-quadraticJet (v 0) (gradient v 0) 0 (frechetHessian v 0) y|≤
          improvementReferenceConstant n*‖y‖^3 := by
  have hshape := near_quadratic_section_geometry huc hc hu0 (ρ:=1/2) (η:=1/2)
    (R:=1) (ε:=σ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact hσsmall) hnear
  have hS : IsCompact (improvementSection u) := by
    convert hshape.1 using 1 <;> norm_num [improvementSection]
  have hSR : improvementSection u⊆Metric.closedBall (0:E n) 1 := by
    have hh := hshape.2.2.2.1
    norm_num at hh
    exact hh.trans (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by norm_num)))
  have hrS : Metric.closedBall (0:E n) (1/4)⊆interior (improvementSection u) := by
    have hh := near_quadratic_section_contains_closedBall_interior huc (ρ:=1/2) (η:=1/2)
      (R:=1) (ε:=σ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num; exact hσsmall) hnear
    convert hh using 1 <;> norm_num [improvementSection]
  have hub : ∀ y∈frontier (improvementSection u), u y-(1/8:ℝ)=0 := by
    convert hshape.2.2.2.2.2 using 1 <;> norm_num [improvementSection]
  have huMA : ∀ A, IsCompact A → A⊆interior (improvementSection u) →
      volume (subgradientImageOn (improvementSection u) (fun y=>u y-1/8) A)=
        (volume.withDensity (fun x=>ENNReal.ofReal (f x))) A := by
    intro A hA hAS
    have hh := volume_subgradientImageOn_pos_mul_add_const (improvementSection u) u
      (t:=1) (by norm_num) (-(1/8)) A
    simp only [one_mul,one_pow,ENNReal.ofReal_one,sub_eq_add_neg] at hh
    simp only [sub_eq_add_neg]
    rw [hh,subgradientImageOn_eq_global hc hAS]
    exact hMA A hA hAS
  have hcompare := alexandrovOn_normalized_constant_density_perturbation
    (huc.sub continuous_const) hwc hfc hS (R:=1) (by norm_num) hSR hub hwb hδ hδ1 hdensity huMA hwMA
  obtain ⟨v,hv,he,hPD,hdet,hTaylor⟩ := exists_reference_improvement_representative
    hwc hS hw hwconv hwb hwMA (r:=1/4) (R:=1) (by norm_num) (by norm_num) hSR hrS (1/8)
  have hvcompare : ∀ y:E n, ‖y‖≤1/8 → |u y-v y|≤δ/2 := by
    intro y hy
    rw [he y (by norm_num; exact hy)]
    have hyball : y∈Metric.closedBall (0:E n) (1/4) := by
      rw [Metric.mem_closedBall,dist_zero_right]
      linarith
    have hyS := interior_subset (hrS hyball)
    have hh := hcompare y hyS
    convert hh using 1 <;> norm_num <;> ring
  refine ⟨v,hv,hvcompare,?_,?_⟩
  · exact frechetHessian_symmetric (contDiff_infty.mp hv 2) 0
  · convert hTaylor using 1 <;> norm_num [improvementReferenceConstant]

end GaussianTilt.MomentMapRegularity
