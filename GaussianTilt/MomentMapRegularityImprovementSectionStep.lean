import GaussianTilt.MomentMapRegularityImprovementReference
import GaussianTilt.MomentMapRegularitySecondOrderLocalPerturbation

/-! # Improvement on the genuine rough-source sublevel section -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal Gradient ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin GaussianTilt.MomentMapSchauder
variable {n : ℕ}

def improvementSection (u : E n → ℝ) : Set (E n) := {x | u x≤1/8}
def improvementReferenceConstant (n : ℕ) : ℝ := referenceTaylorConstant n (1/4) 1

/-- Constant-density comparison and genuine local reference estimates
discharge the comparison, Taylor, positive Hessian and Jacobian inputs of
the actual normalization step. Section roundness follows from the rough
source value error itself. -/
theorem near_quadratic_source_reference_step [NeZero n] {u w f : E n → ℝ}
    (huc : Continuous u) (hc : ConvexOn ℝ univ u) (hu0 : u 0=0)
    (hfc : Continuous f) {σ δ r ρ θ : ℝ}
    (hσ : 0≤σ) (hσsmall : σ≤1/16) (hδ : 0<δ) (hδ1 : δ<1)
    (hr : 0<r) (hrR : r≤1/8) (hρ : 0<ρ) (hθ : 0≤θ) (hθhalf : θ≤1/2)
    (hcoef : 4*(σ+δ/2)/r^2+4*improvementReferenceConstant n*r≤θ)
    (hregion : ρ*(1+2*θ)≤1/8)
    (hnear : ∀ x, ‖x‖≤1 → |u x-‖x‖^2/2|≤σ)
    (hdensity : ∀ x∈interior (improvementSection u), |f x-1|≤δ)
    (hMA : ∀ A, IsCompact A → A⊆interior (improvementSection u) →
      volume (subgradientImage u A)=(volume.withDensity (fun x=>ENNReal.ofReal (f x))) A)
    (hwc : Continuous w) (hw : ContDiffOn ℝ ∞ w (interior (improvementSection u)))
    (hwconv : ConvexOn ℝ (improvementSection u) w)
    (hwb : ∀ y∈frontier (improvementSection u), w y=0)
    (hwMA : ∀ A, IsCompact A → A⊆interior (improvementSection u) →
      volume (subgradientImageOn (improvementSection u) w A)=volume A) :
    ∃ p : E n, ∃ L : E n ≃L[ℝ] E n,
      (L : E n →L[ℝ] E n).det=1 ∧
      ‖(L : E n →L[ℝ] E n)-1‖≤2*θ ∧
      ‖(L.symm : E n →L[ℝ] E n)-1‖≤θ ∧
      Continuous (improvementRescale u p L ρ) ∧
      ConvexOn ℝ univ (improvementRescale u p L ρ) ∧
      improvementRescale u p L ρ 0=0 ∧
      ∀ x, ‖x‖≤1 → |improvementRescale u p L ρ x-‖x‖^2/2|≤
        δ/ρ^2+improvementReferenceConstant n*ρ*(1+2*θ)^3 := by
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
  obtain ⟨L,hL,hLn,hLi,hLc,hLconv,hL0,herr⟩ := actual_reference_improvement_step huc hc
    (contDiff_infty.mp hv 2) hPD hdet (a:=v 0) (p:=gradient v 0) (R:=1/8) (r:=r)
    (ρ:=ρ) (S:=1) (σ:=σ) (ε:=δ/2) (C:=improvementReferenceConstant n) (θ:=θ)
    hr hrR hρ (by norm_num) hσ (by positivity) (referenceTaylorConstant_nonneg _ _ _)
    hθ hθhalf hcoef (by simpa using hregion)
    (fun y hy=>hnear y (hy.trans (by norm_num))) hvcompare (by convert hTaylor using 1 <;> norm_num [improvementReferenceConstant])
  refine ⟨gradient v 0,L,hL,hLn,hLi,hLc,hLconv,hL0,?_⟩
  intro x hx
  have hh := herr x hx
  convert hh using 1 <;> ring

end GaussianTilt.MomentMapRegularity
