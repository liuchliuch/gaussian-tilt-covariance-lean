import GaussianTilt.MomentMapRegularityImprovementReferenceData
import GaussianTilt.MomentMapRegularityImprovementPhysical

/-! # Actual physical Taylor approximations at each constructed affine stage -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal ContDiff Gradient
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.MomentMapSchauder
variable {n : ℕ}
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 1000

theorem physical_reference_approximation_of_stage [NeZero n] {U f : E n → ℝ}
    (hUc : Continuous U) (hUconv : ConvexOn ℝ univ U) (hfc : Continuous f)
    (hMA : ∀ A, IsCompact A → volume (subgradientImage U A)=
      (volume.withDensity (fun x=>ENNReal.ofReal (f x))) A)
    (href : ∀ S : Set (E n), IsCompact S → Convex ℝ S → (interior S).Nonempty →
      ∃ w : E n → ℝ, Continuous w ∧ ContDiffOn ℝ ∞ w (interior S) ∧ ConvexOn ℝ S w ∧
        (∀ y∈frontier S, w y=0) ∧
        ∀ A, IsCompact A → A⊆interior S → volume (subgradientImageOn S w A)=volume A)
    (P : E n ≃L[ℝ] E n) (b : E n) {R R₀ α B F σ : ℝ}
    (hRp : 0 < R) (hRR : R≤R₀) (hα : 0 < α) (hF : 0≤F) (hB : 0 < B)
    (hFB : F*2^α≤B) (hδ1 : B*R^α<1) (hσsmall : σ≤1/16)
    (hPdet : (P : E n →L[ℝ] E n).det=1)
    (hPtwo : ‖(P : E n →L[ℝ] E n)‖≤2) (hPItwo : ‖(P.symm : E n →L[ℝ] E n)‖≤2)
    (hHolder : ∀ y, ‖y‖≤2*R₀ → |f y-1|≤F*‖y‖^α)
    (hnear : ∀ x, ‖x‖≤1 → |improvementRescale U b P R x-‖x‖^2/2|≤σ) :
    ∃ a : ℝ, ∃ p : E n, ∃ H : E n →L[ℝ] E n,
      (∀ v w, inner ℝ (H v) w=inner ℝ v (H w)) ∧
      ∀ x, ‖x‖≤R/16 →
        |U x-quadraticJet a p 0 H x|≤(B/2)*R^(2+α)+
          (8*improvementReferenceConstant n)*‖x‖^3/R := by
  let u := improvementRescale U b P R
  let g : E n → ℝ := fun x=>f (R • P x)
  have huc : Continuous u := improvementRescale_continuous hUc b P R
  have huconv : ConvexOn ℝ univ u := improvementRescale_convex hUconv b P R
  have hu0 : u 0=0 := improvementRescale_zero U b P R
  have hgc : Continuous g := by dsimp [g]; fun_prop
  have hδp : 0 < B*R^α := mul_pos hB (Real.rpow_pos_of_pos hRp _)
  have hshape := near_quadratic_section_geometry huc huconv hu0 (ρ:=1/2) (η:=1/2)
    (R:=1) (ε:=σ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; exact hσsmall) hnear
  have hS : IsCompact (improvementSection u) := by
    convert hshape.1 using 1 <;> norm_num [improvementSection]
  have hSconv : Convex ℝ (improvementSection u) := by
    convert hshape.2.1 using 1 <;> norm_num [improvementSection]
  have hSinner : Metric.closedBall (0:E n) (1/4)⊆interior (improvementSection u) := by
    have hh := near_quadratic_section_contains_closedBall_interior huc (ρ:=1/2) (η:=1/2)
      (R:=1) (ε:=σ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num; exact hσsmall) hnear
    convert hh using 1 <;> norm_num [improvementSection]
  have hSouter : improvementSection u⊆Metric.ball (0:E n) 1 := by
    have hh := hshape.2.2.2.1
    norm_num at hh
    exact hh.trans (Metric.ball_subset_ball (by norm_num))
  have hgδ : ∀ x∈interior (improvementSection u), |g x-1|≤B*R^α := by
    intro x hx
    have hxnorm : ‖x‖≤1 := le_of_lt (by simpa using hSouter (interior_subset hx))
    have hnorm : ‖R • P x‖≤2*R := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos hRp]
      have hh := ((P : E n →L[ℝ] E n).le_opNorm x).trans
        ((mul_le_mul_of_nonneg_right hPtwo (norm_nonneg _)).trans (mul_le_mul_of_nonneg_left hxnorm (by norm_num)))
      simp only [ContinuousLinearEquiv.coe_apply] at hh
      nlinarith
    have hh := hHolder (R • P x) (hnorm.trans (by linarith))
    apply hh.trans
    calc
      F*‖R • P x‖^α ≤ F*(2*R)^α := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hnorm hα.le) hF
      _ = (F*2^α)*R^α := by rw [Real.mul_rpow (by norm_num) hRp.le]; ring
      _ ≤ B*R^α := mul_le_mul_of_nonneg_right hFB (Real.rpow_nonneg hRp.le _)
  have huMA : ∀ Q, IsCompact Q → Q⊆interior (improvementSection u) →
      volume (subgradientImage u Q)=(volume.withDensity (fun x=>ENNReal.ofReal (g x))) Q := by
    intro Q hQ _
    rw [withDensity_apply _ hQ.measurableSet]
    apply alexandrov_density_improvementRescale P hPdet b hRp hQ
    have himage : IsCompact ((fun x:E n=>R • P x) '' Q) := hQ.image (by fun_prop)
    rw [hMA _ himage,withDensity_apply _ himage.measurableSet]
  obtain ⟨w,hwc,hw,hwconv,hwb,hwMA⟩ := href (improvementSection u) hS hSconv
    ⟨0,hSinner (by simp)⟩
  obtain ⟨v,hv,hcompare,hHsym,hTaylor⟩ := near_quadratic_source_reference_data
    huc huconv hu0 hgc hσsmall hδp hδ1 hnear hgδ huMA hwc hw hwconv hwb hwMA
  refine ⟨U 0+R^2*v 0,physicalQuadraticGradient P R b (gradient v 0),
    physicalQuadraticHessian P (frechetHessian v 0),physicalQuadraticHessian_symmetric P hHsym,?_⟩
  intro x hx
  have hh := physical_quadratic_remainder_of_reference P hRp (by norm_num : (0:ℝ)≤2)
    (by positivity : 0≤(B*R^α)/2) (referenceTaylorConstant_nonneg n (1/4) 1) hPItwo
    hcompare hTaylor x (by linarith : 2*‖x‖≤R*(1/8))
  have he : R^2*((B*R^α)/2)=(B/2)*R^(2+α) := by
    rw [Real.rpow_add hRp,Real.rpow_two]
    ring
  convert hh using 1 <;> rw [he] <;> norm_num [improvementReferenceConstant] <;> ring

end GaussianTilt.MomentMapRegularity
