import GaussianTilt.MomentMapRegularityImprovementConclusion
import GaussianTilt.MomentMapRegularityInteriorHolder
import GaussianTilt.MomentMapRegularitySecondOrderDensity

/-! # First C²,α regularity from the literal weak moment transport -/
noncomputable section
open Set MeasureTheory Metric
open scoped NNReal ENNReal ContDiff Gradient
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 1000

lemma improvementRemainderExponent_lt_one {α : ℝ} (hα : 0 < α) :
    improvementRemainderExponent α<1 := by
  have hc : 0 < improvementScaleExponent α := by dsimp [improvementScaleExponent]; positivity
  unfold improvementRemainderExponent
  apply (div_lt_one (by positivity : 0 < 2*(1+improvementScaleExponent α))).mpr
  linarith

/-- The sole external regularity construction in this theorem is the
classical unit-density Dirichlet reference. All source strictness, C¹,α,
weak MA, section geometry, normalization, iteration and C²,α identification
are derived from the actual weak transport. -/
theorem moment_source_C2_holder_of_classical_references [NeZero n]
    {φ V : E n → ℝ} {L : ℝ≥0} (hL : LipschitzWith L φ) (hc : ConvexOn ℝ univ φ)
    {K : Set (E n)} (hK : IsOpen K) (hKc : Convex ℝ K) (hKb : Bornology.IsBounded K)
    (hV : ContDiff ℝ 1 V)
    (hmap : (volume.withDensity (fun x=>ENNReal.ofReal (Real.exp (-φ x)))).map (gradient φ)=
      volume.withDensity (fun x=>ENNReal.ofReal (K.indicator (fun y=>Real.exp (-V y)) x)))
    (href : ∀ S : Set (E n), IsCompact S → Convex ℝ S → (interior S).Nonempty →
      ∃ w : E n → ℝ, Continuous w ∧ ContDiffOn ℝ ∞ w (interior S) ∧ ConvexOn ℝ S w ∧
        (∀ y∈frontier S, w y=0) ∧
        ∀ A, IsCompact A → A⊆interior S → volume (subgradientImageOn S w A)=volume A) :
    ContDiff ℝ 2 φ ∧ ∀ a : E n, ∃ R H β : ℝ, 0 < R ∧ 0≤H ∧ 0 < β ∧ β<1 ∧
      ∀ x∈closedBall a (2*R), ∀ y∈closedBall a (2*R),
        ‖fderiv ℝ (fderiv ℝ φ) x-fderiv ℝ (fderiv ℝ φ) y‖≤H*‖x-y‖^β := by
  have hstrict := strictConvexOn_of_target_density hL hc hK hKc hKb hV.continuous.continuousOn hmap
  have hC1 := contDiff_one_of_target_density hL hc hK hKc hKb hV.continuous.continuousOn hmap
  have hg := continuous_gradient_of_lipschitz_convex_differentiable hL hc (hC1.differentiable le_rfl)
  let f : E n → ℝ := fun x=>Real.exp (V (gradient φ x)-φ x)
  have hfc : Continuous f := Real.continuous_exp.comp
    ((hV.continuous.comp hg).sub hL.continuous)
  have hMA : ∀ A, IsCompact A → volume (subgradientImage φ A)=
      (volume.withDensity (fun y=>ENNReal.ofReal (f y))) A := by
    intro A hA
    exact volume_subgradientImage_eq_mongeAmpere_density hL hc hK hKc hV.continuous.continuousOn hmap hA
  have hfirst := local_holder_gradient_of_target_density hL hc hK hKc hKb hV.continuous.continuousOn hmap
  have hdensity := local_holder_density_of_local_holder_gradient hL hg (fun _=>hV.contDiffAt) hfirst
  have hlocal : ∀ a : E n, ContDiffAt ℝ 2 φ a ∧
      ∃ R H β : ℝ, 0 < R ∧ 0≤H ∧ 0 < β ∧ β<1 ∧
        ∀ x∈closedBall a (2*R), ∀ y∈closedBall a (2*R),
          ‖fderiv ℝ (fderiv ℝ φ) x-fderiv ℝ (fderiv ℝ φ) y‖≤H*‖x-y‖^β := by
    intro a
    obtain ⟨r,m,M,F,α,hr,hm,hM,hF,hα,hα1,hfrange,hfHolder⟩ := hdensity a
    have hsub : closedBall a (r/2)⊆ball a r := closedBall_subset_ball (half_lt_self hr)
    obtain ⟨hreg,R,H,hR,hH,hregsub,hholder⟩ := contDiffOn_two_holder_of_classical_references
      hL hstrict hfc hMA href a (half_pos hr) hm hM hF.le hα hα1
      (fun y hy=>hfrange y (hsub hy)) (fun y hy z hz=>hfHolder y (hsub hy) z (hsub hz))
    refine ⟨hreg.contDiffAt (ball_mem_nhds a (by positivity)),R,H,improvementRemainderExponent α,
      hR,hH,(improvement_exponents hα hα1).2.1,improvementRemainderExponent_lt_one hα,hholder⟩
  exact ⟨contDiff_iff_contDiffAt.mpr (fun a=>(hlocal a).1),fun a=>(hlocal a).2⟩

end GaussianTilt.MomentMapRegularity
