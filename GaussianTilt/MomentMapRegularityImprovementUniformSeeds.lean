import GaussianTilt.MomentMapRegularityImprovementSectionRadius
import GaussianTilt.MomentMapRegularityImprovementAmplitudeBounds

/-! # Uniform actual near-quadratic seeds at every nearby source center -/
noncomputable section
open Set Metric MeasureTheory Filter
open scoped NNReal ENNReal ContDiff
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 1000

def recurrenceSeedPotential (φ f : E n → ℝ) (T L : E n ≃L[ℝ] E n)
    (x p q : E n) (h ρ R : ℝ) : E n → ℝ :=
  improvementRescale (normalizedSectionPotential φ f T x p h) q L (ρ/R)

def recurrenceSeedDensity (f : E n → ℝ) (T L : E n ≃L[ℝ] E n)
    (x : E n) (ρ R : ℝ) : E n → ℝ :=
  fun y=>normalizedSectionDensity f T x ((ρ/R) • L y)

/-- Genuine weak source data and first-order Hölder density produce a
uniform family of actual near-quadratic recurrence seeds. Every coordinate
map and amplitude is constructed from the original source sections. The
classical reference existence input is the remaining independent PDE task. -/
theorem exists_uniform_recurrence_seeds [NeZero n] {φ f : E n → ℝ} {Lip : ℝ≥0}
    (hLip : LipschitzWith Lip φ) (hc : StrictConvexOn ℝ univ φ) (hfc : Continuous f)
    (hMA : ∀ A, IsCompact A → volume (subgradientImage φ A)=
      (volume.withDensity (fun y=>ENNReal.ofReal (f y))) A)
    (href : ∀ S : Set (E n), IsCompact S → Convex ℝ S → (interior S).Nonempty →
      ∃ w : E n → ℝ, Continuous w ∧ ContDiffOn ℝ ∞ w (interior S) ∧ ConvexOn ℝ S w ∧
        (∀ y∈frontier S, w y=0) ∧
        ∀ A, IsCompact A → A⊆interior S → volume (subgradientImageOn S w A)=volume A)
    (x₀ : E n) {r m M F α R η : ℝ} (hr : 0 < r) (hm : 0 < m) (hM : 0 < M)
    (hF : 0≤F) (hα : 0 < α) (hR : 0 < R) (hη : 0 < η)
    (hfrange : ∀ y∈closedBall x₀ r, m≤f y ∧ f y≤M)
    (hfHolder : ∀ y∈closedBall x₀ r, ∀ z∈closedBall x₀ r, |f y-f z|≤F*‖y-z‖^α) :
    ∃ ρ h : ℝ, 0 < ρ ∧ 0 < h ∧ ∀ x∈closedBall x₀ (r/2),
      ∃ p q : E n, ∃ T L : E n ≃L[ℝ] E n,
        (L : E n →L[ℝ] E n).det=1 ∧
        ‖(T : E n →L[ℝ] E n)‖≤ improvementOuterRadius n/(h/(2*(Lip:ℝ)+1)) ∧
        ‖(T.symm : E n →L[ℝ] E n)‖≤1/improvementInnerRadius n m M ∧
        ‖(L.symm : E n →L[ℝ] E n)‖≤ initialForwardNormalizationBound n (improvementInnerRadius n m M) (improvementOuterRadius n) ∧
        Continuous (recurrenceSeedPotential φ f T L x p q h ρ R) ∧
        ConvexOn ℝ univ (recurrenceSeedPotential φ f T L x p q h ρ R) ∧
        Continuous (recurrenceSeedDensity f T L x ρ R) ∧
        (∀ A, IsCompact A → volume (subgradientImage (recurrenceSeedPotential φ f T L x p q h ρ R) A)=
          (volume.withDensity (fun y=>ENNReal.ofReal (recurrenceSeedDensity f T L x ρ R y))) A) ∧
        (∀ y, ‖y‖≤2*R → |recurrenceSeedDensity f T L x ρ R y-1|≤‖y‖^α) ∧
        ∀ y, ‖y‖≤1 →
          |improvementRescale (recurrenceSeedPotential φ f T L x p q h ρ R) 0
            (ContinuousLinearMap.id ℝ (E n)) R y-‖y‖^2/2|≤η := by
  let rin := improvementInnerRadius n m M
  let rout := improvementOuterRadius n
  let N := initialNormalizationBound n rin rout
  let C := referenceTaylorConstant n rin rout
  have hrin : 0 < rin := improvementInnerRadius_pos n hm hM
  have hrout : 0≤rout := by dsimp [rout,improvementOuterRadius]; positivity
  have hN : 0 < N := (by norm_num : (0:ℝ)<1).trans_le (le_max_right _ _)
  have hC : 0≤C := referenceTaylorConstant_nonneg _ _ _
  obtain ⟨ρ,δ,hρ,hδ,hδ1,hregion,herror⟩ := exists_initial_seed_scales (R:=rout) hrin hC hN hη
  obtain ⟨ε,hε,hεr,hε1,hεosc,hεholder⟩ := exists_small_improvement_section_radius
    (F:=F) (ρ:=ρ) (N:=N) (R:=R) hr hrin hm hα hδ
  have hmass : ∀ A : Set (E n), IsCompact A → A⊆closedBall x₀ r →
      ENNReal.ofReal m*volume A≤volume (subgradientImage φ A) ∧
      volume (subgradientImage φ A)≤ENNReal.ofReal M*volume A := by
    intro A hA hAK
    rw [hMA A hA]
    constructor
    · apply const_mul_le_withDensity_of_ae hA.measurableSet
      filter_upwards [ae_restrict_mem hA.measurableSet] with y hy
      exact ENNReal.ofReal_le_ofReal (hfrange y (hAK hy)).1
    · apply withDensity_le_const_mul_of_ae hA.measurableSet
      filter_upwards [ae_restrict_mem hA.measurableSet] with y hy
      exact ENNReal.ofReal_le_ofReal (hfrange y (hAK hy)).2
  obtain ⟨h,hh,hsections⟩ := exists_uniform_centered_source_sections hLip hc x₀ hr hε hεr hm hM hmass
  refine ⟨ρ,h,hρ,hh,?_⟩
  intro x hx
  obtain ⟨p,hp⟩ := exists_supportsAt_of_lipschitz_convex hLip hc.convexOn x
  obtain ⟨T,hS,hSball,hTin,hTout,hTi,hT⟩ := hsections x hx p hp
  let S := supportSection φ p x h
  let D := (fun y=>T (y-x)) '' S
  let u := normalizedSectionPotential φ f T x p h
  let g := normalizedSectionDensity f T x
  have hxK : x∈closedBall x₀ r := closedBall_subset_closedBall (half_le_self hr.le) hx
  have hfx : 0 < f x := hm.trans_le (hfrange x hxK).1
  obtain ⟨huc,huconv,hgc,hub,huMA⟩ := normalized_section_potential_data hLip.continuous hc.convexOn hfc hMA T x p h hfx
  have hD : IsCompact D := hS.image (T.continuous.comp (continuous_id.sub continuous_const))
  have hDconv : Convex ℝ D := by
    have hcc := ((convex_supportSection hc.convexOn p x h).translate (-x)).linear_image T.toLinearMap
    simpa only [image_image,Function.comp_def,neg_add_eq_sub] using hcc
  have hDi : (interior D).Nonempty := ⟨0,hTin (by simp only [mem_closedBall,dist_self]; exact hrin.le)⟩
  obtain ⟨w,hwc,hw,hwconv,hwb,hwMA⟩ := href D hD hDconv hDi
  have huMAlocal : ∀ A, IsCompact A → A⊆interior D →
      volume (subgradientImageOn D u A)=(volume.withDensity (fun y=>ENNReal.ofReal (g y))) A := by
    intro A hA hAD
    rw [subgradientImageOn_eq_global huconv hAD]
    exact huMA A hA
  have hSK : S⊆closedBall x₀ r := by
    intro y hy
    have hh1 : dist y x≤ε := hSball hy
    have hh2 : dist x x₀≤r/2 := hx
    exact (dist_triangle y x x₀).trans (by linarith)
  have hgdata := normalized_section_density_bounds T hα.le hF hm hε.le (div_nonneg hε.le hrin.le)
    hxK hSK hSball (hfrange x hxK).1 hTi hfHolder
  have hgosc : ∀ y∈interior D, |g y-1|≤δ := by
    intro y hy
    exact ((hgdata y (interior_subset hy)).1).trans hεosc
  obtain ⟨q,L,hLdet,hLn,hLin,_,_,_,herr⟩ := initial_reference_normalization huc huconv hgc hwc hD
    hw hwconv hub hwb huMAlocal hwMA hrin hrout hTout hTin hδ hδ1 hgosc hρ hregion
  have hgHolder : ∀ y, ‖y‖≤rin → |g y-1|≤(F*(ε/rin)^α/m)*‖y‖^α := by
    intro y hy
    have hyD : y∈D := interior_subset (hTin (by simpa only [mem_closedBall,dist_zero_right] using hy))
    exact (hgdata y hyD).2
  have hseed : ∀ y, ‖y‖≤1 → |improvementRescale u q L ρ y-‖y‖^2/2|≤η :=
    fun y hy=>(herr y hy).trans herror
  have hdata := normalized_seed_recurrence_data huc huconv hgc huMA L q hLdet hρ hR hN.le
    (by positivity : 0≤F*(ε/rin)^α/m) hα.le hLn (by linarith) hεholder hgHolder hseed
  refine ⟨p,q,T,L,hLdet,hT,?_,hLin,hdata⟩
  exact hTi.trans (div_le_div_of_nonneg_right hε1 hrin.le)

end GaussianTilt.MomentMapRegularity
