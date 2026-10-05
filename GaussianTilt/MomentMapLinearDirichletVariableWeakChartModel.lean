import GaussianTilt.MomentMapLinearDirichletVariableWeakJacobian
import GaussianTilt.MomentMapBoundaryRegularityLocalSystem

/-! # Actual globally measurable chart representatives and their L² distortion -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff Manifold ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin
variable {n : ℕ}
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 1000

lemma exists_global_smooth_chart_eq_near_compact
    {ψ : CoordinateSpace n → CoordinateSpace n} {U S : Set (CoordinateSpace n)}
    (hU : IsOpen U) (hψ : ContDiffOn ℝ ∞ ψ U) (hS : IsCompact S) (hSU : S⊆U) :
    ∃ Ψ : CoordinateSpace n → CoordinateSpace n, ContDiff ℝ ∞ Ψ ∧ ∀ x∈S, Ψ=ᶠ[𝓝 x] ψ := by
  obtain ⟨χ,hχ0,hχ1,_⟩ := exists_smooth_zero_one_nhds_of_isClosed
    𝓘(ℝ,CoordinateSpace n) hU.isClosed_compl hS.isClosed
    (disjoint_left.mpr (fun x hx hxS=>hx (hSU hxS)))
  let Ψ := fun x=>χ x • ψ x
  have hχ : ContDiff ℝ ∞ (χ : CoordinateSpace n → ℝ) := χ.contMDiff.contDiff
  have hΨ : ContDiff ℝ ∞ Ψ := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x∈U
    · exact hχ.contDiffAt.smul (hψ.contDiffAt (hU.mem_nhds hx))
    · have hz : ∀ᶠ y in 𝓝 x, χ y=0 := hχ0.filter_mono (nhds_le_nhdsSet hx)
      apply contDiffAt_const.congr_of_eventuallyEq
      filter_upwards [hz] with y hy
      change χ y • ψ y=0
      rw [hy,zero_smul]
  refine ⟨Ψ,hΨ,?_⟩
  intro x hx
  have hone : ∀ᶠ y in 𝓝 x, χ y=1 := hχ1.filter_mono (nhds_le_nhdsSet hx)
  filter_upwards [hone] with y hy
  change χ y • ψ y=ψ y
  rw [hy,one_smul]

lemma jacobian_ne_zero_of_local_left_inverse {U : Set (CoordinateSpace n)} (hU : IsOpen U)
    {F ψ : CoordinateSpace n → CoordinateSpace n} (hF : Differentiable ℝ F)
    (hψ : DifferentiableOn ℝ ψ U) (hleft : ∀ x∈U, F (ψ x)=x) {x : CoordinateSpace n} (hx : x∈U) :
    (fderiv ℝ ψ x).det≠0 := by
  have he : F ∘ ψ=ᶠ[𝓝 x] id := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hleft y hy
  have hd := (he.fderiv (𝕜:=ℝ)).self_of_nhds
  rw [fderiv_comp x (hF _) ((hψ x hx).differentiableAt (hU.mem_nhds hx)),fderiv_id] at hd
  have hdet := congrArg (fun A : CoordinateSpace n →L[ℝ] CoordinateSpace n=>A.det) hd
  change LinearMap.det ((fderiv ℝ F (ψ x)).toLinearMap.comp (fderiv ℝ ψ x).toLinearMap)=LinearMap.det (LinearMap.id : CoordinateSpace n →ₗ[ℝ] CoordinateSpace n) at hdet
  rw [LinearMap.det_comp,LinearMap.det_id] at hdet
  intro hz
  change LinearMap.det (fderiv ℝ ψ x).toLinearMap=0 at hz
  rw [hz,mul_zero] at hdet
  exact zero_ne_one hdet

/-- A genuine local smooth inverse has an actual globally smooth model
near the chosen compact chart patch and a proved bounded L² pullback there.
No global invertibility of the harmless extension is needed or asserted. -/
theorem exists_bounded_smooth_chart_model {U S : Set (CoordinateSpace n)} (hU : IsOpen U)
    (hS : IsCompact S) (hSU : S⊆U)
    {F ψ : CoordinateSpace n → CoordinateSpace n} (hF : Differentiable ℝ F)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hleft : ∀ x∈U, F (ψ x)=x) :
    ∃ Ψ : CoordinateSpace n → CoordinateSpace n, ∃ C : ℝ, ContDiff ℝ ∞ Ψ ∧ 0 < C ∧
      (∀ x∈S, Ψ=ᶠ[𝓝 x] ψ) ∧
      (volume.restrict S).map Ψ≤ENNReal.ofReal (C ^ 2) • volume := by
  obtain ⟨Ψ,hΨ,he⟩ := exists_global_smooth_chart_eq_near_compact hU hψ hS hSU
  have hJac : ∀ x∈S, (fderiv ℝ Ψ x).det≠0 := by
    intro x hx
    rw [((he x hx).fderiv (𝕜:=ℝ)).self_of_nhds]
    exact jacobian_ne_zero_of_local_left_inverse hU hF (hψ.differentiableOn (by simp)) hleft (hSU hx)
  obtain ⟨lam,hlam,hmin⟩ := exists_jacobian_lower_on_compact hS
    (hΨ.continuous_fderiv (by simp)).continuousOn hJac
  have hinj : InjOn Ψ S := by
    intro x hx y hy heq
    have hx' := hleft x (hSU hx)
    have hy' := hleft y (hSU hy)
    rw [← (he x hx).self_of_nhds] at hx'
    rw [← (he y hy).self_of_nhds] at hy'
    rw [← hx',← hy',heq]
  have hmap := map_restrict_le_of_jacobian_lower hS.measurableSet hΨ.continuous.measurable
    (fun x _=>(hΨ.differentiable (by simp) x).hasFDerivAt) hinj hlam hmin
  let C := lam⁻¹+1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨Ψ,C,hΨ,hC,he,hmap.trans ?_⟩
  have hreal : lam⁻¹≤C ^ 2 := by dsimp [C]; nlinarith [inv_pos.mpr hlam,sq_nonneg lam⁻¹]
  rw [← ENNReal.ofReal_inv_of_pos hlam]
  apply Measure.le_iff.mpr
  intro A hA
  simp only [Measure.smul_apply,smul_eq_mul]
  exact mul_le_mul_right' (ENNReal.ofReal_le_ofReal hreal) (volume A)

end GaussianTilt.MomentMapLinearDirichlet
