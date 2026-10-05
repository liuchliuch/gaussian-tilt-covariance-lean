import GaussianTilt.MomentMapLinearDirichletVariableWeakUniformChart
import GaussianTilt.MomentMapLinearDirichletVariableWeakForcing

/-! # Smooth local coefficients and bounded scalar data of the constructed chart -/
noncomputable section
open Set MeasureTheory Filter Matrix
open scoped Topology ContDiff ENNReal BigOperators Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapRegularity
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 1000

/-- Every smooth representative agreeing with the genuine chart on the
closed unit patch has the actual measure-distortion bound there. -/
lemma actual_flattening_model_measure_bound {w:E n → ℝ} (hw:ContDiff ℝ ∞ w)
    (a:E n) (j:Fin n) (hj:fderiv ℝ w a (EuclideanSpace.basisFun (Fin n) ℝ j)≠0)
    {s:ℝ} (hs:0<s)
    (hInv:∀ z∈Metric.closedBall (0:E n) (2*s),
      z∈(regularLevelFlatteningChart hw a j hj).target ∧
      ContDiffAt ℝ ∞ (regularLevelFlatteningChart hw a j hj).symm z)
    {ψ:CoordinateSpace n → CoordinateSpace n}
    (he:∀ y∈rawChartClosedBall (n:=n) 1,ψ=ᶠ[𝓝 y] scaledRawInverseChart hw a j hj s) :
    ∃ C:ℝ,0<C ∧ (volume.restrict (rawChartClosedBall (n:=n) 1)).map ψ≤ENNReal.ofReal (C^2) • volume := by
  obtain ⟨ψ',C,hψ',hC,he',hmap,hlevel⟩ := exists_actual_flattening_pullback_model hw a j hj hs hInv
  refine ⟨C,hC,?_⟩
  have hm : (volume.restrict (rawChartClosedBall (n:=n) 1)).map ψ=
      (volume.restrict (rawChartClosedBall (n:=n) 1)).map ψ' := by
    apply Measure.map_congr
    filter_upwards [ae_restrict_mem (isCompact_rawChartClosedBall (n:=n) 1).measurableSet] with x hx
    exact ((he x hx).self_of_nhds).trans ((he' x hx).self_of_nhds).symm
  rw [hm]
  exact hmap

/-- The harmless bounded elliptic extension still has the actual C∞
coefficients throughout the open working patch. -/
lemma contDiffOn_actual_flattening_coefficients {w:E n → ℝ} (hw:ContDiff ℝ ∞ w)
    (a:E n) (j:Fin n) (hj:fderiv ℝ w a (EuclideanSpace.basisFun (Fin n) ℝ j)≠0)
    {s:ℝ} (hs:0<s)
    (hInv:∀ z∈Metric.closedBall (0:E n) (2*s),
      z∈(regularLevelFlatteningChart hw a j hj).target ∧
      ContDiffAt ℝ ∞ (regularLevelFlatteningChart hw a j hj).symm z)
    {ψ:CoordinateSpace n → CoordinateSpace n} (hψ:ContDiff ℝ ∞ ψ)
    (he:∀ y∈rawChartClosedBall (n:=n) 1,ψ=ᶠ[𝓝 y] scaledRawInverseChart hw a j hj s)
    {A:CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hA:∀ x∈rawChartClosedBall (n:=n) (1/4),A x=divergenceChartCoefficient (scaledRawForwardChart w a j s) ψ x) :
    ContDiffOn ℝ ∞ A (rawChartBall (n:=n) (1/4)) := by
  obtain ⟨U,hU,hUb,hleft,hright,hψU,hψΩ⟩ := exists_flattening_physical_test_domain hw a j hj hs hInv hψ he
  have hc := contDiffOn_divergenceChartCoefficient (isOpen_rawChartBall (n:=n) (1/2))
    (contDiff_scaledRawForwardChart hw a j s) hψ hleft
  have hsub : rawChartBall (n:=n) (1/4)⊆rawChartBall (1/2) := by
    intro x hx
    change ‖(coordinateEquiv n).symm x‖<1/4 at hx
    change ‖(coordinateEquiv n).symm x‖<1/2
    linarith
  apply (hc.mono hsub).congr
  intro x hx
  exact hA x (show x∈rawChartClosedBall (n:=n) (1/4) from (show ‖(coordinateEquiv n).symm x‖<1/4 from hx).le)

lemma jacobian_load_locally_bounded {S:Set (CoordinateSpace n)} (hS:IsCompact S)
    {ψ:CoordinateSpace n → CoordinateSpace n} (hψ:ContDiff ℝ ∞ ψ)
    {C:ℝ} (hmap:(volume.restrict S).map ψ≤ENNReal.ofReal (C^2) • volume)
    {f g:CoordinateSpace n → ℝ}
    (hg:∀ᵐ x∂volume,x∈S → g x=|(fderiv ℝ ψ x).det| *f (ψ x))
    {M:ℝ} (hM:0≤M) (hf:∀ᵐ x∂volume,|f x|≤M) :
    ∃ B:ℝ,0≤B ∧ ∀ᵐ x∂volume,x∈S → |g x|≤B := by
  have he : S.indicator g=ᵐ[volume] S.indicator (fun x=>|(fderiv ℝ ψ x).det| *f (ψ x)) := by
    filter_upwards [hg] with x hx
    by_cases hxS:x∈S
    · simp only [indicator_of_mem hxS,hx hxS]
    · simp only [indicator_of_notMem hxS]
  obtain ⟨B,hB,hbound⟩ := masked_jacobian_load_bounded hS hψ hmap he hM hf
  refine ⟨B,hB,?_⟩
  filter_upwards [hbound] with x hx hxS
  simpa only [indicator_of_mem hxS] using hx

end GaussianTilt.MomentMapLinearDirichlet
