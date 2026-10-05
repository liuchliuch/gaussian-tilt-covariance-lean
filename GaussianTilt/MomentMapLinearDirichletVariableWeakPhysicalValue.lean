import GaussianTilt.MomentMapLinearDirichletVariableWeakPhysicalHolder

/-! # The actual continuous zero-flat-boundary value representative in the weak chart -/
noncomputable section
open Set MeasureTheory Filter Matrix
open scoped Topology ContDiff ENNReal BigOperators
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapRegularity GaussianTilt.MomentMapElliptic
variable {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 1000

/-- The already constructed continuous physical Dirichlet representative
really pulls back to a continuous representative of the actual flattened
H¹ value, and it vanishes on the flat boundary. -/
theorem flattened_value_continuous_representative {w:E n → ℝ} (hw:ContDiff ℝ ∞ w)
    (a:E n) (j:Fin n) (hj:fderiv ℝ w a (EuclideanSpace.basisFun (Fin n) ℝ j)≠0)
    {s:ℝ} (hs:0<s)
    (hInv:∀ z∈Metric.closedBall (0:E n) (2*s),
      z∈(regularLevelFlatteningChart hw a j hj).target ∧
      ContDiffAt ℝ ∞ (regularLevelFlatteningChart hw a j hj).symm z)
    {ψ:CoordinateSpace n → CoordinateSpace n} (hψ:ContDiff ℝ ∞ ψ)
    (he:∀ y∈rawChartClosedBall (n:=n) 1,ψ=ᶠ[𝓝 y] scaledRawInverseChart hw a j hj s)
    (u:dirichletSobolev (chartPhysicalDomain w a)) (v:dirichletSobolev (coordinateHalfBall j 1))
    (hval:∀ᵐ x∂volume,x∈rawChartBall (n:=n) (1/2) → v.1 0 x=u.1 0 (ψ x))
    {u₀:CoordinateSpace n → ℝ} (hu₀:Continuous u₀)
    (hphys:∀ᵐ x∂volume,x∈chartPhysicalDomain w a → u₀ x=u.1 0 x)
    (hzero:∀x,x∉chartPhysicalDomain w a → u₀ x=0) :
    ∃ v₀:CoordinateSpace n → ℝ,Continuous v₀ ∧
      (∀ᵐ x∂volume,x∈coordinateHalfBall j (1/4) → v₀ x=v.1 0 x) ∧
      (∀x∈rawChartClosedBall (n:=n) (1/4),x j=0 → v₀ x=0) ∧
      ∀x,v₀ x=u₀ (ψ x) := by
  obtain ⟨U,hU,hUb,hleft,hright,hψU,hψΩ⟩ := exists_flattening_physical_test_domain hw a j hj hs hInv hψ he
  obtain ⟨C,hC,hmap⟩ := actual_flattening_model_measure_bound hw a j hj hs hInv he
  have hsmall (x:CoordinateSpace n) (hx:x∈rawChartClosedBall (n:=n) (1/4)) : x∈rawChartBall (n:=n) (1/2) := by
    change ‖(coordinateEquiv n).symm x‖≤1/4 at hx
    change ‖(coordinateEquiv n).symm x‖<1/2
    linarith
  refine ⟨u₀ ∘ ψ,hu₀.comp hψ.continuous,?_,?_,fun _=>rfl⟩
  · have hp := ae_comp_on_patch (isCompact_rawChartClosedBall (n:=n) 1).measurableSet hψ.continuous.measurable hmap hphys
    filter_upwards [hp,hval] with x hx hvx hxD
    have hxS : x∈rawChartClosedBall (n:=n) 1 := by
      have ht := hxD.1
      change ‖(coordinateEquiv n).symm x‖<1/4 at ht
      change ‖(coordinateEquiv n).symm x‖≤1
      linarith
    have hxH : x∈rawChartBall (n:=n) (1/2) := hsmall x hxD.1.le
    exact (hx hxS (hψΩ ⟨hxH,hxD.2⟩)).trans (hvx hxH).symm
  · intro x hx hxj
    apply hzero
    have hforward := congrArg (fun y:CoordinateSpace n=>y j) (hleft x (hsmall x hx))
    change scaledRawForwardChart w a j s (ψ x) j=x j at hforward
    rw [scaledRawForwardChart_normal,hxj] at hforward
    have hlev : coordinatePullback w (ψ x)=w a := by
      have hi:0<s⁻¹ := inv_pos.mpr hs
      nlinarith
    change ¬coordinatePullback w (ψ x)<w a
    rw [hlev]
    exact lt_irrefl _

end GaussianTilt.MomentMapLinearDirichlet
