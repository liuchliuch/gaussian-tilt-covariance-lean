import GaussianTilt.MomentMapLinearDirichletVariableWeakHolderRepresentation

/-! # Actual physical Hölder data become the required weak-chart loads -/
noncomputable section
open Set MeasureTheory Filter Matrix
open scoped Topology ContDiff ENNReal BigOperators NNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapRegularity GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapSchauder
variable {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 1000

/-- Smooth fixed chart coefficients have genuine bounded Hölder first
coefficient derivatives on each compact convex inner patch. -/
lemma boundedHolderOn_coefficient_derivatives {U S:Set (CoordinateSpace n)}
    (hU:IsOpen U) (hS:IsCompact S) (hc:Convex ℝ S) (hSU:S⊆U)
    {A:CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hA:∀ i k,ContDiffOn ℝ ∞ (fun x=>A x i k) U)
    {α:ℝ} (hα:0≤α) (hα1:α≤1) (a i k:Fin n) :
    BoundedHolderOn α (coordinateDerivative a (fun x=>A x i k)) S := by
  have hd : ContDiffOn ℝ ∞ (coordinateDerivative a (fun x=>A x i k)) U :=
    ((hA i k).fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const
  obtain ⟨C,hC,hb,hh⟩ := exists_contDiffOn_holder_bound_on_compact_convex hU
    (hd.of_le (by simp)) hS hc hSU hα hα1
  exact ⟨C,hC.le,hb,hh⟩

/-- A physical Hölder datum gives an actual Hölder representative of the
constructed scalar L² chart load, including at the flat boundary. The AE
change of representative is justified by the true Jacobian map bound. -/
theorem flattened_scalar_load_holder_representative {w:E n → ℝ} (hw:ContDiff ℝ ∞ w)
    (a:E n) (j:Fin n) (hj:fderiv ℝ w a (EuclideanSpace.basisFun (Fin n) ℝ j)≠0)
    {s:ℝ} (hs:0<s)
    (hInv:∀ z∈Metric.closedBall (0:E n) (2*s),
      z∈(regularLevelFlatteningChart hw a j hj).target ∧
      ContDiffAt ℝ ∞ (regularLevelFlatteningChart hw a j hj).symm z)
    {ψ:CoordinateSpace n → CoordinateSpace n} (hψ:ContDiff ℝ ∞ ψ)
    (he:∀ y∈rawChartClosedBall (n:=n) 1,ψ=ᶠ[𝓝 y] scaledRawInverseChart hw a j hj s)
    (f g:Lp ℝ 2 (volume:Measure (CoordinateSpace n)))
    (hg:∀ᵐ x∂volume,x∈rawChartClosedBall (n:=n) 1 → g x=|(fderiv ℝ ψ x).det| *f (ψ x))
    {f₀:CoordinateSpace n → ℝ}
    (hf:∀ᵐ x∂volume,x∈chartPhysicalDomain w a → f x=f₀ x)
    {α:ℝ} (hα:0≤α) (hα1:α≤1) (hfH:BoundedHolderOn α f₀ univ) :
    ∃ g₀:CoordinateSpace n → ℝ,
      BoundedHolderOn α g₀ (rawChartClosedBall (n:=n) (1/4)) ∧
      (∀ᵐ x∂volume,x∈coordinateHalfBall j (1/4) → g x=g₀ x) ∧
      ∀ x,g₀ x=|(fderiv ℝ ψ x).det| *f₀ (ψ x) := by
  obtain ⟨U,hU,hUb,hleft,hright,hψU,hψΩ⟩ := exists_flattening_physical_test_domain hw a j hj hs hInv hψ he
  obtain ⟨C,hC,hmap⟩ := actual_flattening_model_measure_bound hw a j hj hs hInv he
  let g₀ := fun x=>|(fderiv ℝ ψ x).det| *f₀ (ψ x)
  have hSsub : rawChartClosedBall (n:=n) (1/4)⊆rawChartBall (1/2) := by
    intro x hx
    change ‖(coordinateEquiv n).symm x‖≤1/4 at hx
    change ‖(coordinateEquiv n).symm x‖<1/2
    linarith
  have hbound := boundedHolderOn_chart_scalar_forcing (isOpen_rawChartBall (n:=n) (1/2))
    (isCompact_rawChartClosedBall (n:=n) (1/4)) (convex_rawChartClosedBall (n:=n) (1/4)) hSsub
    (contDiff_scaledRawForwardChart hw a j s) hψ hleft hα hα1 (hfH.mono (subset_univ _))
  refine ⟨g₀,hbound,?_,fun _=>rfl⟩
  have hfψ := ae_comp_on_patch (isCompact_rawChartClosedBall (n:=n) 1).measurableSet
    hψ.continuous.measurable hmap hf
  filter_upwards [hg,hfψ] with x hx hfx hxD
  have hxS : x∈rawChartClosedBall (n:=n) 1 := by
    have hh := hxD.1
    change ‖(coordinateEquiv n).symm x‖<1/4 at hh
    change ‖(coordinateEquiv n).symm x‖≤1
    linarith
  have hxhalf : x∈coordinateHalfBall j (1/2) := ⟨hSsub hxD.1.le,hxD.2⟩
  rw [hx hxS,hfx hxS (hψΩ hxhalf)]

end GaussianTilt.MomentMapLinearDirichlet
