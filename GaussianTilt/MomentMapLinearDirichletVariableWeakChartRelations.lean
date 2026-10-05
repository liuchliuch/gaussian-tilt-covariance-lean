import GaussianTilt.MomentMapLinearDirichletVariableWeakHalfBall
import GaussianTilt.MomentMapLinearDirichletVariableWeakEquation

/-! # The exact local inverse relations and physical test domain of the chart -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapRegularity
variable {n : ℕ}
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 1000

lemma scaledRawInverseChart_left_inv {w : E n → ℝ} (hw : ContDiff ℝ ∞ w)
    (a : E n) (j : Fin n) (hj : fderiv ℝ w a (EuclideanSpace.basisFun (Fin n) ℝ j)≠0)
    {s : ℝ} (hs : s≠0) {x : CoordinateSpace n}
    (hx : (coordinateEquiv n).symm x∈(regularLevelFlatteningChart hw a j hj).source) :
    scaledRawInverseChart hw a j hj s (scaledRawForwardChart w a j s x)=x := by
  have hi := (regularLevelFlatteningChart hw a j hj).left_inv hx
  change (regularLevelFlatteningChart hw a j hj).symm (flatteningMap w a j ((coordinateEquiv n).symm x))=
    (coordinateEquiv n).symm x at hi
  unfold scaledRawInverseChart scaledRawForwardChart
  rw [map_smul,(coordinateEquiv n).symm_apply_apply,smul_smul,mul_inv_cancel₀ hs,one_smul,hi,
    (coordinateEquiv n).apply_symm_apply]

lemma scaledRawForwardChart_normal (w : E n → ℝ) (a : E n) (j : Fin n) (s : ℝ) (x : CoordinateSpace n) :
    scaledRawForwardChart w a j s x j=s⁻¹ * (w a-coordinatePullback w x) := by
  change s⁻¹ * (flatteningMap w a j ((coordinateEquiv n).symm x)) j=_
  rw [flatteningMap_normal]
  change s⁻¹ * (-(coordinatePullback w x-w a))=_
  ring

/-- The actual model admits a bounded open physical test neighborhood and
both inverse identities there. This discharges the geometric inputs to
the weak divergence pullback without assuming a global diffeomorphism. -/
theorem exists_flattening_physical_test_domain {w : E n → ℝ} (hw : ContDiff ℝ ∞ w)
    (a : E n) (j : Fin n) (hj : fderiv ℝ w a (EuclideanSpace.basisFun (Fin n) ℝ j)≠0)
    {s : ℝ} (hs : 0 < s)
    (hInv : ∀ z∈Metric.closedBall (0:E n) (2*s),
      z∈(regularLevelFlatteningChart hw a j hj).target ∧
      ContDiffAt ℝ ∞ (regularLevelFlatteningChart hw a j hj).symm z)
    {ψ : CoordinateSpace n → CoordinateSpace n} (hψ : ContDiff ℝ ∞ ψ)
    (he : ∀ y∈rawChartClosedBall (n:=n) 1, ψ=ᶠ[𝓝 y] scaledRawInverseChart hw a j hj s) :
    ∃ U : Set (CoordinateSpace n), IsOpen U ∧ Bornology.IsBounded U ∧
      (∀ z∈rawChartBall (n:=n) (1/2), scaledRawForwardChart w a j s (ψ z)=z) ∧
      (∀ x∈U, scaledRawForwardChart w a j s x∈rawChartBall (n:=n) (1/2) →
        ψ (scaledRawForwardChart w a j s x)=x) ∧
      MapsTo ψ (rawChartBall (n:=n) (1/2)) U ∧
      MapsTo ψ (coordinateHalfBall j (1/2)) (chartPhysicalDomain w a) := by
  let F := scaledRawForwardChart w a j s
  let U₀ := (coordinateEquiv n).symm ⁻¹' (regularLevelFlatteningChart hw a j hj).source
  have hU₀ : IsOpen U₀ := (regularLevelFlatteningChart hw a j hj).open_source.preimage (coordinateEquiv n).symm.continuous
  have hVS : rawChartBall (n:=n) (1/2)⊆rawChartClosedBall 1 := by
    intro z hz
    change ‖(coordinateEquiv n).symm z‖<1/2 at hz
    change ‖(coordinateEquiv n).symm z‖≤1
    linarith
  have hphys (z:CoordinateSpace n) (hz : z∈rawChartBall (n:=n) (1/2)) :
      s • (coordinateEquiv n).symm z∈Metric.closedBall (0:E n) (2*s) := by
    rw [Metric.mem_closedBall,dist_zero_right,norm_smul,Real.norm_of_nonneg hs.le]
    change ‖(coordinateEquiv n).symm z‖<1/2 at hz
    nlinarith
  have heq (z:CoordinateSpace n) (hz : z∈rawChartBall (n:=n) (1/2)) :
      ψ z=scaledRawInverseChart hw a j hj s z := (he z (hVS hz)).self_of_nhds
  have hleft : ∀ z∈rawChartBall (n:=n) (1/2), F (ψ z)=z := by
    intro z hz
    rw [heq z hz]
    have hi := (regularLevelFlatteningChart hw a j hj).right_inv ((hInv _ (hphys z hz)).1)
    change flatteningMap w a j ((regularLevelFlatteningChart hw a j hj).symm
      (s • (coordinateEquiv n).symm z))=s • (coordinateEquiv n).symm z at hi
    change s⁻¹ • coordinateEquiv n (flatteningMap w a j ((coordinateEquiv n).symm
      (coordinateEquiv n ((regularLevelFlatteningChart hw a j hj).symm (s • (coordinateEquiv n).symm z)))))=z
    rw [(coordinateEquiv n).symm_apply_apply,hi,map_smul,(coordinateEquiv n).apply_symm_apply,
      smul_smul,inv_mul_cancel₀ hs.ne',one_smul]
  have hmaps₀ : MapsTo ψ (rawChartBall (n:=n) (1/2)) U₀ := by
    intro z hz
    change (coordinateEquiv n).symm (ψ z)∈_
    rw [heq z hz]
    change (coordinateEquiv n).symm (coordinateEquiv n
      ((regularLevelFlatteningChart hw a j hj).symm (s • (coordinateEquiv n).symm z)))∈_
    rw [(coordinateEquiv n).symm_apply_apply]
    exact (regularLevelFlatteningChart hw a j hj).map_target ((hInv _ (hphys z hz)).1)
  obtain ⟨B,hB⟩ := (isCompact_rawChartClosedBall (n:=n) 1).exists_bound_of_continuousOn hψ.continuous.continuousOn
  let U := U₀∩Metric.ball 0 (max B 0+1)
  refine ⟨U,hU₀.inter Metric.isOpen_ball,Metric.isBounded_ball.subset inter_subset_right,hleft,?_,?_,?_⟩
  · intro x hx hFx
    rw [heq _ hFx]
    exact scaledRawInverseChart_left_inv hw a j hj hs.ne' hx.1
  · intro z hz
    refine ⟨hmaps₀ hz,?_⟩
    rw [Metric.mem_ball,dist_zero_right]
    exact (hB z (hVS hz)).trans_lt (lt_of_le_of_lt (le_max_left _ _) (lt_add_one _))
  · intro z hz
    have hzV : z∈rawChartBall (n:=n) (1/2) := hz.1
    have hi := congrArg (fun y:CoordinateSpace n=>y j) (hleft z hzV)
    change scaledRawForwardChart w a j s (ψ z) j = z j at hi
    rw [scaledRawForwardChart_normal] at hi
    change coordinatePullback w (ψ z)<w a
    have hzj : 0 < z j := hz.2
    have hsInv : 0 < s⁻¹ := inv_pos.mpr hs
    nlinarith

end GaussianTilt.MomentMapLinearDirichlet
