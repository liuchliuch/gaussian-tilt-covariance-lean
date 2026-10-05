import GaussianTilt.MomentMapLinearDirichletVariableWeakChartModel
import GaussianTilt.MomentMapLinearDirichletVariableWeakSobolev
import GaussianTilt.MomentMapLinearDirichletQuantitativeChartForward

/-! # The actual inverse flattening chart as a bounded H¹ pullback model -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapRegularity
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 1000

def rawChartBall (r : ℝ) : Set (CoordinateSpace n) := {x | ‖(coordinateEquiv n).symm x‖<r}
def rawChartClosedBall (r : ℝ) : Set (CoordinateSpace n) := {x | ‖(coordinateEquiv n).symm x‖≤r}

lemma isOpen_rawChartBall (r : ℝ) : IsOpen (rawChartBall (n:=n) r) :=
  isOpen_lt (coordinateEquiv n).symm.continuous.norm continuous_const

lemma isCompact_rawChartClosedBall (r : ℝ) : IsCompact (rawChartClosedBall (n:=n) r) := by
  have he : rawChartClosedBall (n:=n) r=coordinateEquiv n '' Metric.closedBall (0:E n) r := by
    ext y
    constructor
    · intro hy
      exact ⟨(coordinateEquiv n).symm y,by simpa only [Metric.mem_closedBall,dist_zero_right] using hy,
        (coordinateEquiv n).apply_symm_apply y⟩
    · rintro ⟨x,hx,rfl⟩
      simpa only [rawChartClosedBall,mem_setOf_eq,ContinuousLinearEquiv.symm_apply_apply,
        Metric.mem_closedBall,dist_zero_right] using hx
  rw [he]
  exact (isCompact_closedBall _ _).image (coordinateEquiv n).continuous

/-- A globally smooth representative of the genuine local inverse, with
its exact physical level identity and a true area-formula L² distortion
bound on the closed unit chart ball. -/
theorem exists_actual_flattening_pullback_model {w : E n → ℝ} (hw : ContDiff ℝ ∞ w)
    (a : E n) (j : Fin n) (hj : fderiv ℝ w a (EuclideanSpace.basisFun (Fin n) ℝ j)≠0)
    {s : ℝ} (hs : 0 < s)
    (hInv : ∀ z∈Metric.closedBall (0:E n) (2*s),
      z∈(regularLevelFlatteningChart hw a j hj).target ∧
      ContDiffAt ℝ ∞ (regularLevelFlatteningChart hw a j hj).symm z) :
    ∃ ψ : CoordinateSpace n → CoordinateSpace n, ∃ C : ℝ,
      ContDiff ℝ ∞ ψ ∧ 0 < C ∧
      (∀ y∈rawChartClosedBall (n:=n) 1, ψ=ᶠ[𝓝 y] scaledRawInverseChart hw a j hj s) ∧
      (volume.restrict (rawChartClosedBall (n:=n) 1)).map ψ≤ENNReal.ofReal (C^2) • volume ∧
      ∀ y∈rawChartClosedBall (n:=n) 1, coordinatePullback w (ψ y)=w a-s*y j := by
  let g := scaledRawInverseChart hw a j hj s
  let F := scaledRawForwardChart w a j s
  have hphys {y : CoordinateSpace n} (hy : y∈rawChartBall (n:=n) 2) :
      s • (coordinateEquiv n).symm y∈Metric.closedBall (0:E n) (2*s) := by
    rw [Metric.mem_closedBall,dist_zero_right,norm_smul,Real.norm_of_nonneg hs.le]
    change ‖(coordinateEquiv n).symm y‖<2 at hy
    nlinarith
  have hg : ContDiffOn ℝ ∞ g (rawChartBall (n:=n) 2) := by
    intro y hy
    have hlin : ContDiff ℝ ∞ (fun z:CoordinateSpace n=>s • (coordinateEquiv n).symm z) :=
      contDiff_const.smul (coordinateEquiv n).symm.contDiff
    exact ((coordinateEquiv n).contDiff.contDiffAt.comp y
      ((hInv _ (hphys hy)).2.comp y hlin.contDiffAt)).contDiffWithinAt
  have hleft : ∀ y∈rawChartBall (n:=n) 2, F (g y)=y := by
    intro y hy
    have hin := (hInv _ (hphys hy)).1
    have hright := (regularLevelFlatteningChart hw a j hj).right_inv hin
    change flatteningMap w a j ((regularLevelFlatteningChart hw a j hj).symm
      (s • (coordinateEquiv n).symm y))=s • (coordinateEquiv n).symm y at hright
    dsimp [F,g,scaledRawForwardChart,scaledRawInverseChart]
    change s⁻¹ • coordinateEquiv n (flatteningMap w a j ((regularLevelFlatteningChart hw a j hj).symm
      (s • (coordinateEquiv n).symm y)))=y
    rw [hright,map_smul,
      (coordinateEquiv n).apply_symm_apply,smul_smul,inv_mul_cancel₀ hs.ne',one_smul]
  have hsub : rawChartClosedBall (n:=n) 1⊆rawChartBall 2 := by
    intro y hy
    change ‖(coordinateEquiv n).symm y‖≤1 at hy
    change ‖(coordinateEquiv n).symm y‖<2
    linarith
  obtain ⟨ψ,C,hψ,hC,he,hmap⟩ := exists_bounded_smooth_chart_model (isOpen_rawChartBall 2)
    (isCompact_rawChartClosedBall 1) hsub ((contDiff_scaledRawForwardChart hw a j s).differentiable (by simp)) hg hleft
  refine ⟨ψ,C,hψ,hC,he,hmap,?_⟩
  intro y hy
  rw [(he y hy).self_of_nhds]
  change w ((coordinateEquiv n).symm (coordinateEquiv n
    ((regularLevelFlatteningChart hw a j hj).symm (s • (coordinateEquiv n).symm y))))=_
  rw [(coordinateEquiv n).symm_apply_apply,regularLevelFlatteningChart_inverse_level hw a j hj
    ((hInv _ (hphys (hsub hy))).1)]
  rfl

end GaussianTilt.MomentMapLinearDirichlet
