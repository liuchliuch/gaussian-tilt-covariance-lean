import GaussianTilt.MomentMapLinearDirichletQuantitativeChartForward

/-! # One genuine physical neighborhood for all boundary centers -/
noncomputable section
set_option maxHeartbeats 2000000
open Set Filter
open scoped Topology ContDiff
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapRegularity GaussianTilt.Letwin
variable {n : ℕ}

/-- A single smaller physical neighborhood works simultaneously at every
boundary center in it. Its radius and derivative constants depend only on
the fixed defining function and the already selected chart scale. -/
theorem exists_scaled_chart_approach_neighborhood {w : KernelSpace n → ℝ}
    (hw : ContDiff ℝ ∞ w) (a : KernelSpace n) (j : Fin n)
    (hj : fderiv ℝ w a (EuclideanSpace.basisFun (Fin n) ℝ j) ≠ 0)
    (s : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ r C : ℝ, 0 < r ∧ r ≤ 1 ∧ 2*r ≤ ρ ∧ 1 ≤ C ∧ C*r ≤ 1/32 ∧
      (∀ x ∈ Metric.closedBall a (2*r),
        x ∈ (regularLevelFlatteningChart hw a j hj).source ∧
        ‖(coordinateEquiv n).symm (scaledRawForwardChart w a j s (coordinateEquiv n x))‖ ≤ 1/4 ∧
        ‖fderiv ℝ (scaledRawForwardChart w a j s) (coordinateEquiv n x)‖ ≤ C) ∧
      (∀ x ∈ Metric.closedBall a (2*r), ∀ z ∈ Metric.closedBall a (2*r),
        ‖fderiv ℝ (scaledRawForwardChart w a j s) (coordinateEquiv n x)-
          fderiv ℝ (scaledRawForwardChart w a j s) (coordinateEquiv n z)‖ ≤ C*dist x z ∧
        ‖(coordinateEquiv n).symm (scaledRawForwardChart w a j s (coordinateEquiv n x)-
          scaledRawForwardChart w a j s (coordinateEquiv n z))‖ ≤ C*dist x z) := by
  obtain ⟨C,hC,hCb,hCD,hCL⟩ := exists_scaled_raw_forward_bounds hw a j s ρ
  have hCp : 0 < C := zero_lt_one.trans_le hC
  obtain ⟨η,hη,hηU⟩ := Metric.isOpen_iff.mp (regularLevelFlatteningChart hw a j hj).open_source
    a (regularLevelFlatteningChart_source hw a j hj)
  let r := min (ρ/2) (min (η/4) (min 1 (1/(128*C))))
  have hr : 0 < r := by dsimp only [r]; positivity
  have hrρ : r ≤ ρ/2 := min_le_left _ _
  have hrη : r ≤ η/4 := (min_le_right _ _).trans (min_le_left _ _)
  have hr1 : r ≤ 1 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrC : r ≤ 1/(128*C) := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hCr : C*r ≤ 1/128 := by
    have hh := (le_div_iff₀ (show 0 < 128*C by positivity)).mp hrC
    nlinarith
  have hsub : Metric.closedBall a (2*r) ⊆ Metric.closedBall a ρ := Metric.closedBall_subset_closedBall (by linarith)
  refine ⟨r,C,hr,hr1,by linarith,hC,by linarith,?_,?_⟩
  · intro x hx
    have hxa : dist x a ≤ 2*r := hx
    have hsource : x ∈ (regularLevelFlatteningChart hw a j hj).source :=
      hηU (by change dist x a < η; linarith)
    refine ⟨hsource,?_,hCb x (hsub hx)⟩
    have hh := hCL x (hsub hx) a (Metric.mem_closedBall_self hρ.le)
    rw [scaledRawForward_self,sub_zero] at hh
    have hm := mul_le_mul_of_nonneg_left hxa hCp.le
    nlinarith
  · intro x hx z hz
    exact ⟨hCD x (hsub hx) z (hsub hz),hCL x (hsub hx) z (hsub hz)⟩

end GaussianTilt.MomentMapLinearDirichlet
