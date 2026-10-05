import GaussianTilt.MomentMapLinearDirichletQuantitativeChartInverse

/-! # Actual scaled raw-coordinate chart fields and fixed derivative constants -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 1000
open Set Filter Matrix
open scoped Topology ContDiff BigOperators Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapRegularity GaussianTilt.Letwin
variable {n : ℕ}

def scaledRawInverseChart {w : KernelSpace n → ℝ} (hw : ContDiff ℝ ∞ w)
    (a : KernelSpace n) (j : Fin n)
    (hj : fderiv ℝ w a (EuclideanSpace.basisFun (Fin n) ℝ j) ≠ 0)
    (s : ℝ) (y : CoordinateSpace n) : CoordinateSpace n :=
  coordinateEquiv n ((regularLevelFlatteningChart hw a j hj).symm (s • (coordinateEquiv n).symm y))

def scaledRawChartJacobian {w : KernelSpace n → ℝ} (hw : ContDiff ℝ ∞ w)
    (a : KernelSpace n) (j : Fin n)
    (hj : fderiv ℝ w a (EuclideanSpace.basisFun (Fin n) ℝ j) ≠ 0)
    (s : ℝ) (y : CoordinateSpace n) : Matrix (Fin n) (Fin n) ℝ :=
  flatteningJacobian w j ((regularLevelFlatteningChart hw a j hj).symm (s • (coordinateEquiv n).symm y))

lemma flatteningJacobian_entry (w : KernelSpace n → ℝ) (j i k : Fin n) (x : KernelSpace n) :
    flatteningJacobian w j x i k =
      if i=j then -fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ k)
      else if i=k then 1 else 0 := by
  rw [flatteningJacobian,euclideanCLMMatrix_entry]
  by_cases hi : i=j
  · subst i
    rw [boundaryRowLinear_normal]
    simp
  · simp [boundaryRowLinear_apply,EuclideanSpace.basisFun_apply,hi,Ne.symm hi,eq_comm]

lemma contDiff_flatteningJacobian_entry {w : KernelSpace n → ℝ}
    (hw : ContDiff ℝ ∞ w) (j i k : Fin n) :
    ContDiff ℝ ∞ (fun x => flatteningJacobian w j x i k) := by
  simp only [flatteningJacobian_entry]
  by_cases hi : i=j
  · simp only [hi,if_true]
    exact ((hw.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).neg
  · simp only [if_neg hi]
    exact contDiff_const

/-- The fixed scaled inverse and Jacobian fields are smooth on a true
neighborhood of the unit raw Euclidean ball. Compactness constructs their
actual raw derivative bounds, before any unknown coefficient or solution. -/
theorem exists_scaled_raw_chart_bounds {w : KernelSpace n → ℝ} (hw : ContDiff ℝ ∞ w)
    (a : KernelSpace n) (j : Fin n)
    (hj : fderiv ℝ w a (EuclideanSpace.basisFun (Fin n) ℝ j) ≠ 0)
    {s : ℝ} (hs : 0 < s)
    (hInv : ∀ z ∈ Metric.closedBall (0:KernelSpace n) (2*s),
      ContDiffAt ℝ ∞ (regularLevelFlatteningChart hw a j hj).symm z) :
    ∃ Cx Cj : ℝ, 1 ≤ Cx ∧ 1 ≤ Cj ∧
      (∀ y, ‖(coordinateEquiv n).symm y‖ < 2 →
        ContDiffAt ℝ ∞ (scaledRawInverseChart hw a j hj s) y ∧
        ∀ i k, ContDiffAt ℝ ∞ (fun z => scaledRawChartJacobian hw a j hj s z i k) y) ∧
      (∀ y, ‖(coordinateEquiv n).symm y‖ ≤ 1 →
        ThreeDerivativeBound (scaledRawInverseChart hw a j hj s) y Cx ∧
        (∀ i k, |scaledRawChartJacobian hw a j hj s y i k| ≤ Cj) ∧
        ∀ k i l, |matrixCoordinateDerivative (scaledRawChartJacobian hw a j hj s) k y i l| ≤ Cj) := by
  let U := {y : CoordinateSpace n | ‖(coordinateEquiv n).symm y‖ < 2}
  let S := {y : CoordinateSpace n | ‖(coordinateEquiv n).symm y‖ ≤ 1}
  have hU : IsOpen U := isOpen_lt (coordinateEquiv n).symm.continuous.norm continuous_const
  have hS : IsCompact S := by
    have he : S=coordinateEquiv n '' Metric.closedBall (0:E n) 1 := by
      ext y
      constructor
      · intro hy
        exact ⟨(coordinateEquiv n).symm y,by simpa only [Metric.mem_closedBall,dist_zero_right] using hy,
          (coordinateEquiv n).apply_symm_apply y⟩
      · rintro ⟨x,hx,rfl⟩
        simpa only [ContinuousLinearEquiv.symm_apply_apply,Metric.mem_closedBall,dist_zero_right] using hx
    rw [he]
    exact (isCompact_closedBall _ _).image (coordinateEquiv n).continuous
  have hSU : S ⊆ U := fun y hy => by
    change ‖(coordinateEquiv n).symm y‖ ≤ 1 at hy
    change ‖(coordinateEquiv n).symm y‖ < 2
    linarith
  have hlin : ContDiff ℝ ∞ (fun y : CoordinateSpace n => s • (coordinateEquiv n).symm y) :=
    contDiff_const.smul (coordinateEquiv n).symm.contDiff
  have hphys (y : CoordinateSpace n) (hy : y ∈ U) :
      ContDiffAt ℝ ∞ (fun z : CoordinateSpace n =>
        (regularLevelFlatteningChart hw a j hj).symm (s • (coordinateEquiv n).symm z)) y := by
    have hz : s • (coordinateEquiv n).symm y ∈ Metric.closedBall (0:KernelSpace n) (2*s) := by
      simp only [Metric.mem_closedBall,dist_zero_right,norm_smul,Real.norm_of_nonneg hs.le]
      have hy2 : ‖(coordinateEquiv n).symm y‖ < 2 := hy
      nlinarith
    exact (hInv _ hz).comp y hlin.contDiffAt
  have hraw (y : CoordinateSpace n) (hy : y ∈ U) :
      ContDiffAt ℝ ∞ (scaledRawInverseChart hw a j hj s) y :=
    (coordinateEquiv n).contDiff.contDiffAt.comp y (hphys y hy)
  have hJac (i k : Fin n) (y : CoordinateSpace n) (hy : y ∈ U) :
      ContDiffAt ℝ ∞ (fun z => scaledRawChartJacobian hw a j hj s z i k) y :=
    (contDiff_flatteningJacobian_entry hw j i k).contDiffAt.comp y (hphys y hy)
  obtain ⟨Cx,hCx,hXb⟩ := exists_three_derivative_bound_on_compact hU
    (fun y hy => (hraw y hy).contDiffWithinAt) hS hSU
  have hJc : ContinuousOn (scaledRawChartJacobian hw a j hj s) S :=
    continuousOn_pi.mpr (fun i => continuousOn_pi.mpr (fun k y hy =>
      (hJac i k y (hSU hy)).continuousAt.continuousWithinAt))
  have hDJc : ContinuousOn (fun y k i l =>
      matrixCoordinateDerivative (scaledRawChartJacobian hw a j hj s) k y i l) S :=
    continuousOn_pi.mpr (fun k => continuousOn_pi.mpr (fun i => continuousOn_pi.mpr (fun l y hy =>
      (contDiffAt_coordinateDerivative (hJac i l y (hSU hy)) (m := 0) (by simp) k).continuousAt.continuousWithinAt)))
  obtain ⟨J₀,hJ₀⟩ := hS.exists_bound_of_continuousOn hJc
  obtain ⟨J₁,hJ₁⟩ := hS.exists_bound_of_continuousOn hDJc
  let Cj := max 1 (max J₀ J₁)
  refine ⟨Cx,Cj,hCx,le_max_left _ _,?_,?_⟩
  · intro y hy
    exact ⟨hraw y hy,fun i k => hJac i k y hy⟩
  · intro y hy
    refine ⟨hXb y hy,?_,?_⟩
    · intro i k
      have hh := (norm_le_pi_norm (scaledRawChartJacobian hw a j hj s y i) k).trans
        ((norm_le_pi_norm (scaledRawChartJacobian hw a j hj s y) i).trans (hJ₀ y hy))
      exact hh.trans ((le_max_left J₀ J₁).trans (le_max_right _ _))
    · intro k i l
      have hh := (norm_le_pi_norm (matrixCoordinateDerivative (scaledRawChartJacobian hw a j hj s) k y i) l).trans
        ((norm_le_pi_norm (matrixCoordinateDerivative (scaledRawChartJacobian hw a j hj s) k y) i).trans
          ((norm_le_pi_norm (fun k => matrixCoordinateDerivative (scaledRawChartJacobian hw a j hj s) k y) k).trans (hJ₁ y hy)))
      exact hh.trans ((le_max_right J₀ J₁).trans (le_max_right _ _))

end GaussianTilt.MomentMapLinearDirichlet
