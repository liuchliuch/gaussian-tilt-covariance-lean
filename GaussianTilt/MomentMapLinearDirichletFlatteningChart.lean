import GaussianTilt.MomentMapLinearDirichletFlatteningLinear

/-! # Explicit genuine regular-level flattening charts -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

/-- The j-th flattened coordinate is exactly the negative level difference;
all other coordinates retain their translated physical coordinates. -/
def flatteningMap (w : KernelSpace n → ℝ) (a : KernelSpace n) (j : Fin n) (y : KernelSpace n) : KernelSpace n :=
  y - a + (-(w y - w a) - (y j - a j)) • (EuclideanSpace.basisFun (Fin n) ℝ j)

@[simp] lemma flatteningMap_self (w : KernelSpace n → ℝ) (a : KernelSpace n) (j : Fin n) :
    flatteningMap w a j a = 0 := by simp [flatteningMap]

lemma flatteningMap_normal (w : KernelSpace n → ℝ) (a y : KernelSpace n) (j : Fin n) :
    (flatteningMap w a j y) j = -(w y - w a) := by
  simp [flatteningMap, EuclideanSpace.basisFun_apply]

lemma flatteningMap_level_iff (w : KernelSpace n → ℝ) (a y : KernelSpace n) (j : Fin n) :
    (flatteningMap w a j y) j = 0 ↔ w y = w a := by
  rw [flatteningMap_normal]
  constructor <;> intro h <;> linarith

lemma flatteningMap_sublevel_iff (w : KernelSpace n → ℝ) (a y : KernelSpace n) (j : Fin n) :
    0 < (flatteningMap w a j y) j ↔ w y < w a := by
  rw [flatteningMap_normal]
  constructor <;> intro h <;> linarith

lemma contDiff_flatteningMap {m : WithTop ℕ∞} {w : KernelSpace n → ℝ}
    (hw : ContDiff ℝ m w) (a : KernelSpace n) (j : Fin n) :
    ContDiff ℝ m (flatteningMap w a j) := by
  unfold flatteningMap
  fun_prop

lemma hasFDerivAt_flatteningMap {w : KernelSpace n → ℝ} {y : KernelSpace n}
    (hw : DifferentiableAt ℝ w y) (a : KernelSpace n) (j : Fin n) :
    HasFDerivAt (flatteningMap w a j) (boundaryRowLinear (-fderiv ℝ w y) j) y := by
  have hs : HasFDerivAt (fun z : KernelSpace n => -(w z - w a) - (z j - a j))
      (-fderiv ℝ w y - flatteningCoordinate j) y :=
    (hw.hasFDerivAt.sub_const (w a)).neg.sub
      ((flatteningCoordinate j).hasFDerivAt.sub_const (a j))
  exact ((hasFDerivAt_id y).sub_const a).add (hs.smul_const (EuclideanSpace.basisFun (Fin n) ℝ j))

def flatteningDerivativeEquiv (w : KernelSpace n → ℝ) (a : KernelSpace n) (j : Fin n)
    (hj : fderiv ℝ w a (EuclideanSpace.basisFun (Fin n) ℝ j) ≠ 0) : KernelSpace n ≃L[ℝ] KernelSpace n :=
  boundaryRowEquiv (-fderiv ℝ w a) j (by simpa only [ContinuousLinearMap.neg_apply] using neg_ne_zero.mpr hj)

lemma strictDeriv_flatteningMap {w : KernelSpace n → ℝ} (hw : ContDiff ℝ ∞ w)
    (a : KernelSpace n) (j : Fin n)
    (hj : fderiv ℝ w a (EuclideanSpace.basisFun (Fin n) ℝ j) ≠ 0) :
    HasStrictFDerivAt (flatteningMap w a j) (flatteningDerivativeEquiv w a j hj : _ →L[ℝ] _) a := by
  exact (contDiff_flatteningMap hw a j).contDiffAt.hasStrictFDerivAt'
    (hasFDerivAt_flatteningMap (hw.differentiable (by simp) a) a j) (by simp)

/-- The actual inverse function theorem constructs a genuine local chart;
no boundary parametrization is supplied as a hypothesis. -/
def regularLevelFlatteningChart {w : KernelSpace n → ℝ} (hw : ContDiff ℝ ∞ w)
    (a : KernelSpace n) (j : Fin n)
    (hj : fderiv ℝ w a (EuclideanSpace.basisFun (Fin n) ℝ j) ≠ 0) : OpenPartialHomeomorph (KernelSpace n) (KernelSpace n) :=
  (strictDeriv_flatteningMap hw a j hj).toOpenPartialHomeomorph (flatteningMap w a j)

@[simp] lemma regularLevelFlatteningChart_apply {w : KernelSpace n → ℝ} (hw : ContDiff ℝ ∞ w)
    (a : KernelSpace n) (j : Fin n)
    (hj : fderiv ℝ w a (EuclideanSpace.basisFun (Fin n) ℝ j) ≠ 0) (y : KernelSpace n) :
    regularLevelFlatteningChart hw a j hj y = flatteningMap w a j y := rfl

lemma regularLevelFlatteningChart_source {w : KernelSpace n → ℝ} (hw : ContDiff ℝ ∞ w)
    (a : KernelSpace n) (j : Fin n)
    (hj : fderiv ℝ w a (EuclideanSpace.basisFun (Fin n) ℝ j) ≠ 0) :
    a ∈ (regularLevelFlatteningChart hw a j hj).source :=
  (strictDeriv_flatteningMap hw a j hj).mem_toOpenPartialHomeomorph_source

lemma regularLevelFlatteningChart_target {w : KernelSpace n → ℝ} (hw : ContDiff ℝ ∞ w)
    (a : KernelSpace n) (j : Fin n)
    (hj : fderiv ℝ w a (EuclideanSpace.basisFun (Fin n) ℝ j) ≠ 0) :
    (0 : KernelSpace n) ∈ (regularLevelFlatteningChart hw a j hj).target := by
  simpa only [flatteningMap_self] using (strictDeriv_flatteningMap hw a j hj).image_mem_toOpenPartialHomeomorph_target

lemma regularLevelFlatteningChart_symm_zero {w : KernelSpace n → ℝ} (hw : ContDiff ℝ ∞ w)
    (a : KernelSpace n) (j : Fin n)
    (hj : fderiv ℝ w a (EuclideanSpace.basisFun (Fin n) ℝ j) ≠ 0) :
    (regularLevelFlatteningChart hw a j hj).symm 0 = a := by
  have hh := (regularLevelFlatteningChart hw a j hj).left_inv
    (regularLevelFlatteningChart_source hw a j hj)
  simpa only [regularLevelFlatteningChart_apply, flatteningMap_self] using hh

lemma regularLevelFlatteningChart_inverse_contDiffAt {w : KernelSpace n → ℝ}
    (hw : ContDiff ℝ ∞ w) (a : KernelSpace n) (j : Fin n)
    (hj : fderiv ℝ w a (EuclideanSpace.basisFun (Fin n) ℝ j) ≠ 0)
    {z : KernelSpace n} (hz : z ∈ (regularLevelFlatteningChart hw a j hj).target)
    (hn : fderiv ℝ w ((regularLevelFlatteningChart hw a j hj).symm z)
      (EuclideanSpace.basisFun (Fin n) ℝ j) ≠ 0) :
    ContDiffAt ℝ ∞ (regularLevelFlatteningChart hw a j hj).symm z := by
  apply (regularLevelFlatteningChart hw a j hj).contDiffAt_symm hz
    (f₀' := flatteningDerivativeEquiv w ((regularLevelFlatteningChart hw a j hj).symm z) j hn)
  · exact hasFDerivAt_flatteningMap (hw.differentiable (by simp) _) a j
  · exact (contDiff_flatteningMap hw a j).contDiffAt

lemma regularLevelFlatteningChart_inverse_level {w : KernelSpace n → ℝ}
    (hw : ContDiff ℝ ∞ w) (a : KernelSpace n) (j : Fin n)
    (hj : fderiv ℝ w a (EuclideanSpace.basisFun (Fin n) ℝ j) ≠ 0)
    {z : KernelSpace n} (hz : z ∈ (regularLevelFlatteningChart hw a j hj).target) :
    w ((regularLevelFlatteningChart hw a j hj).symm z) = w a - z j := by
  have he := congrArg (fun y : KernelSpace n => y j) ((regularLevelFlatteningChart hw a j hj).right_inv hz)
  simp only [regularLevelFlatteningChart_apply, flatteningMap_normal] at he
  linarith

/-- A real open ball in flattened coordinates has a genuine smooth inverse
and the exact sublevel/half-space correspondence at every point. -/
theorem exists_regularLevelFlattening_inverse_ball {w : KernelSpace n → ℝ}
    (hw : ContDiff ℝ ∞ w) (a : KernelSpace n) (j : Fin n)
    (hj : fderiv ℝ w a (EuclideanSpace.basisFun (Fin n) ℝ j) ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ z ∈ Metric.ball (0 : KernelSpace n) r,
      z ∈ (regularLevelFlatteningChart hw a j hj).target ∧
      ContDiffAt ℝ ∞ (regularLevelFlatteningChart hw a j hj).symm z ∧
      w ((regularLevelFlatteningChart hw a j hj).symm z) = w a - z j := by
  let Ψ := regularLevelFlatteningChart hw a j hj
  have hz : (0 : KernelSpace n) ∈ Ψ.target := regularLevelFlatteningChart_target hw a j hj
  have hi := Ψ.continuousAt_symm hz
  have hc : ContinuousAt (fun z => fderiv ℝ w (Ψ.symm z) (EuclideanSpace.basisFun (Fin n) ℝ j)) 0 :=
    ((hw.continuous_fderiv (by simp)).continuousAt.comp hi).clm_apply continuousAt_const
  have hn : fderiv ℝ w (Ψ.symm 0) (EuclideanSpace.basisFun (Fin n) ℝ j) ≠ 0 := by
    rw [regularLevelFlatteningChart_symm_zero]
    exact hj
  have hev := hc.eventually_ne hn
  obtain ⟨r, hr, hb⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem (Ψ.open_target.mem_nhds hz) hev)
  refine ⟨r, hr, ?_⟩
  intro z hzr
  have hzz := hb hzr
  exact ⟨hzz.1, regularLevelFlatteningChart_inverse_contDiffAt hw a j hj hzz.1 hzz.2,
    regularLevelFlatteningChart_inverse_level hw a j hj hzz.1⟩

end GaussianTilt.MomentMapLinearDirichlet
