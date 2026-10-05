import GaussianTilt.MomentMapLinearDirichletFlatteningChart

/-! # Actual local second chain rules and flattening curvature terms -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic

lemma secondFrechet_comp_at {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : F → ℝ} {P : E → F} {x : E}
    (hu : ContDiffAt ℝ 2 u (P x)) (hP : ContDiffAt ℝ 2 P x) (v z : E) :
    fderiv ℝ (fderiv ℝ (u ∘ P)) x v z =
      fderiv ℝ (fderiv ℝ u) (P x) (fderiv ℝ P x v) (fderiv ℝ P x z) +
        fderiv ℝ u (P x) (fderiv ℝ (fderiv ℝ P) x v z) := by
  have hud := hu.differentiableAt (by norm_num)
  have hPd := hP.differentiableAt (by norm_num)
  have hDu := (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt le_rfl
  have hDP := (hP.fderiv_right (m := 1) (by norm_num)).differentiableAt le_rfl
  have he : fderiv ℝ (u ∘ P) =ᶠ[𝓝 x] (fun y => (fderiv ℝ u (P y)).comp (fderiv ℝ P y)) := by
    filter_upwards [hP.eventually (by norm_num), hP.continuousAt.tendsto (hu.eventually (by norm_num))] with y hy huy
    change ContDiffAt ℝ 2 u (P y) at huy
    exact fderiv_comp y (huy.differentiableAt (by norm_num)) (hy.differentiableAt (by norm_num))
  rw [he.fderiv_eq, fderiv_clm_comp (c := fun y => fderiv ℝ u (P y)) (d := fderiv ℝ P)
    (hDu.comp x hPd) hDP]
  have hdc : fderiv ℝ (fun y => fderiv ℝ u (P y)) x =
      (fderiv ℝ (fderiv ℝ u) (P x)).comp (fderiv ℝ P x) :=
    (hDu.hasFDerivAt.comp x hPd.hasFDerivAt).fderiv
  rw [hdc]
  simp [add_comm]

variable {n : ℕ}

lemma contDiffAt_flatteningMap {m : WithTop ℕ∞} {w : KernelSpace n → ℝ} {x : KernelSpace n}
    (hw : ContDiffAt ℝ m w x) (a : KernelSpace n) (j : Fin n) :
    ContDiffAt ℝ m (flatteningMap w a j) x := by
  unfold flatteningMap
  fun_prop

/-- The flattening's entire curvature is the literal defining Hessian in
its normal coordinate. No coordinate transformation identity is assumed. -/
lemma secondFrechet_flatteningMap_at {w : KernelSpace n → ℝ} {x : KernelSpace n}
    (hw : ContDiffAt ℝ 2 w x) (a : KernelSpace n) (j : Fin n) (v z : KernelSpace n) :
    fderiv ℝ (fderiv ℝ (flatteningMap w a j)) x v z =
      -(fderiv ℝ (fderiv ℝ w) x v z) • (EuclideanSpace.basisFun (Fin n) ℝ j) := by
  have hF := contDiffAt_flatteningMap hw a j
  have hDF := (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt le_rfl
  have hDw := (hw.fderiv_right (m := 1) (by norm_num)).differentiableAt le_rfl
  have he : (fun y => fderiv ℝ (flatteningMap w a j) y z) =ᶠ[𝓝 x]
      (fun y => z + (-fderiv ℝ w y z - z j) • (EuclideanSpace.basisFun (Fin n) ℝ j)) := by
    filter_upwards [hw.eventually (by norm_num)] with y hy
    rw [(hasFDerivAt_flatteningMap (hy.differentiableAt (by norm_num)) a j).fderiv, boundaryRowLinear_apply]
    rfl
  have hcoef := ((hDw.hasFDerivAt.clm_apply (hasFDerivAt_const z x)).neg.sub_const (z j))
  have hfull := (hcoef.smul_const (EuclideanSpace.basisFun (Fin n) ℝ j)).const_add z
  have hval : fderiv ℝ (fun y => fderiv ℝ (flatteningMap w a j) y z) x v =
      fderiv ℝ (fderiv ℝ (flatteningMap w a j)) x v z := by
    rw [fderiv_clm_apply hDF (differentiableAt_const z)]
    simp
  simp only [Pi.neg_apply] at hfull
  rw [← hval, he.fderiv_eq, hfull.fderiv]
  simp

/-- The explicit nonlinear chain rule already includes the transformed
first-order drift term, so it cannot be lost in a formal flattening step. -/
theorem secondFrechet_comp_flattening_at {u w : KernelSpace n → ℝ} {x : KernelSpace n}
    (a : KernelSpace n) (j : Fin n) (hw : ContDiffAt ℝ 2 w x)
    (hu : ContDiffAt ℝ 2 u (flatteningMap w a j x)) (v z : KernelSpace n) :
    fderiv ℝ (fderiv ℝ (u ∘ flatteningMap w a j)) x v z =
      fderiv ℝ (fderiv ℝ u) (flatteningMap w a j x)
        (boundaryRowLinear (-fderiv ℝ w x) j v) (boundaryRowLinear (-fderiv ℝ w x) j z) -
      fderiv ℝ (fderiv ℝ w) x v z *
        fderiv ℝ u (flatteningMap w a j x) (EuclideanSpace.basisFun (Fin n) ℝ j) := by
  rw [secondFrechet_comp_at hu (contDiffAt_flatteningMap hw a j),
    (hasFDerivAt_flatteningMap (hw.differentiableAt (by norm_num)) a j).fderiv,
    secondFrechet_flatteningMap_at hw]
  simp only [map_smul, smul_eq_mul]
  ring

end GaussianTilt.MomentMapLinearDirichlet
