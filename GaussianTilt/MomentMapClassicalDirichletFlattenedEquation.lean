import GaussianTilt.MomentMapClassicalDirichletFlattenedForcingCalculus
import GaussianTilt.MomentMapLinearDirichletFlatteningCoordinates

/-! # Literal rescaled boundary equation, with the full curvature term -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 500000
open Set Filter Matrix
open scoped Topology ContDiff BigOperators
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin GaussianTilt.MomentMapLinearDirichlet GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma coordinateHessian_comp_smul_at {u : CoordinateSpace n → ℝ} (s : ℝ)
    {y : CoordinateSpace n} (hu : ContDiffAt ℝ 2 u (s • y)) :
    coordinateHessian (fun z => u (s • z)) y = s^2 • coordinateHessian u (s • y) := by
  let P : CoordinateSpace n →L[ℝ] CoordinateSpace n := s • ContinuousLinearMap.id ℝ (CoordinateSpace n)
  have hP : ContDiffAt ℝ 2 (fun z : CoordinateSpace n => s • z) y := contDiffAt_const.smul contDiffAt_id
  ext i k
  change coordinateHessian (u ∘ P) y i k = _
  have huP : ContDiffAt ℝ 2 u (P y) := hu
  rw [coordinateHessian_eq_secondFDerivAt (huP.comp y P.contDiff.contDiffAt) i k,Matrix.smul_apply]
  rw [secondFrechet_comp_linear_at P huP,coordinateHessian_eq_secondFDerivAt hu i k]
  simp only [P,ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,map_smul,
    ContinuousLinearMap.smul_apply,smul_eq_mul]
  ring

lemma coordinateDerivative_comp_smul_at {u : CoordinateSpace n → ℝ} (s : ℝ)
    {y : CoordinateSpace n} (hu : DifferentiableAt ℝ u (s • y)) (k : Fin n) :
    coordinateDerivative k (fun z => u (s • z)) y = s*coordinateDerivative k u (s • y) := by
  let P : CoordinateSpace n →L[ℝ] CoordinateSpace n := s • ContinuousLinearMap.id ℝ (CoordinateSpace n)
  change fderiv ℝ (u ∘ P) y (Pi.single k 1) = _
  have huP : DifferentiableAt ℝ u (P y) := hu
  rw [fderiv_comp _ huP P.differentiableAt,P.fderiv]
  simp only [ContinuousLinearMap.comp_apply,P,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply,map_smul,smul_eq_mul,coordinateDerivative]

lemma linearizedMA_comp_smul_at (A : Matrix (Fin n) (Fin n) ℝ)
    {u : CoordinateSpace n → ℝ} (s : ℝ) {y : CoordinateSpace n}
    (hu : ContDiffAt ℝ 2 u (s • y)) :
    linearizedMA A (fun z => u (s • z)) y = s^2*linearizedMA A u (s • y) := by
  simp only [linearizedMA,coordinateHessian_comp_smul_at s hu,Matrix.mul_smul,Matrix.trace_smul,smul_eq_mul]

lemma coordinatePullback_unpullback (u : CoordinateSpace n → ℝ) :
    coordinatePullback (u ∘ (coordinateEquiv n)) = u := by
  funext x
  simp only [coordinatePullback,Function.comp_apply,ContinuousLinearEquiv.apply_symm_apply]

/-- Exact scaled equation for any genuinely local scalar solution in the
actual inverse-function chart. This includes the defining-function drift,
with its correct single scale factor after rescaling. -/
theorem linearizedMA_scaled_flattened_pullback
    {w : KernelSpace n → ℝ} (hw : ContDiff ℝ ∞ w)
    (a : KernelSpace n) (q : Fin n)
    (hq : fderiv ℝ w a (EuclideanSpace.basisFun (Fin n) ℝ q) ≠ 0)
    (s : ℝ) {y : CoordinateSpace n}
    (hz : s • (coordinateEquiv n).symm y ∈ (regularLevelFlatteningChart hw a q hq).target)
    (hn : fderiv ℝ w ((regularLevelFlatteningChart hw a q hq).symm (s • (coordinateEquiv n).symm y))
      (EuclideanSpace.basisFun (Fin n) ℝ q) ≠ 0)
    {T : CoordinateSpace n → ℝ}
    (hT : ContDiffAt ℝ 2 T (coordinateEquiv n
      ((regularLevelFlatteningChart hw a q hq).symm (s • (coordinateEquiv n).symm y))))
    (A : Matrix (Fin n) (Fin n) ℝ) :
    let X := fun z : CoordinateSpace n => coordinateEquiv n
      ((regularLevelFlatteningChart hw a q hq).symm (s • (coordinateEquiv n).symm z))
    linearizedMA (flatteningCoefficient A w q ((coordinateEquiv n).symm (X y))) (T ∘ X) y =
      s^2*linearizedMA A T (X y)+
      s*linearizedMA A (coordinatePullback w) (X y)*coordinateDerivative q (T ∘ X) y := by
  let Ψ := regularLevelFlatteningChart hw a q hq
  let z := s • (coordinateEquiv n).symm y
  let x := Ψ.symm z
  let U : KernelSpace n → ℝ := T ∘ (coordinateEquiv n)
  let v : CoordinateSpace n → ℝ := coordinatePullback (U ∘ Ψ.symm)
  let X := fun z : CoordinateSpace n => coordinateEquiv n (Ψ.symm (s • (coordinateEquiv n).symm z))
  have hx : x ∈ Ψ.source := Ψ.map_target hz
  have hback : Ψ x = z := Ψ.right_inv hz
  have hU : ContDiffAt ℝ 2 U x := hT.comp x (coordinateEquiv n).contDiff.contDiffAt
  have he := ellipticOperator_flattened_pullback hw a q hq hx hn hU A
  change ContDiffAt ℝ 2 (U ∘ Ψ.symm) (Ψ x) ∧
    GaussianTilt.MomentMapSchauder.euclideanEllipticOperator A U x =
    GaussianTilt.MomentMapSchauder.euclideanEllipticOperator (flatteningCoefficient A w q x) (U ∘ Ψ.symm) (Ψ x)-
      GaussianTilt.MomentMapSchauder.euclideanEllipticOperator A w x*
      fderiv ℝ (U ∘ Ψ.symm) (Ψ x) (EuclideanSpace.basisFun (Fin n) ℝ q) at he
  rw [hback] at he
  have hvs : ContDiffAt ℝ 2 v (s • y) := by
    have hh : ContDiffAt ℝ 2 (U ∘ Ψ.symm) z := by simpa only [hback] using he.1
    have hscoord : (coordinateEquiv n).symm (s • y) = z := by simp only [map_smul,z]
    exact (hscoord ▸ hh).comp _ (coordinateEquiv n).symm.contDiff.contDiffAt
  have hvscale : (fun z => v (s • z)) = T ∘ X := by
    funext z
    simp only [v,U,X,coordinatePullback,Function.comp_apply,map_smul]
  have hEq : linearizedMA A T (coordinateEquiv n x) =
      linearizedMA (flatteningCoefficient A w q x) v (s • y)-
      linearizedMA A (coordinatePullback w) (coordinateEquiv n x)*coordinateDerivative q v (s • y) := by
    rw [← coordinatePullback_unpullback T,linearizedMA_coordinatePullback_at A hU]
    have hv : ContDiffAt ℝ 2 (U ∘ Ψ.symm) z := by simpa only [hback] using he.1
    have hsz : coordinateEquiv n z = s • y := by simp only [z,map_smul,ContinuousLinearEquiv.apply_symm_apply]
    rw [← hsz,linearizedMA_coordinatePullback_at _ hv,
      linearizedMA_coordinatePullback_at _ (contDiff_infty.mp hw 2).contDiffAt,
      coordinateDerivative_pullback_at (hv.differentiableAt (by norm_num))]
    simpa only [hback] using he.2
  have hL := linearizedMA_comp_smul_at (flatteningCoefficient A w q x) s hvs
  have hD := coordinateDerivative_comp_smul_at s (hvs.differentiableAt (by norm_num)) q
  rw [hvscale] at hL hD
  change linearizedMA (flatteningCoefficient A w q ((coordinateEquiv n).symm (X y))) (T ∘ X) y =
    s^2*linearizedMA A T (X y)+s*linearizedMA A (coordinatePullback w) (X y)*coordinateDerivative q (T ∘ X) y
  have hxy : X y = coordinateEquiv n x := rfl
  rw [hxy,ContinuousLinearEquiv.symm_apply_apply]
  rw [hL,hD,hEq]
  ring

end GaussianTilt.MomentMapRegularity
