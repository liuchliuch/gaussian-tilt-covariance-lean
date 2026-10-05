import GaussianTilt.MomentMapLinearDirichletFlatteningPullback
import GaussianTilt.MomentMapClassicalDirichletOperator

/-! # Exact local raw-coordinate transfer for the boundary operator -/
noncomputable section
open Matrix Set Filter
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapRegularity GaussianTilt.Letwin
variable {n : ℕ}

lemma secondFrechet_comp_linear_at {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : F → ℝ} (P : E →L[ℝ] F) {x : E} (hu : ContDiffAt ℝ 2 u (P x)) (v z : E) :
    fderiv ℝ (fderiv ℝ (u ∘ P)) x v z =
      fderiv ℝ (fderiv ℝ u) (P x) (P v) (P z) := by
  rw [secondFrechet_comp_at hu P.contDiff.contDiffAt]
  have hp : fderiv ℝ (P : E → F) = fun _ => P := funext (fun _ => P.fderiv)
  rw [hp]
  simp

lemma coordinateDerivative_pullback_at {φ : KernelSpace n → ℝ} {x : KernelSpace n}
    (hφ : DifferentiableAt ℝ φ x) (j : Fin n) :
    coordinateDerivative j (coordinatePullback φ) (coordinateEquiv n x) =
      fderiv ℝ φ x (EuclideanSpace.basisFun (Fin n) ℝ j) := by
  have hh : DifferentiableAt ℝ φ ((coordinateEquiv n).symm (coordinateEquiv n x)) := by simpa using hφ
  unfold coordinateDerivative coordinatePullback
  rw [fderiv_comp _ hh (coordinateEquiv n).symm.differentiableAt,
    (coordinateEquiv n).symm.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.symm_apply_apply,
    ContinuousLinearEquiv.coe_coe, coordinateEquiv_symm_single]

/-- The actual raw nondivergence operator agrees exactly with its Euclidean
version even when the unknown is smooth only near the point. -/
theorem linearizedMA_coordinatePullback_at (A : Matrix (Fin n) (Fin n) ℝ)
    {φ : KernelSpace n → ℝ} {x : KernelSpace n} (hφ : ContDiffAt ℝ 2 φ x) :
    linearizedMA A (coordinatePullback φ) (coordinateEquiv n x) = euclideanEllipticOperator A φ x := by
  have hh : ContDiffAt ℝ 2 φ ((coordinateEquiv n).symm (coordinateEquiv n x)) := by simpa using hφ
  have hraw : ContDiffAt ℝ 2 (coordinatePullback φ) (coordinateEquiv n x) :=
    hh.comp _ (coordinateEquiv n).symm.contDiff.contDiffAt
  simp only [linearizedMA, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    coordinateHessian_eq_secondFDerivAt hraw, euclideanEllipticOperator]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  change fderiv ℝ (fderiv ℝ (φ ∘ (coordinateEquiv n).symm.toContinuousLinearMap))
    (coordinateEquiv n x) (Pi.single i 1) (Pi.single j 1) = _
  rw [secondFrechet_comp_linear_at _ hh]
  simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply,
    coordinateEquiv_symm_single]

/-- Exact local flattening PDE in the raw-coordinate API used by the
intrinsic jets and genuine flat-boundary estimates. -/
theorem linearizedMA_comp_flattening_coordinate_at (A : Matrix (Fin n) (Fin n) ℝ)
    {u w : KernelSpace n → ℝ} {x : KernelSpace n} (a : KernelSpace n) (j : Fin n)
    (hw : ContDiffAt ℝ 2 w x) (hu : ContDiffAt ℝ 2 u (flatteningMap w a j x)) :
    linearizedMA A (coordinatePullback (u ∘ flatteningMap w a j)) (coordinateEquiv n x) =
      linearizedMA (flatteningCoefficient A w j x) (coordinatePullback u)
        (coordinateEquiv n (flatteningMap w a j x)) -
      linearizedMA A (coordinatePullback w) (coordinateEquiv n x) *
        coordinateDerivative j (coordinatePullback u) (coordinateEquiv n (flatteningMap w a j x)) := by
  rw [linearizedMA_coordinatePullback_at A (hu.comp x (contDiffAt_flatteningMap hw a j)),
    linearizedMA_coordinatePullback_at _ hu, linearizedMA_coordinatePullback_at A hw,
    coordinateDerivative_pullback_at (hu.differentiableAt (by norm_num))]
  exact ellipticOperator_comp_flattening_at A a j hw hu

end GaussianTilt.MomentMapLinearDirichlet
