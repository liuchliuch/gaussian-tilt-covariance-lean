import GaussianTilt.MomentMapClassicalDirichletBoundaryAtlas
import GaussianTilt.MomentMapClassicalDirichletGeometryEllipticity
import GaussianTilt.LetwinMomentJacobian

/-! # Actual chart tangential blocks and uniform inverse control -/
noncomputable section
open Set Filter Matrix
open scoped Topology ContDiff BigOperators Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

abbrev TangentIndex (j : Fin n) := {a : Fin n // a ≠ j}

def chartTangentVector (w : CoordinateSpace n → ℝ) (j a : Fin n) (x : CoordinateSpace n) :
    CoordinateSpace n := (Pi.single a 1 : CoordinateSpace n) - boundaryChartCoefficient w j a x • (Pi.single j 1 : CoordinateSpace n)

def chartTangentMatrix (w : CoordinateSpace n → ℝ) (j : Fin n) (x : CoordinateSpace n) :
    Matrix (Fin n) (TangentIndex j) ℝ := fun i a => chartTangentVector w j a x i

def chartTangentBlock (w : CoordinateSpace n → ℝ) (j : Fin n) (x : CoordinateSpace n) :
    Matrix (TangentIndex j) (TangentIndex j) ℝ :=
  (chartTangentMatrix w j x)ᵀ * coordinateHessian w x * chartTangentMatrix w j x

lemma chartTangentMatrix_mulVec_apply (w : CoordinateSpace n → ℝ) (j : Fin n)
    (x : CoordinateSpace n) (c : TangentIndex j → ℝ) (a : TangentIndex j) :
    (chartTangentMatrix w j x *ᵥ c) a = c a := by
  simp only [Matrix.mulVec, dotProduct, chartTangentMatrix, chartTangentVector,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, a.property, if_false, mul_zero, sub_zero]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b hb hba
    have hne : (b : Fin n) ≠ a := fun h => hba (Subtype.ext h)
    simp [hne, Ne.symm hne]
  · simp

lemma chartTangentMatrix_mulVec_injective (w : CoordinateSpace n → ℝ) (j : Fin n)
    (x : CoordinateSpace n) : Function.Injective (chartTangentMatrix w j x).mulVec := by
  intro c d h
  funext a
  have hh := congrFun h (a : Fin n)
  simpa only [chartTangentMatrix_mulVec_apply] using hh

lemma chartTangentBlock_posDef {w : CoordinateSpace n → ℝ} {x : CoordinateSpace n}
    (hH : (coordinateHessian w x).PosDef) (j : Fin n) : (chartTangentBlock w j x).PosDef := by
  simpa only [chartTangentBlock, Matrix.conjTranspose_eq_transpose_of_trivial] using
    hH.conjTranspose_mul_mul_same (chartTangentMatrix_mulVec_injective w j x)

lemma chartTangentVector_tangent {w : CoordinateSpace n → ℝ} {j : Fin n} {x : CoordinateSpace n}
    (hj : coordinateDerivative j w x ≠ 0) (a : Fin n) :
    fderiv ℝ w x (chartTangentVector w j a x) = 0 := by
  simp only [chartTangentVector, map_sub, map_smul, smul_eq_mul]
  change coordinateDerivative a w x - boundaryChartCoefficient w j a x * coordinateDerivative j w x = 0
  simp [boundaryChartCoefficient, div_mul_cancel₀ _ hj]

lemma secondFDeriv_eq_hessianBilinear {f : CoordinateSpace n → ℝ} {x : CoordinateSpace n}
    (hf : ContDiffAt ℝ 2 f x) (v z : CoordinateSpace n) :
    fderiv ℝ (fderiv ℝ f) x v z = v ⬝ᵥ (coordinateHessian f x *ᵥ z) := by
  have hv : (∑ i, v i • (Pi.single i 1 : CoordinateSpace n)) = v := by ext i; simp [Pi.single_apply]
  have hz : (∑ i, z i • (Pi.single i 1 : CoordinateSpace n)) = z := by ext i; simp [Pi.single_apply]
  conv_lhs => rw [← hv, ← hz]
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, coordinateHessian_eq_secondFDerivAt hf]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hf.isSymmSndFDerivAt (by simp) (Pi.single i 1) (Pi.single j 1)]
  ring

lemma chartTangentBlock_apply {w : CoordinateSpace n → ℝ} {x : CoordinateSpace n}
    (hw : ContDiffAt ℝ 2 w x) (j : Fin n) (a b : TangentIndex j) :
    chartTangentBlock w j x a b =
      fderiv ℝ (fderiv ℝ w) x (chartTangentVector w j a x) (chartTangentVector w j b x) := by
  rw [secondFDeriv_eq_hessianBilinear hw]
  simp only [chartTangentBlock, Matrix.mul_apply, Matrix.transpose_apply, chartTangentMatrix,
    dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro l _
  ring

lemma continuousOn_chartTangentBlock {w : CoordinateSpace n → ℝ} (hw : ContDiff ℝ ∞ w)
    (p : BoundaryChartPatch w) :
    ContinuousOn (chartTangentBlock w p.index) (Metric.closedBall p.center p.radius) := by
  have hT : ContinuousOn (chartTangentMatrix w p.index) (Metric.closedBall p.center p.radius) := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro a y hy
    change ContinuousWithinAt (fun y => (Pi.single (a : Fin n) (1 : ℝ) : CoordinateSpace n) i -
      boundaryChartCoefficient w p.index a y * (Pi.single p.index (1 : ℝ) : CoordinateSpace n) i)
      (Metric.closedBall p.center p.radius) y
    exact continuousWithinAt_const.sub ((p.smooth y hy a).continuousAt.continuousWithinAt.mul continuousWithinAt_const)
  have hTH : ContinuousOn (fun x => (chartTangentMatrix w p.index x)ᵀ * coordinateHessian w x)
      (Metric.closedBall p.center p.radius) :=
    (continuous_fst.matrix_mul continuous_snd).comp_continuousOn
      (((continuous_id.matrix_transpose).comp_continuousOn hT).prodMk
        (continuous_coordinateHessian (contDiff_infty.mp hw 2)).continuousOn)
  exact (continuous_fst.matrix_mul continuous_snd).comp_continuousOn (hTH.prodMk hT)

end GaussianTilt.MomentMapRegularity
