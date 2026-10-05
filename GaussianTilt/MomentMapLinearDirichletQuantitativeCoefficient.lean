import GaussianTilt.MomentMapLinearDirichletQuantitativeCoefficientCalculus
import GaussianTilt.MomentMapLinearDirichletQuantitativeChartMatrices

/-! # Uniform transformed coefficients in a fixed genuine boundary chart

The radius is the physical radius `c*s*y j` constructed from the flattened
height. All constants precede the unknown coefficient field.
-/
noncomputable section
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 1000
open Matrix Set Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapRegularity GaussianTilt.Letwin
variable {n : ℕ}

def scaledRawChartCoefficient {w : KernelSpace n → ℝ} (hw : ContDiff ℝ ∞ w)
    (a : KernelSpace n) (j : Fin n)
    (hj : fderiv ℝ w a (EuclideanSpace.basisFun (Fin n) ℝ j) ≠ 0) (s : ℝ)
    (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ) (y : CoordinateSpace n) :
    Matrix (Fin n) (Fin n) ℝ :=
  scaledRawChartJacobian hw a j hj s y*A (scaledRawInverseChart hw a j hj s y)*
    (scaledRawChartJacobian hw a j hj s y)ᵀ

lemma raw_square_sum_eq_norm (v : CoordinateSpace n) :
    (∑ i, v i^2)=‖(coordinateEquiv n).symm v‖^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs,sq_abs]
  rfl

lemma contDiffAt_scaledRawChartCoefficient {w : KernelSpace n → ℝ} (hw : ContDiff ℝ ∞ w)
    (a : KernelSpace n) (j : Fin n)
    (hj : fderiv ℝ w a (EuclideanSpace.basisFun (Fin n) ℝ j) ≠ 0) (s : ℝ)
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {y : CoordinateSpace n}
    (hX : ContDiffAt ℝ ∞ (scaledRawInverseChart hw a j hj s) y)
    (hJ : ∀ i k, ContDiffAt ℝ ∞ (fun z => scaledRawChartJacobian hw a j hj s z i k) y)
    (hA : ∀ i k, ContDiffAt ℝ ∞ (fun x => A x i k) (scaledRawInverseChart hw a j hj s y))
    (i k : Fin n) :
    ContDiffAt ℝ ∞ (fun z => scaledRawChartCoefficient hw a j hj s A z i k) y := by
  unfold scaledRawChartCoefficient
  simp only [Matrix.mul_apply,Matrix.transpose_apply]
  apply ContDiffAt.sum
  intro l _
  apply ContDiffAt.mul
  · apply ContDiffAt.sum
    intro p _
    exact (hJ i p).mul ((hA p l).comp y hX)
  · exact hJ k l

/-- Actual pointwise chart transfer. The only unknown-field inputs are its
original ellipticity and its derivative bound at the physical interior
radius. The chart and inverse derivatives here are the genuine ones. -/
theorem scaled_raw_chart_coefficient_bounds_at {w : KernelSpace n → ℝ}
    (hw : ContDiff ℝ ∞ w) (a : KernelSpace n) (j : Fin n)
    (hj : fderiv ℝ w a (EuclideanSpace.basisFun (Fin n) ℝ j) ≠ 0)
    (hn : 0 < n) {s c C Cx Cj lam Λ K : ℝ}
    (hs : 0 < s) (hc : 0 < c) (hC : 0 < C) (hCx : 0 ≤ Cx) (hCj : 0 ≤ Cj)
    (hlam : 0 ≤ lam) (hΛ : 0 ≤ Λ) (hK : 0 ≤ K)
    {y : CoordinateSpace n} (hyj : 0 < y j) (hyj1 : y j ≤ 1)
    (hInv : s • (coordinateEquiv n).symm y ∈ (regularLevelFlatteningChart hw a j hj).target)
    (hInvSmooth : DifferentiableAt ℝ (regularLevelFlatteningChart hw a j hj).symm
      (s • (coordinateEquiv n).symm y))
    (hInvBound : ‖fderiv ℝ (regularLevelFlatteningChart hw a j hj).symm
      (s • (coordinateEquiv n).symm y)‖ ≤ C)
    (hForward : ‖fderiv ℝ (flatteningMap w a j)
      ((regularLevelFlatteningChart hw a j hj).symm (s • (coordinateEquiv n).symm y))‖ ≤ C)
    (hX : DifferentiableAt ℝ (scaledRawInverseChart hw a j hj s) y)
    (hDX : ‖fderiv ℝ (scaledRawInverseChart hw a j hj s) y‖ ≤ Cx)
    (hJ : ∀ i k, DifferentiableAt ℝ (fun z => scaledRawChartJacobian hw a j hj s z i k) y)
    (hJb : ∀ i k, |scaledRawChartJacobian hw a j hj s y i k| ≤ Cj)
    (hDJb : ∀ k i l, |matrixCoordinateDerivative (scaledRawChartJacobian hw a j hj s) k y i l| ≤ Cj)
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hA : (A (scaledRawInverseChart hw a j hj s y)).PosDef)
    (hAd : ∀ i k, DifferentiableAt ℝ (fun x => A x i k) (scaledRawInverseChart hw a j hj s y))
    (hEll : ∀ v : CoordinateSpace n,
      lam*‖(coordinateEquiv n).symm v‖^2 ≤ v ⬝ᵥ (A (scaledRawInverseChart hw a j hj s y)*ᵥv) ∧
      v ⬝ᵥ (A (scaledRawInverseChart hw a j hj s y)*ᵥv) ≤ Λ*‖(coordinateEquiv n).symm v‖^2)
    (hDA : ∀ k i l, (c*s*y j)*|matrixCoordinateDerivative A k (scaledRawInverseChart hw a j hj s y) i l| ≤ K) :
    (scaledRawChartCoefficient hw a j hj s A y).PosDef ∧
    (∀ v : CoordinateSpace n,
      (lam/((n:ℝ)^2*C^2))*‖(coordinateEquiv n).symm v‖^2 ≤
        v ⬝ᵥ (scaledRawChartCoefficient hw a j hj s A y*ᵥv) ∧
      v ⬝ᵥ (scaledRawChartCoefficient hw a j hj s A y*ᵥv) ≤
        (Λ*((n:ℝ)^2*C^2))*‖(coordinateEquiv n).symm v‖^2) ∧
    (∀ k i l, y j*|matrixCoordinateDerivative (scaledRawChartCoefficient hw a j hj s A) k y i l| ≤
      (n:ℝ)^2*Cj^2*(2*Λ+(n:ℝ)*K*Cx/(c*s))) := by
  let X := scaledRawInverseChart hw a j hj s
  let J := scaledRawChartJacobian hw a j hj s
  let Ac := fun z => A (X z)
  obtain ⟨hJG,hJm,hGm⟩ := regularLevel_chart_matrix_bounds hw a j hj hInv hInvSmooth hInvBound hForward
  have hEll' := matrix_congruence_ellipticity (A (X y)) (J y)
    (euclideanCLMMatrix (fderiv ℝ (regularLevelFlatteningChart hw a j hj).symm (s • (coordinateEquiv n).symm y)))
    hC hn hlam hΛ hJG hJm hGm
    (fun v => by rw [raw_square_sum_eq_norm]; exact (hEll v).1)
    (fun v => by rw [raw_square_sum_eq_norm]; exact (hEll v).2)
  have hAc (i k : Fin n) : DifferentiableAt ℝ (fun z => Ac z i k) y := (hAd i k).comp y hX
  have hAb : ∀ i k, |Ac y i k| ≤ Λ := by
    apply abs_entry_le_of_posSemidef_diagonal_bound hA.posSemidef
    intro i
    have hh := (hEll (Pi.single i 1)).2
    rw [← raw_square_sum_eq_norm] at hh
    simpa [Matrix.mulVec_single_one,single_dotProduct,Matrix.col,Pi.single_apply] using hh
  have hDc (k i l : Fin n) : y j*|matrixCoordinateDerivative Ac k y i l| ≤
      (n:ℝ)*K*Cx/(c*s) := by
    have hh := weighted_coordinateDerivative_comp_bound (hAd i l) hX
      (mul_nonneg (mul_nonneg hc.le hs.le) hyj.le) hK hCx (fun k => hDA k i l) hDX k
    apply (le_div_iff₀ (mul_pos hc hs)).mpr
    change (y j*|coordinateDerivative k (fun z => A (X z) i l) y|)*(c*s) ≤ _
    convert hh using 1 <;> ring
  refine ⟨matrix_congruence_posDef hA hJG,?_,?_⟩
  · intro v
    simpa only [raw_square_sum_eq_norm] using hEll' v
  · intro k i l
    exact weighted_matrix_congruence_derivative_bound hJ hAc hyj.le hyj1 hCj hΛ
      (by positivity) hJb hDJb hAb hDc k i l

end GaussianTilt.MomentMapLinearDirichlet
