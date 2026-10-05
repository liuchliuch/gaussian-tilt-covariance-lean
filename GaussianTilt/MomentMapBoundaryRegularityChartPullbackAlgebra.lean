import GaussianTilt.MomentMapLinearDirichletQuantitativeChartForward

/-! # Quantitative recovery of intrinsic derivatives through the actual chart -/
noncomputable section
set_option maxHeartbeats 2000000
open Set Filter
open scoped Topology ContDiff BigOperators
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin GaussianTilt.MomentMapLinearDirichlet
variable {n : ℕ}

lemma clm_apply_eq_coordinate_sum (L : CoordinateSpace n →L[ℝ] ℝ) (v : CoordinateSpace n) :
    L v=∑ i, v i*L (Pi.single i 1) := by
  have hv : (∑ i, v i • (Pi.single i 1 : CoordinateSpace n))=v := by
    ext j
    simp [Pi.single_apply]
  calc
    L v=L (∑ i, v i • (Pi.single i 1 : CoordinateSpace n)) := by rw [hv]
    _ = _ := by simp

lemma clm_apply_bound_of_coordinates (L : CoordinateSpace n →L[ℝ] ℝ)
    {D : ℝ} (hD : 0 ≤ D) (hL : ∀ i, |L (Pi.single i 1)| ≤ D) (v : CoordinateSpace n) :
    |L v| ≤ (n:ℝ)*D*‖v‖ := by
  rw [clm_apply_eq_coordinate_sum]
  calc
    _ ≤ ∑ i, |v i*L (Pi.single i 1)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, ‖v‖*D := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul (norm_le_pi_norm v i) (hL i) (abs_nonneg _) (norm_nonneg _)
    _ = _ := by simp; ring

lemma intrinsic_derivative_recovery {L D : CoordinateSpace n →L[ℝ] ℝ}
    {X Y : CoordinateSpace n →L[ℝ] CoordinateSpace n}
    (hChain : D=L.comp X) (hXY : X.comp Y=ContinuousLinearMap.id ℝ (CoordinateSpace n)) :
    D.comp Y=L := by
  rw [hChain,ContinuousLinearMap.comp_assoc,hXY]
  rfl

/-- A derivative Hölder estimate in flat coordinates, together with the
actual inverse derivative identity, controls the original derivative.
The second term is the proved Lipschitz variation of the fixed chart. -/
theorem intrinsic_derivative_difference_bound
    (Lx Lz Dx Dz : CoordinateSpace n →L[ℝ] ℝ)
    (Yx Yz : CoordinateSpace n →L[ℝ] CoordinateSpace n)
    {H B C d α : ℝ} (hH : 0 ≤ H) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hd : 0 ≤ d) (hd1 : d ≤ 1) (hα : 0 < α) (hα1 : α ≤ 1)
    (hrecx : Dx.comp Yx=Lx) (hrecz : Dz.comp Yz=Lz)
    (hDiff : ∀ i, |Dx (Pi.single i 1)-Dz (Pi.single i 1)| ≤ H*d^α)
    (hDz : ‖Dz‖ ≤ B) (hYx : ‖Yx‖ ≤ C) (hDY : ‖Yx-Yz‖ ≤ C*d) (k : Fin n) :
    |Lx (Pi.single k 1)-Lz (Pi.single k 1)| ≤ ((n:ℝ)*H*C+B*C)*d^α := by
  have hEval := clm_apply_bound_of_coordinates (Dx-Dz) (by positivity : 0 ≤ H*d^α)
    (by simpa only [ContinuousLinearMap.sub_apply] using hDiff) (Yx (Pi.single k 1))
  have hYk : ‖Yx (Pi.single k 1)‖ ≤ C := by
    have hh := Yx.le_opNorm (Pi.single k 1)
    rw [Pi.norm_single,norm_one,mul_one] at hh
    exact hh.trans hYx
  have hFirst : |(Dx-Dz) (Yx (Pi.single k 1))| ≤ (n:ℝ)*(H*d^α)*C :=
    hEval.trans (mul_le_mul_of_nonneg_left hYk (by positivity))
  have hSecond : |Dz ((Yx-Yz) (Pi.single k 1))| ≤ B*C*d := by
    have hv := (Yx-Yz).le_opNorm (Pi.single k 1)
    rw [Pi.norm_single,norm_one,mul_one] at hv
    have hh := Dz.le_opNorm ((Yx-Yz) (Pi.single k 1))
    change |Dz ((Yx-Yz) (Pi.single k 1))| ≤ _ at hh
    exact hh.trans (by nlinarith [mul_le_mul hDz (hv.trans hDY) (norm_nonneg _) hB])
  have hpower : d ≤ d^α := by
    by_cases hd0 : d=0
    · simp [hd0,Real.zero_rpow hα.ne']
    · simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge (lt_of_le_of_ne hd (Ne.symm hd0)) hd1 hα1
  have hID : Lx (Pi.single k 1)-Lz (Pi.single k 1)=
      (Dx-Dz) (Yx (Pi.single k 1))+Dz ((Yx-Yz) (Pi.single k 1)) := by
    rw [← hrecx,← hrecz]
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.sub_apply,map_sub]
    ring
  rw [hID]
  have hh := abs_add_le ((Dx-Dz) (Yx (Pi.single k 1))) (Dz ((Yx-Yz) (Pi.single k 1)))
  nlinarith [mul_le_mul_of_nonneg_left hpower (mul_nonneg hB hC)]

/-- Genuine within-domain chain rule for the scaled inverse chart. -/
lemma hasFDerivWithinAt_scaled_raw_chart {w : GaussianTilt.MomentMapElliptic.KernelSpace n → ℝ}
    (hw : ContDiff ℝ ∞ w) (a : GaussianTilt.MomentMapElliptic.KernelSpace n) (j : Fin n)
    (hj : fderiv ℝ w a (EuclideanSpace.basisFun (Fin n) ℝ j) ≠ 0) (s : ℝ)
    {T : CoordinateSpace n → ℝ} {D : CoordinateSpace n → CoordinateSpace n →L[ℝ] ℝ}
    {U V : Set (CoordinateSpace n)} {y : CoordinateSpace n}
    (hD : HasFDerivWithinAt T (D (scaledRawInverseChart hw a j hj s y)) U (scaledRawInverseChart hw a j hj s y))
    (hX : DifferentiableAt ℝ (scaledRawInverseChart hw a j hj s) y)
    (hm : MapsTo (scaledRawInverseChart hw a j hj s) V U) :
    HasFDerivWithinAt (fun z => T (scaledRawInverseChart hw a j hj s z))
      ((D (scaledRawInverseChart hw a j hj s y)).comp (fderiv ℝ (scaledRawInverseChart hw a j hj s) y)) V y :=
  hD.comp y hX.hasFDerivAt.hasFDerivWithinAt hm

end GaussianTilt.MomentMapRegularity
