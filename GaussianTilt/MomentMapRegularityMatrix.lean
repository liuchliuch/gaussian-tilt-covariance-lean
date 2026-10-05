import GaussianTilt.LetwinPositivity

/-! # Matrix inequalities in the Monge--Ampère maximum principle

The tangent-plane inequality for log det is proved from the spectral theorem
and the scalar logarithm inequality. It is not supplied as a concavity axiom.
-/
noncomputable section
open Matrix
open scoped BigOperators MatrixOrder
namespace GaussianTilt.MomentMapRegularity
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma log_det_le_trace_sub_card {A : Matrix ι ι ℝ} (hA : A.PosDef) :
    Real.log A.det ≤ A.trace - Fintype.card ι := by
  have he : ∀ i, 0 < hA.isHermitian.eigenvalues i := hA.eigenvalues_pos
  rw [hA.isHermitian.det_eq_prod_eigenvalues, hA.isHermitian.trace_eq_sum_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  rw [Real.log_prod (s := Finset.univ) (f := hA.isHermitian.eigenvalues)
    (fun i _ => (he i).ne')]
  calc
    ∑ i, Real.log (hA.isHermitian.eigenvalues i) ≤
        ∑ i, (hA.isHermitian.eigenvalues i - 1) :=
      Finset.sum_le_sum (fun i _ => Real.log_le_sub_one_of_pos (he i))
    _ = _ := by simp

/-- Klartag's matrix inequality: the true supporting plane of log det
at an arbitrary positive definite matrix. -/
theorem log_det_tangent {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef) :
    Real.log B.det ≤ Real.log A.det + Matrix.trace (A⁻¹ * B) - Fintype.card ι := by
  let R := CFC.sqrt A⁻¹
  have hR : R.PosDef := hA.inv.posDef_sqrt
  have hRR : R * R = A⁻¹ := CFC.sqrt_mul_sqrt_self A⁻¹ hA.inv.posSemidef.nonneg
  have hC : (R * B * R).PosDef := by
    have h := hB.mul_mul_conjTranspose_same (B := R)
      (Matrix.vecMul_injective_iff_isUnit.mpr hR.isUnit)
    simpa only [hR.isHermitian.eq] using h
  have ht : Matrix.trace (R * B * R) = Matrix.trace (A⁻¹ * B) := by
    rw [Matrix.trace_mul_cycle, hRR]
  have hd : (R * B * R).det = A.det⁻¹ * B.det := by
    have hdR := congrArg Matrix.det hRR
    simp only [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv] at hdR
    simp only [Matrix.det_mul]
    calc
      R.det * B.det * R.det = (R.det * R.det) * B.det := by ring
      _ = _ := by rw [hdR]
  have hl : Real.log (R * B * R).det = Real.log B.det - Real.log A.det := by
    rw [hd, Real.log_mul (inv_ne_zero hA.det_pos.ne') hB.det_pos.ne', Real.log_inv]
    ring
  have h := log_det_le_trace_sub_card hC
  rw [ht, hl] at h
  linarith

/-- At a maximum of a source second difference, its Hessian is negative
semidefinite. The resulting determinant comparison is proved here at the
matrix level, ready for the elliptic maximum principle. -/
theorem log_det_second_difference_nonpos {A B C : Matrix ι ι ℝ}
    (hA : A.PosDef) (hB : B.PosDef) (hC : C.PosDef)
    (hmax : ((2 : ℝ) • A - (B + C)).PosSemidef) :
    Real.log B.det + Real.log C.det - 2 * Real.log A.det ≤ 0 := by
  have hB' := log_det_tangent hA hB
  have hC' := log_det_tangent hA hC
  have ht := GaussianTilt.Letwin.trace_mul_nonneg_of_posSemidef A⁻¹
    ((2 : ℝ) • A - (B + C)) hA.inv.posSemidef hmax
  have ht' : 0 ≤ 2 * (Fintype.card ι : ℝ) -
      (Matrix.trace (A⁻¹ * B) + Matrix.trace (A⁻¹ * C)) := by
    simpa only [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_smul,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hA.det_pos.ne'),
      Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one,
      smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat] using ht
  linarith

end GaussianTilt.MomentMapRegularity
