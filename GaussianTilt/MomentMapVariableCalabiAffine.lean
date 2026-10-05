import GaussianTilt.MomentMapCalabiAffine

/-! # Actual affine transfer for variable-density Calabi energy -/
noncomputable section
open Matrix Filter Set
open scoped BigOperators ContDiff Topology
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

lemma adjugate_congruence_scale (H R : Matrix (Fin n) (Fin n) ℝ) :
    R * (Rᵀ * H * R).adjugate * Rᵀ = R.det ^ 2 • H.adjugate := by
  rw [Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib]
  calc
    R * (R.adjugate * (H.adjugate * Rᵀ.adjugate)) * Rᵀ =
        (R * R.adjugate) * H.adjugate * (Rᵀ.adjugate * Rᵀ) := by noncomm_ring
    _ = _ := by
      rw [Matrix.mul_adjugate, Matrix.adjugate_mul, Matrix.det_transpose]
      simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul, pow_two]

lemma cubicMetricEnergy_smul (c : ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (T : Fin n → Fin n → Fin n → ℝ) :
    cubicMetricEnergy (c • A) T = c ^ 3 * cubicMetricEnergy A T := by
  simp only [cubicMetricEnergy, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma calabiAdjugateEnergy_comp_matrix_scale {u : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) (R : Matrix (Fin n) (Fin n) ℝ) (x : CoordinateSpace n) :
    calabiAdjugateEnergy (u ∘ coordinateMatrixMap R) x =
      R.det ^ 6 * calabiAdjugateEnergy u (R *ᵥ x) := by
  unfold calabiAdjugateEnergy
  rw [coordinateHessian_comp_matrix (contDiff_infty.mp hu 2), coordinateThirdDerivative_comp_matrix hu,
    cubicMetricEnergy_affine_invariant _ _ R _ (adjugate_congruence_scale _ R), cubicMetricEnergy_smul]
  congr 1
  ring

def affineLogDensity (F : CoordinateSpace n → ℝ) (R : Matrix (Fin n) (Fin n) ℝ)
    (x : CoordinateSpace n) : ℝ := F (R *ᵥ x) + 2 * Real.log |R.det|

def forcedCalabiEnergy (F u : CoordinateSpace n → ℝ) (x : CoordinateSpace n) : ℝ :=
  Real.exp (-3 * F x) * calabiAdjugateEnergy u x

lemma contDiff_forcedCalabiEnergy {F u : CoordinateSpace n → ℝ}
    (hF : ContDiff ℝ ∞ F) (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (forcedCalabiEnergy F u) :=
  ((contDiff_const.mul hF).exp).mul (contDiff_calabiAdjugateEnergy hu)

/-- The actual scaled energy is invariant under every invertible affine
source matrix, including its non-unit determinant and log-density shift. -/
theorem forcedCalabiEnergy_comp_matrix {F u : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) (R : Matrix (Fin n) (Fin n) ℝ) (hR : R.det ≠ 0) :
    forcedCalabiEnergy (affineLogDensity F R) (u ∘ coordinateMatrixMap R) =
      forcedCalabiEnergy F u ∘ coordinateMatrixMap R := by
  funext x
  unfold forcedCalabiEnergy affineLogDensity
  rw [calabiAdjugateEnergy_comp_matrix_scale hu]
  have he : Real.exp (6 * Real.log |R.det|) = R.det ^ 6 := by
    rw [show (6 : ℝ) * Real.log |R.det| = (6 : ℕ) * Real.log |R.det| by norm_num,
      Real.exp_nat_mul, Real.exp_log (abs_pos.mpr hR)]
    rw [show (6 : ℕ) = 2 * 3 by decide, pow_mul, pow_mul, sq_abs]
  rw [show -3 * (F (R *ᵥ x) + 2 * Real.log |R.det|) =
    -3 * F (R *ᵥ x) - 6 * Real.log |R.det| by ring, Real.exp_sub, he]
  change _ = Real.exp (-3 * F (R *ᵥ x)) * calabiAdjugateEnergy u (R *ᵥ x)
  field_simp

/-- The literal linearized second derivative also transfers, not merely
the value of the cubic energy. -/
theorem linearized_forcedCalabiEnergy_comp_matrix {F u : CoordinateSpace n → ℝ}
    (hF : ContDiff ℝ ∞ F) (hu : ContDiff ℝ ∞ u)
    (A B R : Matrix (Fin n) (Fin n) ℝ) (hR : R.det ≠ 0)
    (hmetric : R * B * Rᵀ = A) (x : CoordinateSpace n) :
    linearizedMA B (forcedCalabiEnergy (affineLogDensity F R) (u ∘ coordinateMatrixMap R)) x =
      linearizedMA A (forcedCalabiEnergy F u) (R *ᵥ x) := by
  rw [forcedCalabiEnergy_comp_matrix hu R hR]
  exact linearizedMA_comp_matrix (contDiff_infty.mp (contDiff_forcedCalabiEnergy hF hu) 2) A B R hmetric x

end GaussianTilt.MomentMapRegularity
