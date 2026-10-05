import GaussianTilt.MomentDynamics
import GaussianTilt.CovarianceInequalities

/-!
# Operator-norm derivatives from actual directional moments

This file supplies the finite-dimensional variational bridge. Any quantitative
variance estimate is an explicit intermediate input, not a claimed proof of
Letwin's inequality or of the final covariance bound.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Matrix.Norms.L2Operator

namespace GaussianTilt

lemma symmetric_opNorm_le_of_quadratic {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) {C : ℝ} (hC : 0 ≤ C)
    (hquad : ∀ v : EuclideanSpace ℝ ι, ‖v‖ = 1 →
      |matrixQuadratic A (fun i ↦ v i)| ≤ C) : ‖A‖ ≤ C := by
  have he (i : ι) : |hA.eigenvalues i| ≤ C := by
    have h := hquad (hA.eigenvectorBasis i) (hA.eigenvectorBasis.orthonormal.1 i)
    rw [hA.eigenvalues_eq]
    simpa only [matrixQuadratic, star_trivial, RCLike.re_to_real] using h
  calc
    ‖A‖ = ‖Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)‖ := by
      conv_lhs => rw [hA.spectral_theorem]
      rw [CStarRing.norm_mul_mem_unitary _ (unitary.star_mem _),
        CStarRing.norm_coe_unitary_mul]
      exact hA.eigenvectorUnitary.prop
    _ ≤ C := diagonal_opNorm_le hC he

lemma matrixQuadratic_rankOne {ι : Type*} [Fintype ι] (v x : ι → ℝ) :
    matrixQuadratic (Matrix.vecMulVec v v) x = (v ⬝ᵥ x) ^ 2 := by
  simp only [matrixQuadratic, vecMulVec_mulVec, dotProduct_smul, smul_eq_mul]
  rw [dotProduct_comm x v]
  simp [pow_two, op_smul_eq_smul]

lemma trace_power_eq_sum_eigenvalues_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (k : ℕ) :
    Matrix.trace (A ^ k) = ∑ i, hA.eigenvalues i ^ k := by
  let U : Matrix ι ι ℝ := hA.eigenvectorUnitary
  let D : Matrix ι ι ℝ := diagonal hA.eigenvalues
  have hU : star U * U = 1 := unitary.coe_star_mul_self _
  have hU' : U * star U = 1 := unitary.coe_mul_star_self _
  have hspec : A = U * D * star U := hA.spectral_theorem
  have hp (j : ℕ) : A ^ j = U * D ^ j * star U := by
    induction j with
    | zero => simp only [pow_zero, mul_one, hU']
    | succ j ih =>
      rw [pow_succ, ih, hspec]
      calc
        U * D ^ j * star U * (U * D * star U) =
            U * (D ^ j * (star U * U) * D) * star U := by noncomm_ring
        _ = U * D ^ (j + 1) * star U := by rw [hU, mul_one, pow_succ]
  rw [hp, Matrix.trace_mul_cycle, hU, one_mul]
  simp [D, diagonal_pow, trace_diagonal]

lemma posSemidef_trace_four_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    Matrix.trace (A ^ 4) ≤ ‖A‖ ^ 2 * Matrix.trace (A ^ 2) := by
  rw [trace_power_eq_sum_eigenvalues_pow hA.1,
    trace_power_eq_sum_eigenvalues_pow hA.1, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have he : hA.1.eigenvalues i ≤ ‖A‖ := by
    have h := matrixQuadratic_le_opNorm A (hA.1.eigenvectorBasis i)
    rw [hA.1.eigenvectorBasis.orthonormal.1 i, one_pow, mul_one] at h
    rw [hA.1.eigenvalues_eq]
    simpa only [matrixQuadratic, PiLp.ofLp_apply, star_trivial, RCLike.re_to_real] using h
  have hs := mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (hA.eigenvalues_nonneg i) he 2) (sq_nonneg (hA.1.eigenvalues i))
  nlinarith

lemma trace_rankOne_mul_square {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (v : ι → ℝ) :
    Matrix.trace ((Matrix.vecMulVec v v * M) ^ 2) = matrixQuadratic M v ^ 2 := by
  have h := trace_square_add_rankOne M (0 : Matrix ι ι ℝ) v
  simp only [add_zero, zero_add, mul_zero, zero_mul, zero_pow (by decide : 2 ≠ 0),
    Matrix.trace_zero, Matrix.zero_mulVec, dotProduct_zero, mul_zero] at h
  calc
    Matrix.trace ((Matrix.vecMulVec v v * M) ^ 2) =
        Matrix.trace ((M * Matrix.vecMulVec v v) ^ 2) := by
      simp only [pow_two]
      rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
      congr 1
      noncomm_ring
    _ = matrixQuadratic M v ^ 2 := h

namespace CompactProbability
variable {n : ℕ} (P : CompactProbability n)

lemma momentMatrixDerivative_isHermitian (t : ℝ) :
    (P.momentMatrixDerivative t).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial, momentMatrixDerivative]
  congr 2
  funext x
  ring

lemma quadratic_momentMatrixDerivative (v : Fin n → ℝ) (t : ℝ) :
    matrixQuadratic (P.momentMatrixDerivative t) v =
      -P.covariance t (fun x ↦ (v ⬝ᵥ (fun i ↦ x i)) ^ 2) energy := by
  have hc := P.covariance_matrixQuadratic (Matrix.vecMulVec v v) t
  simp_rw [matrixQuadratic_rankOne] at hc
  rw [hc]
  simp only [matrixQuadratic, dotProduct, Matrix.mulVec, Finset.mul_sum,
    momentMatrixDerivative, vecMulVec_apply, mul_neg, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The norm of the moment derivative is controlled by directional and radial
variance bounds. Both are moments of the actual tilted measure. -/
lemma momentMatrixDerivative_opNorm_le {t A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hdir : ∀ v : Point n, ‖v‖ = 1 →
      ProbabilityTheory.variance (fun x : Point n ↦ ((fun i ↦ v i) ⬝ᵥ (fun i ↦ x i)) ^ 2)
        (P.tilt t) ≤ A ^ 2)
    (hrad : ProbabilityTheory.variance (@energy n) (P.tilt t) ≤ B ^ 2) :
    ‖P.momentMatrixDerivative t‖ ≤ A * B := by
  apply symmetric_opNorm_le_of_quadratic (P.momentMatrixDerivative_isHermitian t)
    (mul_nonneg hA hB)
  intro v hv
  rw [P.quadratic_momentMatrixDerivative, abs_neg,
    P.covariance_eq_probabilityCovariance
      (P.memLp_continuous_tilt (by unfold dotProduct; fun_prop) t 2)
      (P.memLp_continuous_tilt continuous_energy t 2)]
  exact abs_covariance_le_of_variance_bounds
    (P.memLp_continuous_tilt (by unfold dotProduct; fun_prop) t 2)
    (P.memLp_continuous_tilt continuous_energy t 2) hA hB (hdir v hv) hrad

lemma radial_variance_of_quadratic_bound {t : ℝ}
    (hquad : ∀ B : Matrix (Fin n) (Fin n) ℝ, B.IsHermitian →
      ProbabilityTheory.variance (fun x : Point n ↦ matrixQuadratic B (fun i ↦ x i))
        (P.tilt t) ≤ 10 * Matrix.trace ((B * P.momentMatrix t) ^ 2)) :
    ProbabilityTheory.variance (@energy n) (P.tilt t) ≤ 10 * P.momentHSSquare t := by
  have hpoint (x : Point n) : matrixQuadratic (1 : Matrix (Fin n) (Fin n) ℝ)
      (fun i ↦ x i) = energy x := by
    simp only [matrixQuadratic, Matrix.one_mulVec, dotProduct, energy_eq_sum_sq, pow_two]
  have h := hquad 1 Matrix.isHermitian_one
  simpa only [hpoint, one_mul, ← P.momentHSSquare_eq_trace_square] using h

lemma directional_variance_of_quadratic_bound {t : ℝ}
    (hquad : ∀ B : Matrix (Fin n) (Fin n) ℝ, B.IsHermitian →
      ProbabilityTheory.variance (fun x : Point n ↦ matrixQuadratic B (fun i ↦ x i))
        (P.tilt t) ≤ 10 * Matrix.trace ((B * P.momentMatrix t) ^ 2))
    (v : Point n) (hv : ‖v‖ = 1) :
    ProbabilityTheory.variance (fun x : Point n ↦ ((fun i ↦ v i) ⬝ᵥ (fun i ↦ x i)) ^ 2)
        (P.tilt t) ≤ 10 * ‖P.momentMatrix t‖ ^ 2 := by
  have hrank : (Matrix.vecMulVec (fun i ↦ v i) (fun i ↦ v i)).IsHermitian := by
    ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, vecMulVec_apply]
    ring
  have h := hquad _ hrank
  simp_rw [matrixQuadratic_rankOne, trace_rankOne_mul_square] at h
  have hM : (P.momentMatrix t).PosSemidef :=
    secondMomentMatrix_posSemidef (fun i ↦ P.memLp_continuous_tilt (by fun_prop) t 2)
  have hq : 0 ≤ matrixQuadratic (P.momentMatrix t) (fun i ↦ v i) := by
    simpa only [matrixQuadratic, star_trivial] using hM.2 (fun i ↦ v i)
  have hn := matrixQuadratic_le_opNorm (P.momentMatrix t) v
  simp only [hv, one_pow, mul_one] at hn
  exact h.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq hn 2) (by norm_num))

lemma momentDerivative_bound_of_quadratic_bound {t : ℝ}
    (hquad : ∀ B : Matrix (Fin n) (Fin n) ℝ, B.IsHermitian →
      ProbabilityTheory.variance (fun x : Point n ↦ matrixQuadratic B (fun i ↦ x i))
        (P.tilt t) ≤ 10 * Matrix.trace ((B * P.momentMatrix t) ^ 2)) :
    ‖P.momentMatrixDerivative t‖ ≤ 10 * ‖P.momentMatrix t‖ * P.momentHS t := by
  have hs : P.momentHS t ^ 2 = P.momentHSSquare t :=
    Real.sq_sqrt (P.momentHSSquare_nonneg t)
  have h10 : Real.sqrt 10 ^ 2 = (10 : ℝ) := Real.sq_sqrt (by norm_num)
  have h := P.momentMatrixDerivative_opNorm_le
    (t := t) (A := Real.sqrt 10 * ‖P.momentMatrix t‖)
    (B := Real.sqrt 10 * P.momentHS t) (by positivity) (by unfold momentHS; positivity)
    (fun v hv ↦ by
      simpa only [mul_pow, h10] using P.directional_variance_of_quadratic_bound hquad v hv)
    (by simpa only [mul_pow, h10, hs] using P.radial_variance_of_quadratic_bound hquad)
  convert h using 1
  calc
    10 * ‖P.momentMatrix t‖ * P.momentHS t =
        Real.sqrt 10 ^ 2 * ‖P.momentMatrix t‖ * P.momentHS t := by rw [h10]
    _ = Real.sqrt 10 * ‖P.momentMatrix t‖ * (Real.sqrt 10 * P.momentHS t) := by ring

lemma moment_pairing_bound_of_quadratic_bound {t : ℝ}
    (hquad : ∀ B : Matrix (Fin n) (Fin n) ℝ, B.IsHermitian →
      ProbabilityTheory.variance (fun x : Point n ↦ matrixQuadratic B (fun i ↦ x i))
        (P.tilt t) ≤ 10 * Matrix.trace ((B * P.momentMatrix t) ^ 2)) :
    |P.covariance t (fun x ↦ matrixQuadratic (P.momentMatrix t) (fun i ↦ x i)) energy| ≤
      10 * ‖P.momentMatrix t‖ * P.momentHSSquare t := by
  have hH := P.momentHSSquare_nonneg t
  have hM : (P.momentMatrix t).PosSemidef :=
    secondMomentMatrix_posSemidef (fun i ↦ P.memLp_continuous_tilt (by fun_prop) t 2)
  have hq : ProbabilityTheory.variance
      (fun x : Point n ↦ matrixQuadratic (P.momentMatrix t) (fun i ↦ x i)) (P.tilt t) ≤
        10 * ‖P.momentMatrix t‖ ^ 2 * P.momentHSSquare t := by
    calc
      _ ≤ 10 * Matrix.trace ((P.momentMatrix t * P.momentMatrix t) ^ 2) := hquad _ hM.1
      _ = 10 * Matrix.trace (P.momentMatrix t ^ 4) := by congr 2; noncomm_ring
      _ ≤ 10 * (‖P.momentMatrix t‖ ^ 2 * Matrix.trace (P.momentMatrix t ^ 2)) :=
        mul_le_mul_of_nonneg_left (posSemidef_trace_four_le hM) (by norm_num)
      _ = _ := by rw [← P.momentHSSquare_eq_trace_square]; ring
  have hr := P.radial_variance_of_quadratic_bound hquad
  have hc := covariance_sq_le_variance_mul
    (P.memLp_continuous_tilt (f := fun x ↦ matrixQuadratic (P.momentMatrix t) (fun i ↦ x i))
      (by unfold matrixQuadratic Matrix.mulVec dotProduct; fun_prop) t 2)
    (P.memLp_continuous_tilt continuous_energy t 2)
  rw [← P.covariance_eq_probabilityCovariance
    (P.memLp_continuous_tilt (by unfold matrixQuadratic Matrix.mulVec dotProduct; fun_prop) t 2)
    (P.memLp_continuous_tilt continuous_energy t 2)] at hc
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity :
    0 ≤ 10 * ‖P.momentMatrix t‖ * P.momentHSSquare t)).mp
  rw [sq_abs]
  calc
    _ ≤ _ := hc
    _ ≤ (10 * ‖P.momentMatrix t‖ ^ 2 * P.momentHSSquare t) *
        (10 * P.momentHSSquare t) :=
      mul_le_mul hq hr (variance_nonneg _ _) (by positivity)
    _ = _ := by ring

/-- The exact logarithmic HS differential estimate from the genuine quadratic
variance input. This isolates the sole remaining analytic inequality in 3.2. -/
lemma log_momentHS_bound_of_quadratic_bound (hiso : Reference.isotropic P.measure)
    (hn : 0 < n) {t : ℝ}
    (hquad : ∀ B : Matrix (Fin n) (Fin n) ℝ, B.IsHermitian →
      ProbabilityTheory.variance (fun x : Point n ↦ matrixQuadratic B (fun i ↦ x i))
        (P.tilt t) ≤ 10 * Matrix.trace ((B * P.momentMatrix t) ^ 2)) :
    |deriv (fun s ↦ Real.log (P.momentHS s)) t| ≤ 10 * ‖P.momentMatrix t‖ := by
  rw [(P.log_momentHS_derivative hiso hn t).deriv, abs_div, abs_neg,
    abs_of_pos (P.momentHSSquare_pos hiso hn t)]
  exact (div_le_iff₀ (P.momentHSSquare_pos hiso hn t)).mpr
    (P.moment_pairing_bound_of_quadratic_bound hquad)

lemma momentOperatorNorm_rightSlope_of_quadratic_bound {a b : ℝ}
    (hquad : ∀ t ∈ Set.Ico a b, ∀ B : Matrix (Fin n) (Fin n) ℝ, B.IsHermitian →
      ProbabilityTheory.variance (fun x : Point n ↦ matrixQuadratic B (fun i ↦ x i))
        (P.tilt t) ≤ 10 * Matrix.trace ((B * P.momentMatrix t) ^ 2)) :
    UpperDynamics.RightSlopeBound (fun t ↦ ‖P.momentMatrix t‖)
      (fun t ↦ 10 * P.momentHS t * ‖P.momentMatrix t‖) a b := by
  intro t ht r hr
  apply P.momentOperatorNorm_rightSlope a b t ht r
  have h := P.momentDerivative_bound_of_quadratic_bound (hquad t ht)
  nlinarith

end CompactProbability
end GaussianTilt
