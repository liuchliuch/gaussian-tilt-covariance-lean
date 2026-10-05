import GaussianTilt.PositiveCovariance
import GaussianTilt.PaperResults
import GaussianTilt.UpperDynamics

/-!
# Actual moment-matrix trajectories and their Hilbert--Schmidt derivative

All objects below are built from genuine Gaussian-tilt moments. Their
regularity and positivity are derived, not supplied as flow hypotheses.
-/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators Matrix.Norms.L2Operator

namespace GaussianTilt.CompactProbability
variable {n : ℕ} (P : CompactProbability n)

def momentMatrix (t : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  secondMomentMatrix (P.tilt t) (fun x : Point n ↦ fun i ↦ x i)

def momentMatrixDerivative (t : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ -P.covariance t (fun x ↦ x i * x j) energy

def momentHSSquare (t : ℝ) : ℝ := ∑ i, ∑ j, P.momentMatrix t i j ^ 2

def momentHS (t : ℝ) : ℝ := Real.sqrt (P.momentHSSquare t)

lemma momentMatrix_hasDerivAt (t : ℝ) :
    HasDerivAt P.momentMatrix (P.momentMatrixDerivative t) t := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  exact P.hasDerivAt_secondMoment_entry t i j

lemma momentMatrix_continuous : Continuous P.momentMatrix :=
  continuous_iff_continuousAt.mpr fun t ↦ (P.momentMatrix_hasDerivAt t).continuousAt

lemma momentMatrixDerivative_continuous : Continuous P.momentMatrixDerivative := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (P.continuous_covariance (P.integrable_continuous (by fun_prop))
    P.integrable_energy (P.integrable_continuous (by unfold energy; fun_prop))).neg

lemma momentHSSquare_nonneg (t : ℝ) : 0 ≤ P.momentHSSquare t :=
  Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ sq_nonneg _

lemma momentHSSquare_eq_trace_square (t : ℝ) :
    P.momentHSSquare t = Matrix.trace (P.momentMatrix t ^ 2) := by
  have hsym := (secondMomentMatrix_posSemidef
    (fun i ↦ P.memLp_continuous_tilt (f := fun x : Point n ↦ x i) (by fun_prop) t 2)).1
  have heq (i j : Fin n) : P.momentMatrix t j i = P.momentMatrix t i j := by
    exact congrArg (fun A : Matrix (Fin n) (Fin n) ℝ ↦ A i j) hsym
  simp only [momentHSSquare, Matrix.trace, Matrix.diag, pow_two, Matrix.mul_apply, heq]

lemma momentHSSquare_pos (hiso : Reference.isotropic P.measure) (hn : 0 < n) (t : ℝ) :
    0 < P.momentHSSquare t := by
  apply lt_of_le_of_ne (P.momentHSSquare_nonneg t)
  intro hz
  have hzero : P.momentMatrix t = 0 := by
    ext i j
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun k (_ : k ∈ Finset.univ) ↦
        Finset.sum_nonneg (fun l (_ : l ∈ Finset.univ) ↦ sq_nonneg (P.momentMatrix t k l)))).mp hz.symm i (Finset.mem_univ i)
    have hij := (Finset.sum_eq_zero_iff_of_nonneg
      (fun l (_ : l ∈ Finset.univ) ↦ sq_nonneg (P.momentMatrix t i l))).mp hi j (Finset.mem_univ j)
    exact sq_eq_zero_iff.mp hij
  have hnorm := P.secondMoment_opNorm_pos hiso hn t
  change 0 < ‖P.momentMatrix t‖ at hnorm
  simpa only [hzero, norm_zero, lt_self_iff_false] using hnorm

lemma momentHS_pos (hiso : Reference.isotropic P.measure) (hn : 0 < n) (t : ℝ) :
    0 < P.momentHS t := Real.sqrt_pos.mpr (P.momentHSSquare_pos hiso hn t)

lemma momentHSSquare_hasDerivAt (t : ℝ) :
    HasDerivAt P.momentHSSquare
      (2 * ∑ i, ∑ j, P.momentMatrix t i j * P.momentMatrixDerivative t i j) t := by
  have h := HasDerivAt.sum (u := Finset.univ) (fun i _ ↦
    HasDerivAt.sum (u := Finset.univ) (fun j _ ↦
      (P.hasDerivAt_secondMoment_entry t i j).pow 2))
  convert h using 1
  · funext s
    simp only [momentHSSquare, momentMatrix, secondMomentMatrix, Finset.sum_apply, Pi.pow_apply]
    rfl
  · simp only [momentMatrix, secondMomentMatrix, momentMatrixDerivative, Nat.cast_ofNat,
      Nat.reduceSub, pow_one, Finset.mul_sum, mul_assoc]
    rfl

lemma momentHS_hasDerivAt (hiso : Reference.isotropic P.measure) (hn : 0 < n) (t : ℝ) :
    HasDerivAt P.momentHS
      ((∑ i, ∑ j, P.momentMatrix t i j * P.momentMatrixDerivative t i j) /
        P.momentHS t) t := by
  have h := (P.momentHSSquare_hasDerivAt t).sqrt (ne_of_gt (P.momentHSSquare_pos hiso hn t))
  convert h using 1
  dsimp only [momentHS]
  field_simp

lemma log_momentHS_hasDerivAt (hiso : Reference.isotropic P.measure) (hn : 0 < n) (t : ℝ) :
    HasDerivAt (fun s ↦ Real.log (P.momentHS s))
      ((∑ i, ∑ j, P.momentMatrix t i j * P.momentMatrixDerivative t i j) /
        P.momentHSSquare t) t := by
  have h := (P.momentHS_hasDerivAt hiso hn t).log (ne_of_gt (P.momentHS_pos hiso hn t))
  convert h using 1
  rw [div_div, ← pow_two]
  dsimp only [momentHS]
  rw [Real.sq_sqrt (P.momentHSSquare_nonneg t)]

lemma covariance_eq_probabilityCovariance {f g : Point n → ℝ}
    (hf : MemLp f 2 (P.tilt t)) (hg : MemLp g 2 (P.tilt t)) :
    P.covariance t f g = ProbabilityTheory.covariance f g (P.tilt t) := by
  rw [ProbabilityTheory.covariance_eq_sub hf hg]
  simp only [covariance, P.integral_tilt, Pi.mul_apply]

lemma covariance_matrixQuadratic (B : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    P.covariance t (fun x ↦ matrixQuadratic B (fun i ↦ x i)) energy =
      ∑ i, ∑ j, B i j * P.covariance t (fun x ↦ x i * x j) energy := by
  have hpoint (x : Point n) : matrixQuadratic B (fun i ↦ x i) =
      ∑ i, ∑ j, B i j * (x i * x j) := by
    simp only [matrixQuadratic, dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hpoint]
  have he := P.memLp_continuous_tilt continuous_energy t 2
  have hx (i j : Fin n) := P.memLp_continuous_tilt
    (f := fun x : Point n ↦ x i * x j) (by fun_prop) t 2
  rw [P.covariance_eq_probabilityCovariance
    (P.memLp_continuous_tilt (by fun_prop) t 2) he]
  rw [ProbabilityTheory.covariance_fun_sum_left
    (fun i ↦ P.memLp_continuous_tilt (by fun_prop) t 2) he]
  apply Finset.sum_congr rfl
  intro i _
  rw [ProbabilityTheory.covariance_fun_sum_left
    (fun j ↦ (hx i j).const_mul (B i j)) he]
  apply Finset.sum_congr rfl
  intro j _
  rw [ProbabilityTheory.covariance_mul_left,
    P.covariance_eq_probabilityCovariance (hx i j) he]

lemma momentDerivative_pairing (t : ℝ) :
    (∑ i, ∑ j, P.momentMatrix t i j * P.momentMatrixDerivative t i j) =
      -P.covariance t (fun x ↦ matrixQuadratic (P.momentMatrix t) (fun i ↦ x i)) energy := by
  rw [P.covariance_matrixQuadratic]
  simp only [momentMatrixDerivative, mul_neg, Finset.sum_neg_distrib]

/-- The exact logarithmic Hilbert--Schmidt flow underlying Lemma 3.2. -/
lemma log_momentHS_derivative (hiso : Reference.isotropic P.measure) (hn : 0 < n) (t : ℝ) :
    HasDerivAt (fun s ↦ Real.log (P.momentHS s))
      (-P.covariance t (fun x ↦ matrixQuadratic (P.momentMatrix t) (fun i ↦ x i)) energy /
        P.momentHSSquare t) t := by
  simpa only [P.momentDerivative_pairing] using P.log_momentHS_hasDerivAt hiso hn t

/-- Right-slope control of the actual operator norm needs no differentiability
of the top eigenvector and no spectral nonmultiplicity assumption. -/
lemma momentOperatorNorm_rightSlope (a b : ℝ) :
    UpperDynamics.RightSlopeBound (fun t ↦ ‖P.momentMatrix t‖)
      (fun t ↦ ‖P.momentMatrixDerivative t‖) a b := by
  intro t ht r hr
  exact (P.momentMatrix_hasDerivAt t).hasDerivWithinAt.liminf_right_slope_norm_le hr

end GaussianTilt.CompactProbability
