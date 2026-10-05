import GaussianTilt.MomentMapSchauderEuclideanSource

/-! # Actual finite-difference equations for variable-coefficient linear PDEs -/
noncomputable section
open Matrix Set
open scoped ContDiff BigOperators
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

def matrixDifferenceQuotient (A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ)
    (h : KernelSpace n) (s : ℝ) (x : KernelSpace n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => s⁻¹*(A (x+h) i j-A x i j)

def linearDifferenceForcing (A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ)
    (u f : KernelSpace n → ℝ) (h : KernelSpace n) (s : ℝ) (x : KernelSpace n) : ℝ :=
  vectorDifferenceQuotient f h s x-matrixContraction (matrixDifferenceQuotient A h s x) (euclideanHessianMatrix u x)

/-- Differencing a literal linear PDE gives a literal linear PDE with a
shifted coefficient field. The only error is the exact coefficient
increment contracted with the original Hessian. -/
theorem linear_difference_elliptic_equation {A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ}
    {u f : KernelSpace n → ℝ} (hu : ContDiff ℝ 2 u) (h x : KernelSpace n) (s : ℝ)
    (heqx : euclideanEllipticOperator (A x) u x=f x)
    (heqxh : euclideanEllipticOperator (A (x+h)) u (x+h)=f (x+h)) :
    euclideanEllipticOperator (A (x+h)) (vectorDifferenceQuotient u h s) x =
      linearDifferenceForcing A u f h s x := by
  unfold linearDifferenceForcing
  change euclideanEllipticOperator (A (x+h)) (vectorDifferenceQuotient u h s) x =
    s⁻¹*(f (x+h)-f x)-matrixContraction (matrixDifferenceQuotient A h s x) (euclideanHessianMatrix u x)
  rw [← heqx, ← heqxh]
  simp only [euclideanEllipticOperator, secondFrechet_vectorDifferenceQuotient hu, vectorDifferenceQuotient, matrixContraction, matrixDifferenceQuotient,
    euclideanHessianMatrix, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    smul_eq_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Derivative Hölder bounds give step-uniform coefficient-increment
bounds, using the actual scalar FTC for every entry. -/
theorem matrixDifferenceQuotient_bounds {A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, ContDiff ℝ 1 (fun x => A x i j)) {S T : Set (KernelSpace n)}
    {M H α : ℝ} (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hb : ∀ x ∈ S, ∀ i j, ‖fderiv ℝ (fun z => A z i j) x‖ ≤ M)
    (hh : ∀ x ∈ S, ∀ y ∈ S, ∀ i j,
      ‖fderiv ℝ (fun z => A z i j) x-fderiv ℝ (fun z => A z i j) y‖ ≤ H*‖x-y‖^α)
    (e : KernelSpace n) (he : ‖e‖ ≤ 1) {s : ℝ} (hs : s ≠ 0)
    (hseg : ∀ x ∈ T, ∀ t ∈ Icc (0 : ℝ) 1, x+t • (s • e) ∈ S) :
    (∀ x ∈ T, ∀ i j, |matrixDifferenceQuotient A (s • e) s x i j| ≤ M) ∧
    (∀ x ∈ T, ∀ y ∈ T, ∀ i j,
      |matrixDifferenceQuotient A (s • e) s x i j-matrixDifferenceQuotient A (s • e) s y i j| ≤ H*‖x-y‖^α) := by
  constructor
  · intro x hx i j
    exact (abs_differenceQuotient_le (hA i j) x e hs
      (fun t ht => hb _ (hseg x hx t ht) i j)).trans (mul_le_of_le_one_right hM he)
  · intro x hx y hy i j
    exact (differenceQuotient_holder_bound (hA i j) (fun z hz w hw => hh z hz w hw i j)
      x y e hs (hseg x hx) (hseg y hy)).trans
      (mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hH he) (Real.rpow_nonneg (norm_nonneg _) α))

/-- Explicit forcing bounds for the genuine differenced PDE. Only the
original Hessian, coefficient first derivative, and forcing first derivative
enter, so these constants are independent of the nonzero step. -/
theorem linearDifferenceForcing_bounds {A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ}
    {u f : KernelSpace n → ℝ} {S : Set (KernelSpace n)}
    {M H J Q F G α : ℝ} (hM : 0 ≤ M) (hH : 0 ≤ H) (hJ : 0 ≤ J) (hQ : 0 ≤ Q)
    (hF : 0 ≤ F) (hG : 0 ≤ G) (h : KernelSpace n) (s : ℝ)
    (hAb : ∀ x ∈ S, ∀ i j, |matrixDifferenceQuotient A h s x i j| ≤ M)
    (hAH : ∀ x ∈ S, ∀ y ∈ S, ∀ i j,
      |matrixDifferenceQuotient A h s x i j-matrixDifferenceQuotient A h s y i j| ≤ H*‖x-y‖^α)
    (hHb : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ J)
    (hHH : ∀ x ∈ S, ∀ y ∈ S, ‖fderiv ℝ (fderiv ℝ u) x-fderiv ℝ (fderiv ℝ u) y‖ ≤ Q*‖x-y‖^α)
    (hfb : ∀ x ∈ S, |vectorDifferenceQuotient f h s x| ≤ F)
    (hfH : ∀ x ∈ S, ∀ y ∈ S,
      |vectorDifferenceQuotient f h s x-vectorDifferenceQuotient f h s y| ≤ G*‖x-y‖^α) :
    (∀ x ∈ S, |linearDifferenceForcing A u f h s x| ≤ F+(n : ℝ)^2*M*J) ∧
    (∀ x ∈ S, ∀ y ∈ S,
      |linearDifferenceForcing A u f h s x-linearDifferenceForcing A u f h s y| ≤
        (G+(n : ℝ)^2*(M*Q+H*J))*‖x-y‖^α) := by
  constructor
  · intro x hx
    have hb := abs_matrixContraction_le hM hJ (hAb x hx)
      (fun i j => (abs_euclidean_bilinear_entry_le_norm _ i j).trans (hHb x hx))
    apply (abs_sub _ _).trans
    exact add_le_add (hfb x hx) (by simpa only [Fintype.card_fin] using hb)
  · intro x hx y hy
    have hp := Real.rpow_nonneg (norm_nonneg (x-y)) α
    have hc := abs_matrixContraction_sub_le hM hJ (mul_nonneg hH hp) (mul_nonneg hQ hp)
      (hAb x hx) (fun i j => (abs_euclidean_bilinear_entry_le_norm _ i j).trans (hHb y hy))
      (hAH x hx y hy) (fun i j => (abs_euclidean_bilinear_entry_le_norm
        (fderiv ℝ (fderiv ℝ u) x-fderiv ℝ (fderiv ℝ u) y) i j).trans (hHH x hx y hy))
    have he : linearDifferenceForcing A u f h s x-linearDifferenceForcing A u f h s y =
        (vectorDifferenceQuotient f h s x-vectorDifferenceQuotient f h s y)-
        (matrixContraction (matrixDifferenceQuotient A h s x) (euclideanHessianMatrix u x)-
          matrixContraction (matrixDifferenceQuotient A h s y) (euclideanHessianMatrix u y)) := by
      unfold linearDifferenceForcing
      ring
    rw [he]
    apply (abs_sub _ _).trans
    exact (add_le_add (hfH x hx y hy) hc).trans_eq (by simp only [Fintype.card_fin]; ring)

end GaussianTilt.MomentMapSchauder
