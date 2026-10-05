import GaussianTilt.MomentMapBoundaryRegularityCriticalDensity
import GaussianTilt.NegativeSobolevBochner

/-!
# Actual variable-coefficient Bernstein differentiation

These identities retain every coefficient derivative. They apply to the
logarithm of a positive solution after its actual equation is divided by
the solution, and provide the differential input for interior Harnack on
balls where the rescaled coefficient derivatives are controlled.
-/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

lemma coordinateHessian_sum {ι : Type*} [Fintype ι]
    (f : ι → CoordinateSpace n → ℝ) (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (x : CoordinateSpace n) :
    coordinateHessian (fun y => ∑ i, f i y) x = ∑ i, coordinateHessian (f i) x := by
  ext a b
  have he : coordinateDerivative a (fun y => ∑ i, f i y) =
      fun y => ∑ i, coordinateDerivative a (f i) y := by
    funext y
    exact coordinateDerivative_sum f (fun i => (hf i).differentiable (by simp)) a y
  change coordinateDerivative b (coordinateDerivative a (fun y => ∑ i, f i y)) x = _
  rw [he, coordinateDerivative_sum _ (fun i => (smooth_coordinateDerivative (hf i) a).differentiable (by simp))]
  simp only [Matrix.sum_apply, coordinateHessian]

lemma linearizedMA_sum {ι : Type*} [Fintype ι]
    (A : Matrix (Fin n) (Fin n) ℝ) (f : ι → CoordinateSpace n → ℝ)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (x : CoordinateSpace n) :
    linearizedMA A (fun y => ∑ i, f i y) x = ∑ i, linearizedMA A (f i) x := by
  simp only [linearizedMA, coordinateHessian_sum f hf, Matrix.mul_sum, Matrix.trace_sum]

lemma contDiff_gradientSquare {φ : CoordinateSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (gradientSquare φ) := by
  apply ContDiff.sum
  intro i _
  exact (smooth_coordinateDerivative hφ i).pow 2

lemma coordinateDerivative_gradientSquare {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (k : Fin n) (x : CoordinateSpace n) :
    coordinateDerivative k (gradientSquare φ) x =
      2 * ∑ i, coordinateDerivative i φ x * coordinateHessian φ x i k := by
  unfold gradientSquare
  rw [coordinateDerivative_sum _ (fun i => ((smooth_coordinateDerivative hφ i).pow 2).differentiable (by simp))]
  have hp (i : Fin n) : coordinateDerivative k (fun y => (coordinateDerivative i φ y)^2) x =
      2 * coordinateDerivative i φ x * coordinateHessian φ x i k := by
    change (fderiv ℝ (fun y => (coordinateDerivative i φ y)^2) x) (Pi.single k 1) = _
    rw [(((smooth_coordinateDerivative hφ i).differentiable (by simp) x).hasFDerivAt.pow 2).fderiv]
    norm_num [nsmul_eq_mul, coordinateHessian, coordinateDerivative]
  simp_rw [hp]
  simp only [Finset.mul_sum, mul_assoc]

lemma linearizedMA_gradientSquare {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (A : Matrix (Fin n) (Fin n) ℝ) (x : CoordinateSpace n) :
    linearizedMA A (gradientSquare φ) x =
      2 * ∑ k, (coordinateDerivative k φ x * linearizedMA A (coordinateDerivative k φ) x +
        coordinateGradient (coordinateDerivative k φ) x ⬝ᵥ
          (A *ᵥ coordinateGradient (coordinateDerivative k φ) x)) := by
  unfold gradientSquare
  rw [linearizedMA_sum _ _ (fun k => (smooth_coordinateDerivative hφ k).pow 2)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have he : (fun y => (coordinateDerivative k φ y)^2) =
      (fun y => 2 * ((coordinateDerivative k φ y)^2 / 2)) := by funext y; ring
  rw [he, linearizedMA_const_mul_at _
      (((contDiff_infty.mp (smooth_coordinateDerivative hφ k) 2).pow 2).div_const 2).contDiffAt,
    linearizedMA_half_sq_at _ (contDiff_infty.mp (smooth_coordinateDerivative hφ k) 2).contDiffAt]

lemma coordinateDerivative_variable_operator {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, Differentiable ℝ (fun y => A y i j)) (k : Fin n) (x : CoordinateSpace n) :
    coordinateDerivative k (fun y => linearizedMA (A y) φ y) x =
      (matrixCoordinateDerivative A k x * coordinateHessian φ x).trace +
        linearizedMA (A x) (coordinateDerivative k φ) x := by
  unfold linearizedMA
  rw [coordinateDerivative_trace (differentiable_matrix_mul_entries hA
    (fun i j => (smooth_coordinateHessian hφ i j).differentiable (by simp))),
    matrixCoordinateDerivative_mul hA (fun i j => (smooth_coordinateHessian hφ i j).differentiable (by simp)),
    Matrix.trace_add, ← hessian_coordinateDerivative_eq_matrixDerivative hφ]

lemma coordinateDerivative_variable_quadratic
    {g : CoordinateSpace n → CoordinateSpace n} (hg : ∀ i, Differentiable ℝ (fun y => g y i))
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, Differentiable ℝ (fun y => A y i j))
    (k : Fin n) (x : CoordinateSpace n) (hs : (A x).IsSymm) :
    coordinateDerivative k (fun y => g y ⬝ᵥ (A y *ᵥ g y)) x =
      2 * ((fun i => coordinateDerivative k (fun y => g y i) x) ⬝ᵥ (A x *ᵥ g x)) +
        g x ⬝ᵥ (matrixCoordinateDerivative A k x *ᵥ g x) := by
  let dg := fun i => coordinateDerivative k (fun y => g y i) x
  have he : (fun y => g y ⬝ᵥ (A y *ᵥ g y)) =
      fun y => ∑ i, ∑ j, g y i * (A y i j * g y j) := by
    funext y
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  have hdi (i : Fin n) : Differentiable ℝ (fun y => ∑ j, g y i * (A y i j * g y j)) := by
    apply Differentiable.fun_sum
    intro j _
    exact (hg i).mul ((hA i j).mul (hg j))
  rw [he, coordinateDerivative_sum (fun i y => ∑ j, g y i * (A y i j * g y j)) hdi]
  have hdij (i j : Fin n) : Differentiable ℝ (fun y => g y i * (A y i j * g y j)) :=
    (hg i).mul ((hA i j).mul (hg j))
  simp_rw [coordinateDerivative_sum (fun j y => g y _ * (A y _ j * g y j)) (hdij _)]
  have hprod (i j : Fin n) : coordinateDerivative k (fun y => g y i * (A y i j * g y j)) x =
      dg i * (A x i j * g x j) + g x i *
        (coordinateDerivative k (fun y => A y i j) x * g x j + A x i j * dg j) := by
    have hgp : Differentiable ℝ (fun y => A y i j * g y j) := (hA i j).mul (hg j)
    rw [coordinateDerivative_mul (hg i) hgp,
      coordinateDerivative_mul (hA i j) (hg j)]
  simp_rw [hprod]
  have hx : (∑ i, ∑ j, g x i * (A x i j * dg j)) = dg ⬝ᵥ (A x *ᵥ g x) := by
    rw [Finset.sum_comm]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    rw [hs.apply i j]
    ring
  change (∑ i, ∑ j, (dg i * (A x i j * g x j) +
    g x i * (coordinateDerivative k (fun y => A y i j) x * g x j + A x i j * dg j))) = _
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [hx]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, matrixCoordinateDerivative]
  dsimp only [dg]
  ring_nf
  simp only [← Finset.sum_mul]
  ring

/-- Differentiating the logarithmic equation retains the coefficient
variation and the true differentiated source. -/
lemma differentiated_logarithmic_equation {φ h : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, Differentiable ℝ (fun y => A y i j))
    {x : CoordinateSpace n} (hs : (A x).IsSymm)
    (heq : ∀ᶠ y in 𝓝 x, linearizedMA (A y) φ y +
      coordinateGradient φ y ⬝ᵥ (A y *ᵥ coordinateGradient φ y) = h y)
    (k : Fin n) :
    linearizedMA (A x) (coordinateDerivative k φ) x = coordinateDerivative k h x -
      (matrixCoordinateDerivative A k x * coordinateHessian φ x).trace -
      2 * (coordinateGradient (coordinateDerivative k φ) x ⬝ᵥ (A x *ᵥ coordinateGradient φ x)) -
      coordinateGradient φ x ⬝ᵥ (matrixCoordinateDerivative A k x *ᵥ coordinateGradient φ x) := by
  have hL : Differentiable ℝ (fun y => linearizedMA (A y) φ y) := by
    simp only [linearizedMA, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    apply Differentiable.fun_sum
    intro i _
    apply Differentiable.fun_sum
    intro j _
    exact (hA i j).mul ((smooth_coordinateHessian hφ j i).differentiable (by simp))
  have hg (i : Fin n) : Differentiable ℝ (fun y => coordinateGradient φ y i) :=
    (smooth_coordinateDerivative hφ i).differentiable (by simp)
  have hq : Differentiable ℝ (fun y => coordinateGradient φ y ⬝ᵥ (A y *ᵥ coordinateGradient φ y)) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Differentiable.fun_sum
    intro i _
    apply Differentiable.fun_sum
    intro j _
    exact (hg i).mul ((hA i j).mul (hg j))
  have hd := coordinateDerivative_congr_nhds heq k
  rw [coordinateDerivative_add hL hq, coordinateDerivative_variable_operator hφ hA,
    coordinateDerivative_variable_quadratic hg hA k x hs] at hd
  have hcomm : (fun i => coordinateDerivative k (fun y => coordinateGradient φ y i) x) =
      coordinateGradient (coordinateDerivative k φ) x := by
    ext i
    exact congrFun (coordinateDerivative_commute (contDiff_infty.mp hφ 2) k i) x
  rw [hcomm] at hd
  linarith

/-- The true variable-coefficient Bochner identity for a logarithm. -/
theorem bernstein_log_gradient_identity {φ h : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, Differentiable ℝ (fun y => A y i j))
    {x : CoordinateSpace n} (hs : (A x).IsSymm)
    (heq : ∀ᶠ y in 𝓝 x, linearizedMA (A y) φ y +
      coordinateGradient φ y ⬝ᵥ (A y *ᵥ coordinateGradient φ y) = h y) :
    linearizedMA (A x) (gradientSquare φ) x +
      2 * (coordinateGradient φ x ⬝ᵥ (A x *ᵥ coordinateGradient (gradientSquare φ) x)) =
      2 * (∑ k, coordinateGradient (coordinateDerivative k φ) x ⬝ᵥ
        (A x *ᵥ coordinateGradient (coordinateDerivative k φ) x)) -
      2 * (∑ k, coordinateDerivative k φ x *
        (matrixCoordinateDerivative A k x * coordinateHessian φ x).trace) -
      2 * (∑ k, coordinateDerivative k φ x *
        (coordinateGradient φ x ⬝ᵥ (matrixCoordinateDerivative A k x *ᵥ coordinateGradient φ x))) +
      2 * (coordinateGradient φ x ⬝ᵥ coordinateGradient h x) := by
  have hgrad : coordinateGradient (gradientSquare φ) x =
      (2 : ℝ) • (∑ k, coordinateDerivative k φ x • coordinateGradient (coordinateDerivative k φ) x) := by
    ext i
    rw [show coordinateGradient (gradientSquare φ) x i = coordinateDerivative i (gradientSquare φ) x from rfl,
      coordinateDerivative_gradientSquare hφ]
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    rfl
  have hsym (k : Fin n) :
      coordinateGradient φ x ⬝ᵥ (A x *ᵥ coordinateGradient (coordinateDerivative k φ) x) =
        coordinateGradient (coordinateDerivative k φ) x ⬝ᵥ (A x *ᵥ coordinateGradient φ x) := by
    rw [symmetric_dot_mulVec (A x) hs, dotProduct_comm]
  rw [linearizedMA_gradientSquare hφ, hgrad]
  simp_rw [differentiated_logarithmic_equation hφ hA hs heq]
  simp only [Matrix.mulVec_smul, Matrix.mulVec_sum, dotProduct_smul, dotProduct_sum,
    smul_eq_mul]
  simp_rw [hsym]
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.mul_sum, dotProduct, coordinateGradient]
  ring_nf

end GaussianTilt.MomentMapRegularity
