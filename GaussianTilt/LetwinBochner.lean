import GaussianTilt.LetwinMongeAmpere

/-!
# Twice differentiating the Monge--Ampère equation

These identities use actual fourth coordinate derivatives and the actual
inverse-Hessian generator.
-/
noncomputable section
open Matrix MeasureTheory Filter Set
open scoped BigOperators Topology ContDiff
namespace GaussianTilt.Letwin

lemma smooth_coordinateDerivative {n : ℕ} {f : CoordinateSpace n → ℝ}
    (hf : ContDiff ℝ ∞ f) (i : Fin n) : ContDiff ℝ ∞ (coordinateDerivative i f) :=
  contDiff_coordinateDerivative hf (by simp) i

lemma smooth_coordinateHessian {n : ℕ} {f : CoordinateSpace n → ℝ}
    (hf : ContDiff ℝ ∞ f) (i j : Fin n) : ContDiff ℝ ∞ (fun x => coordinateHessian f x i j) :=
  smooth_coordinateDerivative (smooth_coordinateDerivative hf i) j

lemma coordinateDerivative_add {n : ℕ} {f g : CoordinateSpace n → ℝ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (i : Fin n) (x : CoordinateSpace n) :
    coordinateDerivative i (fun y => f y + g y) x =
      coordinateDerivative i f x + coordinateDerivative i g x := by
  unfold coordinateDerivative
  rw [fderiv_fun_add (hf x) (hg x)]
  rfl

lemma coordinateDerivative_neg {n : ℕ} (f : CoordinateSpace n → ℝ) (i : Fin n) (x : CoordinateSpace n) :
    coordinateDerivative i (fun y => -f y) x = -coordinateDerivative i f x := by
  simp only [coordinateDerivative, fderiv_fun_neg, ContinuousLinearMap.neg_apply]

lemma coordinateDerivative_commute {n : ℕ} {f : CoordinateSpace n → ℝ}
    (hf : ContDiff ℝ 2 f) (i j : Fin n) :
    coordinateDerivative i (coordinateDerivative j f) = coordinateDerivative j (coordinateDerivative i f) := by
  funext x
  exact (coordinateHessian_isSymm hf x).apply i j

/-- The fourth-derivative interchange needed when the differentiated
Monge--Ampère equation is written as a diffusion of a Hessian entry. -/
lemma fourth_coordinateDerivative_exchange {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (a b i j : Fin n) :
    coordinateDerivative b (coordinateDerivative a (coordinateDerivative j (coordinateDerivative i φ))) =
      coordinateDerivative j (coordinateDerivative i (coordinateDerivative b (coordinateDerivative a φ))) := by
  have hi := smooth_coordinateDerivative hφ i
  have hai := smooth_coordinateDerivative hi a
  have ha := smooth_coordinateDerivative hφ a
  rw [coordinateDerivative_commute (contDiff_infty.mp hi 2) a j,
    coordinateDerivative_commute (contDiff_infty.mp hai 2) b j,
    coordinateDerivative_commute (contDiff_infty.mp hφ 2) a i,
    coordinateDerivative_commute (contDiff_infty.mp ha 2) b i]

lemma matrixCoordinateDerivative_hessian_exchange {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (i j : Fin n) (x : CoordinateSpace n) :
    matrixCoordinateDerivative (fun y => matrixCoordinateDerivative (coordinateHessian φ) i y) j x =
      coordinateHessian (fun y => coordinateHessian φ y i j) x := by
  ext a b
  exact congrFun (fourth_coordinateDerivative_exchange hφ a b i j).symm x

lemma coordinateThirdDerivative_cycle {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 3 φ) (x : CoordinateSpace n) (a i j : Fin n) :
    coordinateThirdDerivative φ x a i j = coordinateThirdDerivative φ x i j a := by
  rw [coordinateThirdDerivative_symm (hφ.of_le (by norm_num)) x a i j,
    coordinateThirdDerivative_swap_last hφ x i a j]

lemma coordinateDerivative_trace {n : ℕ}
    {H : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hH : ∀ a b, Differentiable ℝ (fun x => H x a b)) (j : Fin n) (x : CoordinateSpace n) :
    coordinateDerivative j (fun y => Matrix.trace (H y)) x =
      Matrix.trace (matrixCoordinateDerivative H j x) := by
  change coordinateDerivative j (fun y => ∑ a, H y a a) x = ∑ a, _
  rw [coordinateDerivative_sum (fun a y => H y a a) (fun a => hH a a)]
  rfl

/-- The second derivative of log det Hessian in its trace form. -/
theorem second_logdet_trace_identity {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hdet : ∀ x, (coordinateHessian φ x).det ≠ 0)
    (i j : Fin n) (x : CoordinateSpace n) :
    coordinateDerivative j (fun y => Matrix.trace
      (inverseHessian φ y * matrixCoordinateDerivative (coordinateHessian φ) i y)) x =
      -Matrix.trace (inverseHessian φ x * matrixCoordinateDerivative (coordinateHessian φ) j x *
        inverseHessian φ x * matrixCoordinateDerivative (coordinateHessian φ) i x) +
      Matrix.trace (inverseHessian φ x * coordinateHessian (fun y => coordinateHessian φ y i j) x) := by
  have hφ3 : ContDiff ℝ 3 φ := contDiff_infty.mp hφ 3
  have hA := fun a b => (contDiff_inverseHessian hφ3 hdet a b).differentiable le_rfl
  have hDH (a b : Fin n) : Differentiable ℝ
      (fun y => matrixCoordinateDerivative (coordinateHessian φ) i y a b) :=
    (smooth_coordinateDerivative (smooth_coordinateHessian hφ a b) i).differentiable (by simp)
  have hprod (a b : Fin n) : Differentiable ℝ
      (fun y => (inverseHessian φ y * matrixCoordinateDerivative (coordinateHessian φ) i y) a b) := by
    simp only [Matrix.mul_apply]
    apply Differentiable.fun_sum
    intro k _
    exact (hA a k).mul (hDH k b)
  rw [coordinateDerivative_trace hprod,
    matrixCoordinateDerivative_mul hA hDH]
  change Matrix.trace (matrixCoordinateDerivative (fun y => (coordinateHessian φ y)⁻¹) j x *
      matrixCoordinateDerivative (coordinateHessian φ) i x +
      inverseHessian φ x * matrixCoordinateDerivative
        (fun y => matrixCoordinateDerivative (coordinateHessian φ) i y) j x) = _
  rw [matrixCoordinateDerivative_inv (contDiff_coordinateHessian hφ3) hdet,
    matrixCoordinateDerivative_hessian_exchange hφ i j x]
  simp only [Matrix.trace_add, Matrix.neg_mul, Matrix.trace_neg, inverseHessian]

/-- Letwin Lemma 2.4, in matrix-trace form. Every derivative and the generator
is the actual analytic one. This identity does not require convexity of V;
convexity is used later for the sign of its Hessian term. -/
theorem mongeAmpere_hessian_equation {n : ℕ} {φ V : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ)
    (hV : ∀ y, DifferentiableAt ℝ V (coordinateGradient φ y))
    (hDV : ∀ a y, DifferentiableAt ℝ (coordinateDerivative a V) (coordinateGradient φ y))
    (hdet : ∀ x, (coordinateHessian φ x).det ≠ 0)
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x + V (coordinateGradient φ x))
    (i j : Fin n) (x : CoordinateSpace n) :
    divergenceDiffusion φ (inverseHessian φ) (fun y => coordinateHessian φ y i j) x +
      coordinateHessian φ x i j =
      (coordinateHessian φ x * coordinateHessian V (coordinateGradient φ x) * coordinateHessian φ x) i j +
      Matrix.trace (inverseHessian φ x * matrixCoordinateDerivative (coordinateHessian φ) j x *
        inverseHessian φ x * matrixCoordinateDerivative (coordinateHessian φ) i x) := by
  have hφ2 : ContDiff ℝ 2 φ := contDiff_infty.mp hφ 2
  have hφ3 : ContDiff ℝ 3 φ := contDiff_infty.mp hφ 3
  have hgrad : Differentiable ℝ (coordinateGradient φ) := differentiable_pi.mpr
    (fun a => (smooth_coordinateDerivative hφ a).differentiable (by simp))
  have hvd (a : Fin n) : Differentiable ℝ
      (fun y => coordinateDerivative a V (coordinateGradient φ y)) :=
    fun y => (hDV a y).comp y (hgrad y)
  have hHd (a b : Fin n) : Differentiable ℝ (fun y => coordinateHessian φ y a b) :=
    (smooth_coordinateHessian hφ a b).differentiable (by simp)
  have hsum : Differentiable ℝ (fun y => ∑ a,
      coordinateDerivative a V (coordinateGradient φ y) * coordinateHessian φ y a i) := by
    apply Differentiable.fun_sum
    intro a _
    exact (hvd a).mul (hHd a i)
  have hvchain (a : Fin n) :
      coordinateDerivative j (fun y => coordinateDerivative a V (coordinateGradient φ y)) x =
        ∑ b, coordinateHessian V (coordinateGradient φ x) a b * coordinateHessian φ x b j :=
    coordinateDerivative_comp_gradient hφ2 (fun y => hDV a y) j x
  have hcycle (a : Fin n) : coordinateDerivative j (fun y => coordinateHessian φ y a i) x =
      coordinateDerivative a (fun y => coordinateHessian φ y i j) x :=
    coordinateThirdDerivative_cycle hφ3 x a i j
  have hmatrix : (∑ a, (∑ b, coordinateHessian V (coordinateGradient φ x) a b * coordinateHessian φ x b j) *
      coordinateHessian φ x a i) =
      (coordinateHessian φ x * coordinateHessian V (coordinateGradient φ x) * coordinateHessian φ x) i j := by
    rw [Matrix.mul_assoc]
    simp only [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro a _
    rw [(coordinateHessian_isSymm hφ2 x).apply i a]
    ring
  have hright : coordinateDerivative j (fun y => -coordinateDerivative i φ y +
      ∑ a, coordinateDerivative a V (coordinateGradient φ y) * coordinateHessian φ y a i) x =
      -coordinateHessian φ x i j +
      (coordinateHessian φ x * coordinateHessian V (coordinateGradient φ x) * coordinateHessian φ x) i j +
      ∑ a, coordinateDerivative a V (coordinateGradient φ x) *
        coordinateDerivative a (fun y => coordinateHessian φ y i j) x := by
    rw [coordinateDerivative_add (f := fun y => -coordinateDerivative i φ y)
      ((smooth_coordinateDerivative hφ i).differentiable (by simp)).neg hsum,
      coordinateDerivative_neg]
    rw [coordinateDerivative_sum
      (fun a y => coordinateDerivative a V (coordinateGradient φ y) * coordinateHessian φ y a i)
      (fun a => (hvd a).mul (hHd a i))]
    simp only [coordinateDerivative_mul (hvd _) (hHd _ _), hvchain,
      Finset.sum_add_distrib, hcycle, hmatrix]
    change -coordinateHessian φ x i j + (_ + _) = _
    ring
  have heq : (fun y => Matrix.trace
      (inverseHessian φ y * matrixCoordinateDerivative (coordinateHessian φ) i y)) =
      (fun y => -coordinateDerivative i φ y +
        ∑ a, coordinateDerivative a V (coordinateGradient φ y) * coordinateHessian φ y a i) :=
    funext fun y => differentiated_mongeAmpere hφ3 hV hdet hMA i y
  have hdiff := congrArg (fun F : CoordinateSpace n → ℝ => coordinateDerivative j F x) heq
  dsimp only at hdiff
  rw [second_logdet_trace_identity hφ hdet i j x, hright] at hdiff
  rw [mongeAmpere_generator_formula hφ3 hV
    (contDiff_infty.mp (smooth_coordinateHessian hφ i j) 2) hdet hMA]
  linarith

end GaussianTilt.Letwin
