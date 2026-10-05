import GaussianTilt.LetwinTraceEnergy

/-! # Actual Hessian transport under source linear changes -/
noncomputable section
open Matrix Set
open scoped BigOperators ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

lemma coordinateDerivative_comp_linear {φ : CoordinateSpace n → ℝ}
    (hd : Differentiable ℝ φ) (e : CoordinateSpace n →L[ℝ] CoordinateSpace n)
    (i : Fin n) (x : CoordinateSpace n) :
    coordinateDerivative i (φ ∘ e) x =
      ∑ a, e (Pi.single i 1) a * coordinateDerivative a φ (e x) := by
  unfold coordinateDerivative
  rw [fderiv_comp x (hd _) e.differentiableAt, e.fderiv, ContinuousLinearMap.comp_apply]
  exact fderiv_apply_eq_sum_coordinates φ (e x) (e (Pi.single i 1))

lemma coordinateHessian_comp_linear {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (e : CoordinateSpace n →L[ℝ] CoordinateSpace n)
    (x : CoordinateSpace n) (i j : Fin n) :
    coordinateHessian (φ ∘ e) x i j =
      ∑ a, ∑ b, e (Pi.single i 1) a * e (Pi.single j 1) b * coordinateHessian φ (e x) a b := by
  have hd := hφ.differentiable (by norm_num)
  have hD (a : Fin n) : Differentiable ℝ (coordinateDerivative a φ) :=
    (contDiff_coordinateDerivative hφ (m := 1) (by norm_num) a).differentiable le_rfl
  change coordinateDerivative j (coordinateDerivative i (φ ∘ e)) x = _
  rw [show coordinateDerivative i (φ ∘ e) =
      (fun y => ∑ a, e (Pi.single i 1) a * coordinateDerivative a φ (e y)) from
    funext (fun y => coordinateDerivative_comp_linear hd e i y)]
  have hF (a : Fin n) : Differentiable ℝ
      (fun y => e (Pi.single i 1) a * coordinateDerivative a φ (e y)) :=
    ((hD a).comp e.differentiable).const_mul _
  rw [coordinateDerivative_sum (fun a y => e (Pi.single i 1) a * coordinateDerivative a φ (e y)) hF]
  apply Finset.sum_congr rfl
  intro a _
  have hde : Differentiable ℝ (fun y => coordinateDerivative a φ (e y)) :=
    (hD a).comp e.differentiable
  rw [coordinateDerivative_const_mul hde]
  change e (Pi.single i 1) a * coordinateDerivative j (coordinateDerivative a φ ∘ e) x = _
  rw [coordinateDerivative_comp_linear (hD a) e j x, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  change _ = _ * _ * coordinateDerivative b (coordinateDerivative a φ) (e x)
  ring

lemma coordinateHessian_sub_const (φ : CoordinateSpace n → ℝ) (c : ℝ)
    (x : CoordinateSpace n) : coordinateHessian (fun y => φ y - c) x = coordinateHessian φ x := by
  ext i j
  unfold coordinateHessian coordinateDerivative
  simp only [fderiv_sub_const]

/-- Global boundedness of the real Hessian entries survives every continuous
linear source change, with a fully explicit finite-dimensional bound. -/
theorem hessian_bound_comp_linear {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (e : CoordinateSpace n →L[ℝ] CoordinateSpace n)
    {S : ℝ} (hS : ∀ x i j, |coordinateHessian φ x i j| ≤ S) (c : ℝ) :
    ∀ x i j, |coordinateHessian (fun y => φ (e y) - c) x i j| ≤
      (n : ℝ)^2 * max S 0 * ‖e‖^2 := by
  have he (i a : Fin n) : |e (Pi.single i 1) a| ≤ ‖e‖ := by
    calc
      _ ≤ ‖e (Pi.single i 1)‖ := by simpa using norm_le_pi_norm (e (Pi.single i 1)) a
      _ ≤ ‖e‖ * ‖(Pi.single i 1 : CoordinateSpace n)‖ := e.le_opNorm _
      _ = ‖e‖ := by simp [Pi.norm_single]
  intro x i j
  rw [coordinateHessian_sub_const]
  change |coordinateHessian (φ ∘ e) x i j| ≤ _
  rw [coordinateHessian_comp_linear hφ]
  calc
    _ ≤ ∑ a, ∑ b, |e (Pi.single i 1) a * e (Pi.single j 1) b * coordinateHessian φ (e x) a b| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun a _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ _a : Fin n, ∑ _b : Fin n, ‖e‖ * ‖e‖ * max S 0 := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      simp only [abs_mul]
      exact mul_le_mul (mul_le_mul (he i a) (he j b) (abs_nonneg _) (norm_nonneg _))
        ((hS (e x) a b).trans (le_max_left S 0)) (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by simp; ring

end GaussianTilt.MomentMapRegularity
