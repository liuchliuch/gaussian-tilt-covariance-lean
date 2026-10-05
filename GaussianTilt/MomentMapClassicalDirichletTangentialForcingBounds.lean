import GaussianTilt.MomentMapClassicalDirichletTangentialForcingCalculus

/-! # Genuine scale-weighted bounds for the differentiated tangential forcing -/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

lemma abs_trace_product_le_entry_bounds {A B : Matrix (Fin n) (Fin n) ℝ} {a b : ℝ}
    (ha : 0 ≤ a) (hA : ∀ i j, |A i j| ≤ a) (hB : ∀ i j, |B i j| ≤ b) :
    |(A*B).trace| ≤ (n:ℝ)^2*a*b := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply]
  calc
    _ ≤ ∑ i, ∑ j, |A i j*B j i| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, (a*b) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul (hA i j) (hB j i) (abs_nonneg _) ha
    _ = _ := by simp; ring

lemma scaled_abs_le_of_abs_le {r a C : ℝ} (hr1 : r ≤ 1) (ha : |a| ≤ C) : r*|a| ≤ C :=
  (mul_le_mul_of_nonneg_right hr1 (abs_nonneg _)).trans (by simpa using ha)

/-- The scaled derivative of the literal forcing uses only the scaled
first coefficient derivative, fixed chart derivatives, and actual C² bounds. -/
theorem scaled_tangentialFieldForcing_derivative_bound
    {u F β : CoordinateSpace n → ℝ} (hu : ContDiff ℝ ∞ u)
    (hF : ContDiff ℝ ∞ F) (hβ : ContDiff ℝ ∞ β)
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, Differentiable ℝ (fun x => A x i j))
    (x : CoordinateSpace n) (a j k : Fin n)
    {r I D G H B₀ B₁ B₂ B₃ K₁ K₂ : ℝ}
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hI : 0 ≤ I) (hD : 0 ≤ D) (hG : 0 ≤ G)
    (hH : 0 ≤ H) (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁)
    (hA0 : ∀ i l, |A x i l| ≤ I)
    (hA1 : ∀ i l, r*|matrixCoordinateDerivative A k x i l| ≤ D)
    (hu1 : |coordinateDerivative j u x| ≤ G) (hu2 : |coordinateHessian u x j k| ≤ H)
    (hβ0 : |β x| ≤ B₀) (hβ1 : |coordinateDerivative k β x| ≤ B₁)
    (hβ2 : ∀ i l, |coordinateHessian β x i l| ≤ B₂)
    (hβ3 : ∀ i l, |coordinateThirdDerivative β x i l k| ≤ B₃)
    (hF1 : |coordinateDerivative j F x| ≤ K₁)
    (hF2 : |coordinateHessian F x a k| ≤ K₂) (hF2j : |coordinateHessian F x j k| ≤ K₂) :
    r*|coordinateDerivative k (tangentialFieldForcing A u F β a j) x| ≤
      K₂+B₁*K₁+B₀*K₂+H*((n:ℝ)^2*I*B₂)+G*((n:ℝ)^2*(D*B₂+I*B₃))+2*B₂ := by
  have hL : |linearizedMA (A x) β x| ≤ (n:ℝ)^2*I*B₂ :=
    abs_trace_product_le_entry_bounds hI hA0 hβ2
  have hDL1 : r*|(matrixCoordinateDerivative A k x*coordinateHessian β x).trace| ≤ (n:ℝ)^2*D*B₂ := by
    have hscaled : ∀ i l, |(r • matrixCoordinateDerivative A k x) i l| ≤ D := by
      intro i l
      simpa only [Matrix.smul_apply,smul_eq_mul,abs_mul,abs_of_nonneg hr] using hA1 i l
    have hh := abs_trace_product_le_entry_bounds hD hscaled hβ2
    simpa only [Matrix.smul_mul,Matrix.trace_smul,smul_eq_mul,abs_mul,abs_of_nonneg hr] using hh
  have hDL2 : r*|(A x*matrixCoordinateDerivative (coordinateHessian β) k x).trace| ≤ (n:ℝ)^2*I*B₃ :=
    scaled_abs_le_of_abs_le hr1 (abs_trace_product_le_entry_bounds hI hA0 hβ3)
  have hDL : r*|((matrixCoordinateDerivative A k x*coordinateHessian β x).trace +
      (A x*matrixCoordinateDerivative (coordinateHessian β) k x).trace)| ≤ (n:ℝ)^2*(D*B₂+I*B₃) := by
    have hh := mul_le_mul_of_nonneg_left (abs_add_le
      (matrixCoordinateDerivative A k x*coordinateHessian β x).trace
      (A x*matrixCoordinateDerivative (coordinateHessian β) k x).trace) hr
    nlinarith
  have h1 := scaled_abs_le_of_abs_le hr1 hF2
  have h2 : r*|coordinateDerivative k β x*coordinateDerivative j F x| ≤ B₁*K₁ :=
    scaled_abs_le_of_abs_le hr1 (by rw [abs_mul]; exact mul_le_mul hβ1 hF1 (abs_nonneg _) hB₁)
  have h3 : r*|β x*coordinateHessian F x j k| ≤ B₀*K₂ :=
    scaled_abs_le_of_abs_le hr1 (by rw [abs_mul]; exact mul_le_mul hβ0 hF2j (abs_nonneg _) hB₀)
  have h4 : r*|coordinateHessian u x j k*linearizedMA (A x) β x| ≤ H*((n:ℝ)^2*I*B₂) :=
    scaled_abs_le_of_abs_le hr1 (by rw [abs_mul]; exact mul_le_mul hu2 hL (abs_nonneg _) hH)
  have h5 : r*|coordinateDerivative j u x*
      ((matrixCoordinateDerivative A k x*coordinateHessian β x).trace+
        (A x*matrixCoordinateDerivative (coordinateHessian β) k x).trace)| ≤ G*((n:ℝ)^2*(D*B₂+I*B₃)) := by
    rw [abs_mul]
    have hh := mul_le_mul hu1 hDL (mul_nonneg hr (abs_nonneg _)) hG
    nlinarith
  have h6 : r*|2*coordinateHessian β x j k| ≤ 2*B₂ :=
    scaled_abs_le_of_abs_le hr1 (by rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]; exact mul_le_mul_of_nonneg_left (hβ2 j k) (by norm_num))
  rw [coordinateDerivative_tangentialFieldForcing hu hF hβ hA]
  have ha1 := abs_sub (coordinateHessian F x a k) (coordinateDerivative k β x*coordinateDerivative j F x)
  have ha2 := abs_sub (coordinateHessian F x a k-coordinateDerivative k β x*coordinateDerivative j F x)
    (β x*coordinateHessian F x j k)
  have ha3 := abs_sub (coordinateHessian F x a k-coordinateDerivative k β x*coordinateDerivative j F x-
    β x*coordinateHessian F x j k) (coordinateHessian u x j k*linearizedMA (A x) β x)
  have ha4 := abs_sub (coordinateHessian F x a k-coordinateDerivative k β x*coordinateDerivative j F x-
    β x*coordinateHessian F x j k-coordinateHessian u x j k*linearizedMA (A x) β x)
    (coordinateDerivative j u x*((matrixCoordinateDerivative A k x*coordinateHessian β x).trace+
      (A x*matrixCoordinateDerivative (coordinateHessian β) k x).trace))
  have ha5 := abs_sub (coordinateHessian F x a k-coordinateDerivative k β x*coordinateDerivative j F x-
    β x*coordinateHessian F x j k-coordinateHessian u x j k*linearizedMA (A x) β x-
    coordinateDerivative j u x*((matrixCoordinateDerivative A k x*coordinateHessian β x).trace+
      (A x*matrixCoordinateDerivative (coordinateHessian β) k x).trace)) (2*coordinateHessian β x j k)
  have hh := mul_le_mul_of_nonneg_left (show
      |coordinateHessian F x a k-coordinateDerivative k β x*coordinateDerivative j F x-
        β x*coordinateHessian F x j k-coordinateHessian u x j k*linearizedMA (A x) β x-
        coordinateDerivative j u x*((matrixCoordinateDerivative A k x*coordinateHessian β x).trace+
          (A x*matrixCoordinateDerivative (coordinateHessian β) k x).trace)-2*coordinateHessian β x j k| ≤
      |coordinateHessian F x a k|+|coordinateDerivative k β x*coordinateDerivative j F x|+
        |β x*coordinateHessian F x j k|+|coordinateHessian u x j k*linearizedMA (A x) β x|+
        |coordinateDerivative j u x*((matrixCoordinateDerivative A k x*coordinateHessian β x).trace+
          (A x*matrixCoordinateDerivative (coordinateHessian β) k x).trace)|+|2*coordinateHessian β x j k| by linarith) hr
  nlinarith

lemma tangentialFieldForcing_abs_bound
    {u F β : CoordinateSpace n → ℝ}
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    (x : CoordinateSpace n) (a j : Fin n) {I G B₀ B₁ B₂ K : ℝ}
    (hI : 0 ≤ I) (hG : 0 ≤ G) (hB₀ : 0 ≤ B₀)
    (hA : ∀ i l, |A x i l| ≤ I)
    (hu : |coordinateDerivative j u x| ≤ G) (hβ0 : |β x| ≤ B₀)
    (hβ1 : |coordinateDerivative j β x| ≤ B₁)
    (hβ2 : ∀ i l, |coordinateHessian β x i l| ≤ B₂)
    (hFa : |coordinateDerivative a F x| ≤ K) (hFj : |coordinateDerivative j F x| ≤ K) :
    |tangentialFieldForcing A u F β a j x| ≤ K+B₀*K+G*((n:ℝ)^2*I*B₂)+2*B₁ := by
  have hL : |linearizedMA (A x) β x| ≤ (n:ℝ)^2*I*B₂ := abs_trace_product_le_entry_bounds hI hA hβ2
  have hp : |β x*coordinateDerivative j F x| ≤ B₀*K := by
    rw [abs_mul]
    exact mul_le_mul hβ0 hFj (abs_nonneg _) hB₀
  have hq : |coordinateDerivative j u x*linearizedMA (A x) β x| ≤ G*((n:ℝ)^2*I*B₂) := by
    rw [abs_mul]
    exact mul_le_mul hu hL (abs_nonneg _) hG
  have hs : |2*coordinateDerivative j β x| ≤ 2*B₁ := by
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    exact mul_le_mul_of_nonneg_left hβ1 (by norm_num)
  unfold tangentialFieldForcing
  have h1 := abs_sub (coordinateDerivative a F x) (β x*coordinateDerivative j F x)
  have h2 := abs_sub (coordinateDerivative a F x-β x*coordinateDerivative j F x)
    (coordinateDerivative j u x*linearizedMA (A x) β x)
  have h3 := abs_sub (coordinateDerivative a F x-β x*coordinateDerivative j F x-
    coordinateDerivative j u x*linearizedMA (A x) β x) (2*coordinateDerivative j β x)
  linarith

end GaussianTilt.MomentMapRegularity
