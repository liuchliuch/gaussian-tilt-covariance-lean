import GaussianTilt.Letwin
import GaussianTilt.FunctionalBrascampLieb

/-! # Diffusion product calculus for the quadratic Hessian trace energy -/
noncomputable section
open Matrix MeasureTheory Filter Set
open scoped BigOperators Topology ContDiff
namespace GaussianTilt.Letwin

lemma weightedCoordinateDivergence_add {n : ℕ} (φ : CoordinateSpace n → ℝ)
    {f g : CoordinateSpace n → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (i : Fin n) (x : CoordinateSpace n) :
    weightedCoordinateDivergence φ (fun y => f y + g y) i x =
      weightedCoordinateDivergence φ f i x + weightedCoordinateDivergence φ g i x := by
  unfold weightedCoordinateDivergence
  rw [coordinateDerivative_add hf hg]
  ring

lemma weightedCoordinateDivergence_mul {n : ℕ} (φ : CoordinateSpace n → ℝ)
    {f g : CoordinateSpace n → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (i : Fin n) (x : CoordinateSpace n) :
    weightedCoordinateDivergence φ (fun y => f y * g y) i x =
      f x * weightedCoordinateDivergence φ g i x + coordinateDerivative i f x * g x := by
  unfold weightedCoordinateDivergence
  rw [coordinateDerivative_mul hf hg]
  ring

lemma diffusionFlux_mul {n : ℕ}
    (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    {f g : CoordinateSpace n → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (i : Fin n) (x : CoordinateSpace n) :
    diffusionFlux A (fun y => f y * g y) i x = f x * diffusionFlux A g i x + g x * diffusionFlux A f i x := by
  simp only [diffusionFlux, coordinateDerivative_mul hf hg, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Equation (2.3) of Letwin for the actual divergence-form operator. -/
theorem divergenceDiffusion_mul {n : ℕ} (φ : CoordinateSpace n → ℝ)
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {f g : CoordinateSpace n → ℝ}
    (hA : ∀ i j, ContDiff ℝ 1 (fun x => A x i j)) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (x : CoordinateSpace n) (hAs : (A x).IsSymm) :
    divergenceDiffusion φ A (fun y => f y * g y) x =
      f x * divergenceDiffusion φ A g x + g x * divergenceDiffusion φ A f x +
        2 * diffusionGamma A f g x := by
  have hfd := hf.differentiable (by norm_num)
  have hgd := hg.differentiable (by norm_num)
  have hflux (i : Fin n) : diffusionFlux A (fun y => f y * g y) i =
      (fun y => f y * diffusionFlux A g i y + g y * diffusionFlux A f i y) :=
    funext (diffusionFlux_mul A hfd hgd i)
  have hFi := fun i => (contDiff_diffusionFlux hA hf i).differentiable le_rfl
  have hGi := fun i => (contDiff_diffusionFlux hA hg i).differentiable le_rfl
  have hrow (i : Fin n) : weightedCoordinateDivergence φ (diffusionFlux A (fun y => f y * g y) i) i x =
      (f x * weightedCoordinateDivergence φ (diffusionFlux A g i) i x + coordinateDerivative i f x * diffusionFlux A g i x) +
      (g x * weightedCoordinateDivergence φ (diffusionFlux A f i) i x + coordinateDerivative i g x * diffusionFlux A f i x) := by
    rw [hflux]
    rw [weightedCoordinateDivergence_add φ
      (f := fun y => f y * diffusionFlux A g i y) (g := fun y => g y * diffusionFlux A f i y)
      (hfd.mul (hGi i)) (hgd.mul (hFi i)),
      weightedCoordinateDivergence_mul φ hfd (hGi i),
      weightedCoordinateDivergence_mul φ hgd (hFi i)]
  simp only [divergenceDiffusion, hrow]
  have heq : (∑ i, ((f x * weightedCoordinateDivergence φ (diffusionFlux A g i) i x +
      coordinateDerivative i f x * diffusionFlux A g i x) +
      (g x * weightedCoordinateDivergence φ (diffusionFlux A f i) i x +
        coordinateDerivative i g x * diffusionFlux A f i x))) =
      f x * (∑ i, weightedCoordinateDivergence φ (diffusionFlux A g i) i x) +
      g x * (∑ i, weightedCoordinateDivergence φ (diffusionFlux A f i) i x) +
      diffusionGamma A g f x + diffusionGamma A f g x := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, diffusionGamma]
    have h₁ : (∑ i, coordinateDerivative i f x * diffusionFlux A g i x) =
        ∑ i, diffusionFlux A g i x * coordinateDerivative i f x := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    have h₂ : (∑ i, coordinateDerivative i g x * diffusionFlux A f i x) =
        ∑ i, diffusionFlux A f i x * coordinateDerivative i g x := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [h₁, h₂]
    ring
  rw [heq, diffusionGamma_symm g f x hAs]
  ring

lemma coordinateDerivative_const_mul {n : ℕ} {f : CoordinateSpace n → ℝ}
    (hf : Differentiable ℝ f) (c : ℝ) (i : Fin n) (x : CoordinateSpace n) :
    coordinateDerivative i (fun y => c * f y) x = c * coordinateDerivative i f x := by
  unfold coordinateDerivative
  rw [((hf x).hasFDerivAt.const_mul c).fderiv]
  rfl

lemma diffusionFlux_sum {n : ℕ} {κ : Type*} [Fintype κ]
    (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ) (F : κ → CoordinateSpace n → ℝ)
    (hF : ∀ k, Differentiable ℝ (F k)) (i : Fin n) (x : CoordinateSpace n) :
    diffusionFlux A (fun y => ∑ k, F k y) i x = ∑ k, diffusionFlux A (F k) i x := by
  simp only [diffusionFlux, coordinateDerivative_sum F hF, Finset.mul_sum]
  rw [Finset.sum_comm]

lemma weightedCoordinateDivergence_sum {n : ℕ} {κ : Type*} [Fintype κ]
    (φ : CoordinateSpace n → ℝ) (F : κ → CoordinateSpace n → ℝ)
    (hF : ∀ k, Differentiable ℝ (F k)) (i : Fin n) (x : CoordinateSpace n) :
    weightedCoordinateDivergence φ (fun y => ∑ k, F k y) i x =
      ∑ k, weightedCoordinateDivergence φ (F k) i x := by
  simp only [weightedCoordinateDivergence, coordinateDerivative_sum F hF,
    Finset.sum_sub_distrib, Finset.mul_sum]

lemma divergenceDiffusion_sum {n : ℕ} {κ : Type*} [Fintype κ]
    (φ : CoordinateSpace n → ℝ) {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, ContDiff ℝ 1 (fun x => A x i j))
    (F : κ → CoordinateSpace n → ℝ) (hF : ∀ k, ContDiff ℝ 2 (F k)) (x : CoordinateSpace n) :
    divergenceDiffusion φ A (fun y => ∑ k, F k y) x = ∑ k, divergenceDiffusion φ A (F k) x := by
  have heq (i : Fin n) : diffusionFlux A (fun y => ∑ k, F k y) i =
      (fun y => ∑ k, diffusionFlux A (F k) i y) :=
    funext (diffusionFlux_sum A F (fun k => (hF k).differentiable (by norm_num)) i)
  simp only [divergenceDiffusion, heq,
    weightedCoordinateDivergence_sum φ _ (fun k => (contDiff_diffusionFlux hA (hF k) _).differentiable le_rfl)]
  rw [Finset.sum_comm]

lemma diffusionFlux_const_mul {n : ℕ}
    (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ) {f : CoordinateSpace n → ℝ}
    (hf : Differentiable ℝ f) (c : ℝ) (i : Fin n) (x : CoordinateSpace n) :
    diffusionFlux A (fun y => c * f y) i x = c * diffusionFlux A f i x := by
  simp only [diffusionFlux, coordinateDerivative_const_mul hf c, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma weightedCoordinateDivergence_const_mul {n : ℕ} (φ : CoordinateSpace n → ℝ)
    {f : CoordinateSpace n → ℝ} (hf : Differentiable ℝ f) (c : ℝ) (i : Fin n) (x : CoordinateSpace n) :
    weightedCoordinateDivergence φ (fun y => c * f y) i x = c * weightedCoordinateDivergence φ f i x := by
  simp only [weightedCoordinateDivergence, coordinateDerivative_const_mul hf c]
  ring

lemma divergenceDiffusion_const_mul {n : ℕ} (φ : CoordinateSpace n → ℝ)
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {f : CoordinateSpace n → ℝ}
    (hA : ∀ i j, ContDiff ℝ 1 (fun x => A x i j)) (hf : ContDiff ℝ 2 f) (c : ℝ) (x : CoordinateSpace n) :
    divergenceDiffusion φ A (fun y => c * f y) x = c * divergenceDiffusion φ A f x := by
  have heq (i : Fin n) : diffusionFlux A (fun y => c * f y) i = (fun y => c * diffusionFlux A f i y) :=
    funext (diffusionFlux_const_mul A (hf.differentiable (by norm_num)) c i)
  simp only [divergenceDiffusion, heq,
    weightedCoordinateDivergence_const_mul φ ((contDiff_diffusionFlux hA hf _).differentiable le_rfl) c,
    Finset.mul_sum]

/-- The diffusion square identity for a finite family of genuine observables. -/
theorem divergenceDiffusion_sum_squares {n : ℕ} {κ : Type*} [Fintype κ]
    (φ : CoordinateSpace n → ℝ) {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, ContDiff ℝ 1 (fun x => A x i j))
    (F : κ → CoordinateSpace n → ℝ) (hF : ∀ k, ContDiff ℝ 2 (F k))
    (x : CoordinateSpace n) (hAs : (A x).IsSymm) :
    divergenceDiffusion φ A (fun y => ∑ k, (F k y)^2) x =
      2 * (∑ k, F k x * divergenceDiffusion φ A (F k) x) +
      2 * (∑ k, diffusionGamma A (F k) (F k) x) := by
  rw [divergenceDiffusion_sum φ hA (fun k y => (F k y)^2) (fun k => (hF k).pow 2)]
  simp only [pow_two, divergenceDiffusion_mul φ hA (hF _) (hF _) x hAs,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

section MatrixFields
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

lemma matrix_conjugate_entry (R H : Matrix κ κ ℝ) (i j : κ) :
    (R * H * R) i j = ∑ a, ∑ b, (R i a * R b j) * H a b := by
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

lemma contDiff_matrix_conjugate {n : ℕ} {k : WithTop ℕ∞}
    (R : Matrix κ κ ℝ) {H : CoordinateSpace n → Matrix κ κ ℝ}
    (hH : ∀ a b, ContDiff ℝ k (fun x => H x a b)) (i j : κ) :
    ContDiff ℝ k (fun x => (R * H x * R) i j) := by
  simp_rw [matrix_conjugate_entry]
  apply ContDiff.sum
  intro a _
  apply ContDiff.sum
  intro b _
  exact contDiff_const.mul (hH a b)

/-- Entrywise application of the actual scalar diffusion. -/
def matrixDiffusion {n : ℕ} (φ : CoordinateSpace n → ℝ)
    (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (H : CoordinateSpace n → Matrix κ κ ℝ) (x : CoordinateSpace n) : Matrix κ κ ℝ :=
  fun i j => divergenceDiffusion φ A (fun y => H y i j) x

lemma matrixDiffusion_conjugate {n : ℕ} (φ : CoordinateSpace n → ℝ)
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, ContDiff ℝ 1 (fun x => A x i j)) (R : Matrix κ κ ℝ)
    {H : CoordinateSpace n → Matrix κ κ ℝ} (hH : ∀ a b, ContDiff ℝ 2 (fun x => H x a b))
    (x : CoordinateSpace n) :
    matrixDiffusion φ A (fun y => R * H y * R) x = R * matrixDiffusion φ A H x * R := by
  ext i j
  change divergenceDiffusion φ A (fun y => (R * H y * R) i j) x = _
  simp_rw [matrix_conjugate_entry]
  rw [divergenceDiffusion_sum φ hA
    (fun a y => ∑ b, (R i a * R b j) * H y a b)
    (fun a => ContDiff.sum (fun b _ => contDiff_const.mul (hH a b)))]
  apply Finset.sum_congr rfl
  intro a _
  rw [divergenceDiffusion_sum φ hA (fun b y => (R i a * R b j) * H y a b)
    (fun b => contDiff_const.mul (hH a b))]
  simp only [divergenceDiffusion_const_mul φ hA (hH _ _), matrixDiffusion]

lemma isSymm_conjugate (R H : Matrix κ κ ℝ) (hR : R.IsSymm) (hH : H.IsSymm) :
    (R * H * R).IsSymm := by
  change (R * H * R).transpose = _
  simp only [Matrix.transpose_mul, hR.eq, hH.eq]
  rw [Matrix.mul_assoc]

/-- The contraction identity behind the quadratic trace energy. -/
lemma conjugate_hs_inner_eq_trace (R H E : Matrix κ κ ℝ) (hR : R.IsSymm) (hH : H.IsSymm) :
    (∑ i, ∑ j, (R * H * R) i j * (R * E * R) i j) =
      Matrix.trace ((R * R) * H * (R * R) * E) := by
  have hF := isSymm_conjugate R H hR hH
  calc
    _ = Matrix.trace ((R * E * R) * (R * H * R)) := by
      change (∑ i, ∑ j, (R * H * R) i j * (R * E * R) i j) =
        ∑ i, ∑ j, (R * E * R) i j * (R * H * R) j i
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hF.apply i j]
      ring
    _ = Matrix.trace (R * (E * (R * R) * H * R)) := by congr 1; noncomm_ring
    _ = Matrix.trace ((E * (R * R) * H * R) * R) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (E * ((R * R) * H * (R * R))) := by congr 1; noncomm_ring
    _ = _ := Matrix.trace_mul_comm _ _

lemma hsSquare_conjugate_eq_trace (R H : Matrix κ κ ℝ) (hR : R.IsSymm) (hH : H.IsSymm) :
    hsSquare (R * H * R) = Matrix.trace ((R * R) * H * (R * R) * H) := by
  simpa only [hsSquare, pow_two] using conjugate_hs_inner_eq_trace R H H hR hH

/-- The complete pointwise diffusion identity for the quadratic norm of a
constant sandwich of a smooth matrix field. -/
theorem divergenceDiffusion_hsSquare_conjugate {n : ℕ} (φ : CoordinateSpace n → ℝ)
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, ContDiff ℝ 1 (fun x => A x i j)) (R : Matrix κ κ ℝ) (hR : R.IsSymm)
    {H : CoordinateSpace n → Matrix κ κ ℝ} (hH : ∀ a b, ContDiff ℝ 2 (fun x => H x a b))
    (x : CoordinateSpace n) (hHx : (H x).IsSymm) (hAs : (A x).IsSymm) :
    divergenceDiffusion φ A (fun y => hsSquare (R * H y * R)) x =
      2 * Matrix.trace ((R * R) * H x * (R * R) * matrixDiffusion φ A H x) +
      2 * (∑ i, ∑ j, diffusionGamma A (fun y => (R * H y * R) i j)
        (fun y => (R * H y * R) i j) x) := by
  have h := divergenceDiffusion_sum_squares φ hA
    (fun p : κ × κ => fun y => (R * H y * R) p.1 p.2)
    (fun p => contDiff_matrix_conjugate R hH p.1 p.2) x hAs
  simp only [Fintype.sum_prod_type] at h
  change divergenceDiffusion φ A (fun y => hsSquare (R * H y * R)) x = _ at h
  have heq (i j : κ) : divergenceDiffusion φ A (fun y => (R * H y * R) i j) x =
      (R * matrixDiffusion φ A H x * R) i j :=
    congrArg (fun M => M i j) (matrixDiffusion_conjugate φ hA R hH x)
  simp_rw [heq] at h
  rw [conjugate_hs_inner_eq_trace R (H x) (matrixDiffusion φ A H x) hR hHx] at h
  exact h

end MatrixFields

/-- The weighted Gram matrix of the actual third derivatives. -/
def thirdHessianGram {n : ℕ} (φ : CoordinateSpace n → ℝ) (x : CoordinateSpace n) :
    Matrix (Fin n) (Fin n) ℝ := fun i j =>
  Matrix.trace (inverseHessian φ x * matrixCoordinateDerivative (coordinateHessian φ) j x *
    inverseHessian φ x * matrixCoordinateDerivative (coordinateHessian φ) i x)

def hessianSandwichSquare {n : ℕ} (R : Matrix (Fin n) (Fin n) ℝ)
    (φ : CoordinateSpace n → ℝ) (x : CoordinateSpace n) : ℝ :=
  hsSquare (R * coordinateHessian φ x * R)

def hessianSandwichEnergy {n : ℕ} (R : Matrix (Fin n) (Fin n) ℝ)
    (φ : CoordinateSpace n → ℝ) (x : CoordinateSpace n) : ℝ :=
  ∑ i, ∑ j, diffusionGamma (inverseHessian φ)
    (fun y => (R * coordinateHessian φ y * R) i j)
    (fun y => (R * coordinateHessian φ y * R) i j) x

def hessianSandwichVTerm {n : ℕ} (R : Matrix (Fin n) (Fin n) ℝ)
    (φ V : CoordinateSpace n → ℝ) (x : CoordinateSpace n) : ℝ :=
  Matrix.trace ((R * R) * coordinateHessian φ x * (R * R) *
    (coordinateHessian φ x * coordinateHessian V (coordinateGradient φ x) * coordinateHessian φ x))

def hessianSandwichThirdTerm {n : ℕ} (R : Matrix (Fin n) (Fin n) ℝ)
    (φ : CoordinateSpace n → ℝ) (x : CoordinateSpace n) : ℝ :=
  Matrix.trace ((R * R) * coordinateHessian φ x * (R * R) * thirdHessianGram φ x)

lemma matrixDiffusion_hessian_eq {n : ℕ} {φ V : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ)
    (hV : ∀ y, DifferentiableAt ℝ V (coordinateGradient φ y))
    (hDV : ∀ a y, DifferentiableAt ℝ (coordinateDerivative a V) (coordinateGradient φ y))
    (hdet : ∀ x, (coordinateHessian φ x).det ≠ 0)
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x + V (coordinateGradient φ x))
    (x : CoordinateSpace n) :
    matrixDiffusion φ (inverseHessian φ) (coordinateHessian φ) x =
      coordinateHessian φ x * coordinateHessian V (coordinateGradient φ x) * coordinateHessian φ x +
        thirdHessianGram φ x - coordinateHessian φ x := by
  ext i j
  have h := mongeAmpere_hessian_equation hφ hV hDV hdet hMA i j x
  simp only [matrixDiffusion, Matrix.sub_apply, Matrix.add_apply, thirdHessianGram]
  linarith

/-- Equation (2.10): the pointwise quadratic trace-energy identity, proved
from the actual diffusion product rule and differentiated Monge--Ampère equation. -/
theorem hessian_trace_energy_identity {n : ℕ} {φ V : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hH : ∀ x, (coordinateHessian φ x).PosDef)
    (hV : ∀ y, DifferentiableAt ℝ V (coordinateGradient φ y))
    (hDV : ∀ a y, DifferentiableAt ℝ (coordinateDerivative a V) (coordinateGradient φ y))
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x + V (coordinateGradient φ x))
    (R : Matrix (Fin n) (Fin n) ℝ) (hR : R.IsSymm) (x : CoordinateSpace n) :
    divergenceDiffusion φ (inverseHessian φ) (hessianSandwichSquare R φ) x + 2 * hessianSandwichSquare R φ x =
      2 * hessianSandwichEnergy R φ x + 2 * hessianSandwichVTerm R φ V x +
        2 * hessianSandwichThirdTerm R φ x := by
  have hφ2 : ContDiff ℝ 2 φ := contDiff_infty.mp hφ 2
  have hφ3 : ContDiff ℝ 3 φ := contDiff_infty.mp hφ 3
  have hdet : ∀ x, (coordinateHessian φ x).det ≠ 0 := fun x => (hH x).det_pos.ne'
  have hAs : (inverseHessian φ x).IsSymm := by
    simpa only [Matrix.IsHermitian, Matrix.IsSymm, Matrix.conjTranspose_eq_transpose_of_trivial]
      using (hH x).inv.isHermitian
  unfold hessianSandwichSquare
  rw [divergenceDiffusion_hsSquare_conjugate φ (contDiff_inverseHessian hφ3 hdet) R hR
    (fun i j => contDiff_infty.mp (smooth_coordinateHessian hφ i j) 2) x (coordinateHessian_isSymm hφ2 x) hAs,
    matrixDiffusion_hessian_eq hφ hV hDV hdet hMA x,
    Matrix.mul_sub, Matrix.mul_add, Matrix.trace_sub, Matrix.trace_add,
    hsSquare_conjugate_eq_trace R (coordinateHessian φ x) hR (coordinateHessian_isSymm hφ2 x)]
  dsimp [hessianSandwichEnergy, hessianSandwichVTerm, hessianSandwichThirdTerm]
  ring

lemma hessianSandwichEnergy_nonneg {n : ℕ} (R : Matrix (Fin n) (Fin n) ℝ)
    (φ : CoordinateSpace n → ℝ) (x : CoordinateSpace n) (hH : (coordinateHessian φ x).PosSemidef) :
    0 ≤ hessianSandwichEnergy R φ x :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    diffusionGamma_nonneg _ x hH.inv

lemma hessianSandwich_remainders_nonneg {n : ℕ} {φ V : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 2 φ) {x : CoordinateSpace n} (hH : (coordinateHessian φ x).PosSemidef)
    {U : Set (CoordinateSpace n)} (hU : IsOpen U) (hVc : ConvexOn ℝ U V)
    (hV : ContDiffOn ℝ 2 V U) (hx : coordinateGradient φ x ∈ U)
    (R : Matrix (Fin n) (Fin n) ℝ) (hR : R.IsSymm) :
    0 ≤ hessianSandwichVTerm R φ V x ∧ 0 ≤ hessianSandwichThirdTerm R φ x := by
  have hB : (R * R).IsSymm := by
    change (R * R).transpose = _
    simp only [Matrix.transpose_mul, hR.eq]
  have hM : ((R * R) * coordinateHessian φ x * (R * R)).PosSemidef := by
    have h := hH.mul_mul_conjTranspose_same (R * R)
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial, hB.eq] at h
  obtain ⟨hP, hQ⟩ := mongeAmpere_hessian_remainders_posSemidef hφ hH hU hVc hV hx
  exact ⟨trace_mul_nonneg_of_posSemidef _ _ hM hP, trace_mul_nonneg_of_posSemidef _ _ hM hQ⟩

lemma contDiff_matrix_mul_entries {n : ℕ} {κ : Type*} [Fintype κ] {k : WithTop ℕ∞}
    {F G : CoordinateSpace n → Matrix κ κ ℝ}
    (hF : ∀ i j, ContDiff ℝ k (fun x => F x i j)) (hG : ∀ i j, ContDiff ℝ k (fun x => G x i j))
    (i j : κ) : ContDiff ℝ k (fun x => (F x * G x) i j) := by
  simp only [Matrix.mul_apply]
  exact ContDiff.sum (fun a _ => (hF i a).mul (hG a j))

lemma contDiff_matrix_trace_entries {n : ℕ} {κ : Type*} [Fintype κ] {k : WithTop ℕ∞}
    {F : CoordinateSpace n → Matrix κ κ ℝ} (hF : ∀ i j, ContDiff ℝ k (fun x => F x i j)) :
    ContDiff ℝ k (fun x => Matrix.trace (F x)) := by
  change ContDiff ℝ k (fun x => ∑ i, F x i i)
  exact ContDiff.sum (fun i _ => hF i i)

lemma smooth_hessianSandwichSquare {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (R : Matrix (Fin n) (Fin n) ℝ) :
    ContDiff ℝ ∞ (hessianSandwichSquare R φ) := by
  unfold hessianSandwichSquare hsSquare
  exact ContDiff.sum (fun i _ => ContDiff.sum (fun j _ =>
    (contDiff_matrix_conjugate R (smooth_coordinateHessian hφ) i j).pow 2))

lemma smooth_hessianSandwichEnergy {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hdet : ∀ x, (coordinateHessian φ x).det ≠ 0)
    (R : Matrix (Fin n) (Fin n) ℝ) : ContDiff ℝ ∞ (hessianSandwichEnergy R φ) := by
  unfold hessianSandwichEnergy
  exact ContDiff.sum (fun i _ => ContDiff.sum (fun j _ =>
    smooth_inverseHessian_energy hφ
      (contDiff_matrix_conjugate R (smooth_coordinateHessian hφ) i j) hdet))

lemma smooth_thirdHessianGram {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hdet : ∀ x, (coordinateHessian φ x).det ≠ 0)
    (i j : Fin n) : ContDiff ℝ ∞ (fun x => thirdHessianGram φ x i j) := by
  have hA := smooth_inverseHessian hφ hdet
  have hD (k a b : Fin n) : ContDiff ℝ ∞
      (fun x => matrixCoordinateDerivative (coordinateHessian φ) k x a b) :=
    smooth_coordinateDerivative (smooth_coordinateHessian hφ a b) k
  exact contDiff_matrix_trace_entries
    (contDiff_matrix_mul_entries
      (contDiff_matrix_mul_entries (contDiff_matrix_mul_entries hA (hD j)) hA) (hD i))

lemma smooth_hessianSandwichThirdTerm {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hdet : ∀ x, (coordinateHessian φ x).det ≠ 0)
    (R : Matrix (Fin n) (Fin n) ℝ) : ContDiff ℝ ∞ (hessianSandwichThirdTerm R φ) :=
  contDiff_matrix_trace_entries
    (contDiff_matrix_mul_entries
      (contDiff_matrix_conjugate (R * R) (smooth_coordinateHessian hφ))
      (smooth_thirdHessianGram hφ hdet))

/-- Bounded matrix entries imply a genuine bound on the sandwich-square
observable, by compactness of the finite coordinate cube. -/
lemma hsSquare_conjugate_bounded {Ω κ : Type*} [Fintype κ] [DecidableEq κ]
    (R : Matrix κ κ ℝ) {H : Ω → Matrix κ κ ℝ} (S : ℝ)
    (hH : ∀ x i j, |H x i j| ≤ S) : ∃ C : ℝ, ∀ x, |hsSquare (R * H x * R)| ≤ C := by
  let K : Set (κ × κ → ℝ) := Icc (fun _ => -|S|) (fun _ => |S|)
  let Q : (κ × κ → ℝ) → ℝ := fun z => hsSquare (R * (Matrix.of fun i j => z (i, j)) * R)
  have hQc : Continuous Q := by
    dsimp [Q, hsSquare]
    simp only [Matrix.mul_apply, Matrix.of_apply]
    fun_prop
  have hK : IsCompact K := isCompact_Icc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hQc.continuousOn
  refine ⟨C, fun x => ?_⟩
  have hx : (fun p : κ × κ => H x p.1 p.2) ∈ K := by
    constructor
    · intro p
      exact (abs_le.mp ((hH x p.1 p.2).trans (le_abs_self S))).1
    · intro p
      exact (abs_le.mp ((hH x p.1 p.2).trans (le_abs_self S))).2
  have h := hC _ hx
  simpa only [Q, Matrix.of_apply, Real.norm_eq_abs] using h

lemma hessianSandwichSquare_bounded {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (R : Matrix (Fin n) (Fin n) ℝ) (S : ℝ)
    (hH : ∀ x i j, |coordinateHessian φ x i j| ≤ S) :
    ∃ C : ℝ, ∀ x, |hessianSandwichSquare R φ x| ≤ C :=
  hsSquare_conjugate_bounded R S hH

lemma targetPotential_derivatives_on_gradient {n : ℕ} {φ V : CoordinateSpace n → ℝ}
    {U : Set (CoordinateSpace n)} (hU : IsOpen U) (hV : ContDiffOn ℝ 2 V U)
    (hgrad : ∀ x, coordinateGradient φ x ∈ U) :
    (∀ x, DifferentiableAt ℝ V (coordinateGradient φ x)) ∧
      (∀ a x, DifferentiableAt ℝ (coordinateDerivative a V) (coordinateGradient φ x)) := by
  constructor
  · intro x
    exact (hV.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds (hgrad x))
  · intro a x
    have hDa : ContDiffOn ℝ 1 (coordinateDerivative a V) U :=
      (hV.fderiv_of_isOpen hU (m := 1) (by norm_num)).clm_apply contDiffOn_const
    exact (hDa.differentiableOn le_rfl).differentiableAt (hU.mem_nhds (hgrad x))

/-- Equation (2.11), including the integrability of all nonnegative terms.
The proof applies the proved cutoff/Fatou conservation theorem to the actual
bounded Hessian-sandwich square, then integrates the pointwise identity. -/
theorem integrated_hessian_trace_energy {n : ℕ} {φ V : CoordinateSpace n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ ∞ φ) (hc : ConvexOn ℝ univ φ)
    (hH : ∀ x, (coordinateHessian φ x).PosDef)
    {K U : Set (CoordinateSpace n)} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hgrad : ∀ x, coordinateGradient φ x ∈ K)
    (hV : ContDiffOn ℝ 2 V U) (hVc : ConvexOn ℝ U V)
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x + V (coordinateGradient φ x))
    (S : ℝ) (hHb : ∀ x i j, |coordinateHessian φ x i j| ≤ S)
    (R : Matrix (Fin n) (Fin n) ℝ) (hR : R.IsSymm) :
    Integrable (hessianSandwichSquare R φ) (potentialMeasure φ) ∧
    Integrable (hessianSandwichEnergy R φ) (potentialMeasure φ) ∧
    Integrable (hessianSandwichVTerm R φ V) (potentialMeasure φ) ∧
    Integrable (hessianSandwichThirdTerm R φ) (potentialMeasure φ) ∧
    (∫ x, hessianSandwichSquare R φ x ∂potentialMeasure φ) =
      (∫ x, hessianSandwichEnergy R φ x ∂potentialMeasure φ) +
      (∫ x, hessianSandwichVTerm R φ V x ∂potentialMeasure φ) +
      (∫ x, hessianSandwichThirdTerm R φ x ∂potentialMeasure φ) := by
  let q := hessianSandwichSquare R φ
  let e := hessianSandwichEnergy R φ
  let p := hessianSandwichVTerm R φ V
  let r := hessianSandwichThirdTerm R φ
  let Lq := divergenceDiffusion φ (inverseHessian φ) q
  have hdet : ∀ x, (coordinateHessian φ x).det ≠ 0 := fun x => (hH x).det_pos.ne'
  obtain ⟨hVd, hDV⟩ := targetPotential_derivatives_on_gradient hU hV (fun x => hKU (hgrad x))
  have hid (x : CoordinateSpace n) : Lq x + 2 * q x = 2 * e x + 2 * p x + 2 * r x :=
    hessian_trace_energy_identity hφ hH hVd hDV hMA R hR x
  have he0 (x : CoordinateSpace n) : 0 ≤ e x := hessianSandwichEnergy_nonneg R φ x (hH x).posSemidef
  have hpr0 (x : CoordinateSpace n) : 0 ≤ p x ∧ 0 ≤ r x :=
    hessianSandwich_remainders_nonneg (contDiff_infty.mp hφ 2) (hH x).posSemidef hU hVc hV
      (hKU (hgrad x)) R hR
  have hqc : ContDiff ℝ ∞ q := smooth_hessianSandwichSquare hφ R
  obtain ⟨C, hC⟩ := hessianSandwichSquare_bounded R S hHb
  have hqB : ∀ᵐ x ∂potentialMeasure φ, ‖q x‖ ≤ C := Filter.Eventually.of_forall
    (fun x => by simpa only [Real.norm_eq_abs] using hC x)
  have hsub : ∀ᵐ x ∂potentialMeasure φ, 0 ≤ Lq x + 2 * q x := by
    filter_upwards with x
    linarith [hid x, he0 x, (hpr0 x).1, (hpr0 x).2]
  obtain ⟨hLqi, hLq0⟩ := regular_mongeAmpere_conservation hφ hc hH hK hU hKU hgrad
    (hV.of_le (by norm_num)) hMA hqc 2 C hqB hsub
  have hqi : Integrable q (potentialMeasure φ) := Integrable.of_bound hqc.continuous.aestronglyMeasurable C hqB
  let G := fun x => (Lq x + 2 * q x) / 2
  have hGi : Integrable G (potentialMeasure φ) := (hLqi.add (hqi.const_mul 2)).div_const 2
  have hei : Integrable e (potentialMeasure φ) := by
    apply hGi.mono' (smooth_hessianSandwichEnergy hφ hdet R).continuous.aestronglyMeasurable
    filter_upwards with x
    rw [Real.norm_of_nonneg (he0 x)]
    dsimp [G]
    linarith [hid x, (hpr0 x).1, (hpr0 x).2]
  have hri : Integrable r (potentialMeasure φ) := by
    apply hGi.mono' (smooth_hessianSandwichThirdTerm hφ hdet R).continuous.aestronglyMeasurable
    filter_upwards with x
    rw [Real.norm_of_nonneg (hpr0 x).2]
    dsimp [G]
    linarith [hid x, he0 x, (hpr0 x).1]
  have hpi : Integrable p (potentialMeasure φ) := by
    convert (hGi.sub hei).sub hri using 1
    funext x
    dsimp [G]
    linarith [hid x]
  have hGint : (∫ x, G x ∂potentialMeasure φ) = ∫ x, q x ∂potentialMeasure φ := by
    dsimp [G]
    rw [integral_div, integral_add hLqi (hqi.const_mul 2), integral_const_mul, hLq0]
    ring
  have hGeq : G = fun x => e x + p x + r x := by
    funext x
    dsimp [G]
    linarith [hid x]
  rw [hGeq] at hGint
  dsimp only at hGint
  have hsplit := integral_add (hei.add hpi) hri
  simp only [Pi.add_apply] at hsplit
  rw [hsplit, integral_add hei hpi] at hGint
  exact ⟨hqi, hei, hpi, hri, hGint.symm⟩

end GaussianTilt.Letwin
