import GaussianTilt.LetwinIntegration
import GaussianTilt.LetwinExhaustion

/-!
# The actual weighted divergence-form diffusion

The generator is defined using coordinate derivatives, not by an assumed
integration-by-parts identity. Its chain and Green identities are derived here.
-/

noncomputable section
open MeasureTheory Filter Matrix
open scoped BigOperators Topology

namespace GaussianTilt.Letwin

abbrev CoordinateSpace (n : ℕ) := Fin n → ℝ

def diffusionFlux {n : ℕ} (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (f : CoordinateSpace n → ℝ) (i : Fin n) (x : CoordinateSpace n) : ℝ :=
  ∑ j, A x i j * coordinateDerivative j f x

def diffusionGamma {n : ℕ} (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (f g : CoordinateSpace n → ℝ) (x : CoordinateSpace n) : ℝ :=
  ∑ i, diffusionFlux A f i x * coordinateDerivative i g x

def divergenceDiffusion {n : ℕ} (φ : CoordinateSpace n → ℝ)
    (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (f : CoordinateSpace n → ℝ) (x : CoordinateSpace n) : ℝ :=
  ∑ i, weightedCoordinateDivergence φ (diffusionFlux A f i) i x

lemma coordinateDerivative_mul {n : ℕ} {f g : CoordinateSpace n → ℝ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (i : Fin n) (x : CoordinateSpace n) :
    coordinateDerivative i (fun y => f y * g y) x =
      coordinateDerivative i f x * g x + f x * coordinateDerivative i g x := by
  unfold coordinateDerivative
  rw [fderiv_fun_mul (hf x) (hg x)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

lemma coordinateDerivative_comp {n : ℕ} {η : ℝ → ℝ} {f : CoordinateSpace n → ℝ}
    (hη : Differentiable ℝ η) (hf : Differentiable ℝ f) (i : Fin n) (x : CoordinateSpace n) :
    coordinateDerivative i (η ∘ f) x = deriv η (f x) * coordinateDerivative i f x := by
  unfold coordinateDerivative
  rw [(hη (f x)).hasDerivAt.comp_hasFDerivAt x (hf x).hasFDerivAt |>.fderiv]
  simp

lemma contDiff_diffusionFlux {n : ℕ}
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {f : CoordinateSpace n → ℝ}
    (hA : ∀ i j, ContDiff ℝ 1 (fun x => A x i j)) (hf : ContDiff ℝ 2 f) (i : Fin n) :
    ContDiff ℝ 1 (diffusionFlux A f i) := by
  apply ContDiff.sum
  intro j _
  exact (hA i j).mul (contDiff_coordinateDerivative hf (m := 1) (by norm_num) j)

lemma diffusionFlux_comp {n : ℕ}
    (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ) {η : ℝ → ℝ} {f : CoordinateSpace n → ℝ}
    (hη : Differentiable ℝ η) (hf : Differentiable ℝ f) (i : Fin n) (x : CoordinateSpace n) :
    diffusionFlux A (η ∘ f) i x = deriv η (f x) * diffusionFlux A f i x := by
  simp only [diffusionFlux, coordinateDerivative_comp hη hf, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The diffusion chain rule for actual twice differentiable functions. -/
theorem divergenceDiffusion_comp {n : ℕ}
    (φ : CoordinateSpace n → ℝ)
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {η : ℝ → ℝ} {f : CoordinateSpace n → ℝ}
    (hA : ∀ i j, ContDiff ℝ 1 (fun x => A x i j))
    (hη : ContDiff ℝ 2 η) (hf : ContDiff ℝ 2 f) (x : CoordinateSpace n) :
    divergenceDiffusion φ A (η ∘ f) x =
      deriv η (f x) * divergenceDiffusion φ A f x +
      deriv (deriv η) (f x) * diffusionGamma A f f x := by
  have hηd := hη.differentiable (by norm_num)
  have hfd := hf.differentiable (by norm_num)
  have hη'd : Differentiable ℝ (deriv η) := hη.differentiable_deriv_two
  have hηfc : Differentiable ℝ (fun y => deriv η (f y)) := hη'd.comp hfd
  have hflux (i : Fin n) : diffusionFlux A (η ∘ f) i =
      (fun y => deriv η (f y) * diffusionFlux A f i y) := by
    funext y
    exact diffusionFlux_comp A hηd hfd i y
  simp only [divergenceDiffusion, weightedCoordinateDivergence, hflux,
    coordinateDerivative_mul hηfc ((contDiff_diffusionFlux hA hf _).differentiable le_rfl)]
  have hchain (i : Fin n) : coordinateDerivative i (fun y => deriv η (f y)) x =
      deriv (deriv η) (f x) * coordinateDerivative i f x :=
    coordinateDerivative_comp hη'd hfd i x
  simp only [hchain, diffusionGamma, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Positivity of the carré du champ follows from the actual matrix quadratic
form when the diffusion matrix is positive semidefinite. -/
theorem diffusionGamma_nonneg {n : ℕ}
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    (f : CoordinateSpace n → ℝ) (x : CoordinateSpace n) (hA : (A x).PosSemidef) :
    0 ≤ diffusionGamma A f f x := by
  have h := hA.2 (coordinateGradient f x)
  simpa only [diffusionGamma, diffusionFlux, coordinateGradient, dotProduct, Matrix.mulVec,
    star_trivial, Finset.sum_mul, mul_comm] using h

lemma continuous_weightedCoordinateDivergence {n : ℕ} {φ F : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hF : ContDiff ℝ 1 F) (i : Fin n) :
    Continuous (weightedCoordinateDivergence φ F i) :=
  (contDiff_coordinateDerivative hF (m := 0) (by norm_num) i).continuous.sub
    ((contDiff_coordinateDerivative hφ (m := 0) (by norm_num) i).continuous.mul hF.continuous)

lemma continuous_divergenceDiffusion {n : ℕ} {φ f : CoordinateSpace n → ℝ}
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hφ : ContDiff ℝ 1 φ) (hA : ∀ i j, ContDiff ℝ 1 (fun x => A x i j))
    (hf : ContDiff ℝ 2 f) : Continuous (divergenceDiffusion φ A f) := by
  apply continuous_finset_sum
  intro i _
  exact continuous_weightedCoordinateDivergence hφ (contDiff_diffusionFlux hA hf i) i

/-- Green's formula for the actual divergence-form operator, with no assumed
operator symmetry. -/
theorem integral_divergenceDiffusion_mul {n : ℕ}
    {φ f g : CoordinateSpace n → ℝ} [IsFiniteMeasure (potentialMeasure φ)]
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hφ : ContDiff ℝ 1 φ) (hA : ∀ i j, ContDiff ℝ 1 (fun x => A x i j))
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) :
    (∫ x, divergenceDiffusion φ A f x * g x ∂potentialMeasure φ) =
      -(∫ x, diffusionGamma A f g x ∂potentialMeasure φ) := by
  have hleft (i : Fin n) : Integrable
      (fun x => weightedCoordinateDivergence φ (diffusionFlux A f i) i x * g x)
      (potentialMeasure φ) :=
    ((continuous_weightedCoordinateDivergence hφ (contDiff_diffusionFlux hA hf i) i).mul
      hg.continuous).integrable_of_hasCompactSupport hgc.mul_left
  have hright (i : Fin n) : Integrable
      (fun x => diffusionFlux A f i x * coordinateDerivative i g x) (potentialMeasure φ) :=
    ((contDiff_diffusionFlux hA hf i).continuous.mul
      (contDiff_coordinateDerivative hg (m := 0) (by norm_num) i).continuous).integrable_of_hasCompactSupport
        (hgc.fderiv_apply (𝕜 := ℝ) (Pi.single i 1)).mul_left
  simp only [divergenceDiffusion, Finset.sum_mul, diffusionGamma]
  rw [integral_finset_sum _ (fun i _ => hleft i),
    integral_finset_sum _ (fun i _ => hright i), ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_weightedCoordinateDivergence_mul i hφ (contDiff_diffusionFlux hA hf i) hg hgc

lemma diffusionGamma_comp_right {n : ℕ}
    (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    {q : ℝ → ℝ} {f : CoordinateSpace n → ℝ}
    (hq : Differentiable ℝ q) (hf : Differentiable ℝ f) (x : CoordinateSpace n) :
    diffusionGamma A f (q ∘ f) x = deriv q (f x) * diffusionGamma A f f x := by
  simp only [diffusionGamma, coordinateDerivative_comp hq hf, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The energy-testing identity used to estimate the cutoffs in A4. -/
theorem integral_diffusion_energy_test {n : ℕ}
    {φ W : CoordinateSpace n → ℝ} [IsFiniteMeasure (potentialMeasure φ)]
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {q : ℝ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hA : ∀ i j, ContDiff ℝ 1 (fun x => A x i j))
    (hW : ContDiff ℝ 2 W) (hq : ContDiff ℝ 1 q) (hqc : HasCompactSupport (q ∘ W)) :
    (∫ x, q (W x) * divergenceDiffusion φ A W x ∂potentialMeasure φ) =
      -(∫ x, deriv q (W x) * diffusionGamma A W W x ∂potentialMeasure φ) := by
  have h := integral_divergenceDiffusion_mul hφ hA hW (hq.comp (hW.of_le (by norm_num))) hqc
  simpa only [Function.comp_apply, mul_comm, diffusionGamma_comp_right A
    (hq.differentiable le_rfl) (hW.differentiable (by norm_num))] using h

lemma continuous_diffusionGamma {n : ℕ}
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {f g : CoordinateSpace n → ℝ}
    (hA : ∀ i j, ContDiff ℝ 1 (fun x => A x i j))
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 1 g) : Continuous (diffusionGamma A f g) := by
  apply continuous_finset_sum
  intro i _
  exact (contDiff_diffusionFlux hA hf i).continuous.mul
    (contDiff_coordinateDerivative hg (m := 0) (by norm_num) i).continuous

lemma tsupport_diffusionFlux_subset {n : ℕ}
    (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ) (f : CoordinateSpace n → ℝ) (i : Fin n) :
    tsupport (diffusionFlux A f i) ⊆ tsupport f := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra hn
  apply hx
  simp only [diffusionFlux, coordinateDerivative, fderiv_of_notMem_tsupport ℝ hn,
    ContinuousLinearMap.zero_apply, mul_zero, Finset.sum_const_zero]

lemma divergenceDiffusion_hasCompactSupport {n : ℕ}
    (φ : CoordinateSpace n → ℝ) (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    {f : CoordinateSpace n → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (divergenceDiffusion φ A f) := by
  apply hf.mono'
  intro x hx
  by_contra hn
  apply hx
  unfold divergenceDiffusion weightedCoordinateDivergence
  apply Finset.sum_eq_zero
  intro i _
  have hni : x ∉ tsupport (diffusionFlux A f i) :=
    fun hx => hn (tsupport_diffusionFlux_subset A f i hx)
  have hz : diffusionFlux A f i x = 0 := Function.notMem_support.mp
    (fun hx => hni (subset_closure hx))
  simp [coordinateDerivative, fderiv_of_notMem_tsupport ℝ hni, hz]

/-- Green's formula with a compactly supported input function. -/
theorem integral_divergenceDiffusion_mul_compact_left {n : ℕ}
    {φ f g : CoordinateSpace n → ℝ} [IsFiniteMeasure (potentialMeasure φ)]
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hφ : ContDiff ℝ 1 φ) (hA : ∀ i j, ContDiff ℝ 1 (fun x => A x i j))
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 1 g) (hfc : HasCompactSupport f) :
    (∫ x, divergenceDiffusion φ A f x * g x ∂potentialMeasure φ) =
      -(∫ x, diffusionGamma A f g x ∂potentialMeasure φ) := by
  have hFc (i : Fin n) : HasCompactSupport (diffusionFlux A f i) :=
    hfc.mono' (fun x hx => tsupport_diffusionFlux_subset A f i (subset_closure hx))
  have hleft (i : Fin n) : Integrable
      (fun x => weightedCoordinateDivergence φ (diffusionFlux A f i) i x * g x)
      (potentialMeasure φ) := by
    apply ((continuous_weightedCoordinateDivergence hφ (contDiff_diffusionFlux hA hf i) i).mul
      hg.continuous).integrable_of_hasCompactSupport
    exact ((hFc i).fderiv_apply (𝕜 := ℝ) (Pi.single i 1) |>.sub (hFc i).mul_left).mul_right
  have hright (i : Fin n) : Integrable
      (fun x => diffusionFlux A f i x * coordinateDerivative i g x) (potentialMeasure φ) :=
    ((contDiff_diffusionFlux hA hf i).continuous.mul
      (contDiff_coordinateDerivative hg (m := 0) (by norm_num) i).continuous).integrable_of_hasCompactSupport
        (hFc i).mul_right
  simp only [divergenceDiffusion, Finset.sum_mul, diffusionGamma]
  rw [integral_finset_sum _ (fun i _ => hleft i),
    integral_finset_sum _ (fun i _ => hright i), ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_weightedCoordinateDivergence_mul_compact_left i hφ (contDiff_diffusionFlux hA hf i) hg (hFc i)

lemma diffusionGamma_symm {n : ℕ}
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} (f g : CoordinateSpace n → ℝ)
    (x : CoordinateSpace n) (hA : (A x).IsSymm) :
    diffusionGamma A f g x = diffusionGamma A g f x := by
  simp only [diffusionGamma, diffusionFlux, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hA.apply j i]
  ring

/-- Symmetry of the actual divergence operator, derived from Green's formula
and symmetry of its matrix coefficients. Only one test needs compact support. -/
theorem divergenceDiffusion_test_symmetry {n : ℕ}
    {φ f g : CoordinateSpace n → ℝ} [IsFiniteMeasure (potentialMeasure φ)]
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hφ : ContDiff ℝ 1 φ) (hA : ∀ i j, ContDiff ℝ 1 (fun x => A x i j))
    (hAs : ∀ x, (A x).IsSymm) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) :
    (∫ x, g x * divergenceDiffusion φ A f x ∂potentialMeasure φ) =
      ∫ x, f x * divergenceDiffusion φ A g x ∂potentialMeasure φ := by
  have h₁ := integral_divergenceDiffusion_mul hφ hA hf (hg.of_le (by norm_num)) hgc
  have h₂ := integral_divergenceDiffusion_mul_compact_left hφ hA hg (hf.of_le (by norm_num)) hgc
  have heq : diffusionGamma A f g = diffusionGamma A g f :=
    funext fun x => diffusionGamma_symm f g x (hAs x)
  rw [heq] at h₁
  simpa only [mul_comm] using h₁.trans h₂.symm

end GaussianTilt.Letwin
