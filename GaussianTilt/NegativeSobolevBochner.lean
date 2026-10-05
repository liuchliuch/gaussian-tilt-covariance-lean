import GaussianTilt.LetwinBochner

/-!
# Euclidean weighted Bochner identity for negative Sobolev duality

All operators below are the actual coordinate derivatives.  For a smooth
potential and compactly supported smooth test, the integrated Bochner identity
is proved from the already established whole-space Green formula.  In
particular, neither the identity nor its coercivity conclusion is a premise.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ContDiff
namespace GaussianTilt.Letwin

/-- The ordinary weighted Laplacian, with identity diffusion matrix. -/
def weightedLaplacian {n : ℕ} (φ u : CoordinateSpace n → ℝ) : CoordinateSpace n → ℝ :=
  divergenceDiffusion φ (fun _ => 1) u

/-- Squared Euclidean length of the actual coordinate gradient. -/
def gradientSquare {n : ℕ} (u : CoordinateSpace n → ℝ) (x : CoordinateSpace n) : ℝ :=
  ∑ i, (coordinateDerivative i u x)^2

@[simp] lemma diffusionFlux_one {n : ℕ} (u : CoordinateSpace n → ℝ)
    (i : Fin n) (x : CoordinateSpace n) :
    diffusionFlux (fun _ => 1) u i x = coordinateDerivative i u x := by
  simp [diffusionFlux, Matrix.one_apply]

@[simp] lemma diffusionFlux_one_fun {n : ℕ} (u : CoordinateSpace n → ℝ)
    (i : Fin n) : diffusionFlux (fun _ => 1) u i = coordinateDerivative i u :=
  funext (diffusionFlux_one u i)

@[simp] lemma diffusionGamma_one {n : ℕ} (u v : CoordinateSpace n → ℝ)
    (x : CoordinateSpace n) :
    diffusionGamma (fun _ => 1) u v x =
      ∑ i, coordinateDerivative i u x * coordinateDerivative i v x := by
  simp [diffusionGamma]

lemma weightedLaplacian_apply {n : ℕ} (φ u : CoordinateSpace n → ℝ)
    (x : CoordinateSpace n) :
    weightedLaplacian φ u x = ∑ i : Fin n, (coordinateDerivative i (coordinateDerivative i u) x -
      coordinateDerivative i φ x * coordinateDerivative i u x) := by
  simp [weightedLaplacian, divergenceDiffusion, weightedCoordinateDivergence]

lemma smooth_weightedLaplacian {n : ℕ} {φ u : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (weightedLaplacian φ u) := by
  change ContDiff ℝ ∞ (fun x => weightedLaplacian φ u x)
  simp_rw [weightedLaplacian_apply]
  apply ContDiff.sum
  intro i _
  exact (smooth_coordinateDerivative (smooth_coordinateDerivative hu i) i).sub
    ((smooth_coordinateDerivative hφ i).mul (smooth_coordinateDerivative hu i))

lemma weightedLaplacian_hasCompactSupport {n : ℕ} (φ : CoordinateSpace n → ℝ)
    {u : CoordinateSpace n → ℝ} (hu : HasCompactSupport u) :
    HasCompactSupport (weightedLaplacian φ u) :=
  divergenceDiffusion_hasCompactSupport φ (fun _ => 1) hu

lemma coordinateDerivative_sub_smooth {n : ℕ} {f g : CoordinateSpace n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (i : Fin n) (x : CoordinateSpace n) :
    coordinateDerivative i (fun y => f y - g y) x =
      coordinateDerivative i f x - coordinateDerivative i g x := by
  unfold coordinateDerivative
  rw [fderiv_fun_sub (hf.differentiable (by simp) x) (hg.differentiable (by simp) x)]
  rfl

/-- Differentiating the weighted Laplacian produces the actual Hessian of its
potential. -/
lemma coordinateDerivative_weightedLaplacian {n : ℕ} {φ u : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hu : ContDiff ℝ ∞ u) (i : Fin n) (x : CoordinateSpace n) :
    coordinateDerivative i (weightedLaplacian φ u) x =
      weightedLaplacian φ (coordinateDerivative i u) x -
        ∑ j, coordinateHessian φ x j i * coordinateDerivative j u x := by
  have hsum : weightedLaplacian φ u = fun y => ∑ j : Fin n,
      (coordinateDerivative j (coordinateDerivative j u) y -
        coordinateDerivative j φ y * coordinateDerivative j u y) :=
    funext (weightedLaplacian_apply φ u)
  rw [hsum, coordinateDerivative_sum]
  · simp_rw [coordinateDerivative_sub_smooth
      (smooth_coordinateDerivative (smooth_coordinateDerivative hu _) _)
      ((smooth_coordinateDerivative hφ _).mul (smooth_coordinateDerivative hu _)),
      coordinateDerivative_mul ((smooth_coordinateDerivative hφ _).differentiable (by simp))
        ((smooth_coordinateDerivative hu _).differentiable (by simp))]
    rw [weightedLaplacian_apply, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have hthird := congrFun
      (coordinateDerivative_commute (contDiff_infty.mp (smooth_coordinateDerivative hu j) 2) i j) x
    have hsecond := coordinateDerivative_commute (contDiff_infty.mp hu 2) i j
    rw [hsecond] at hthird
    rw [hthird]
    simp only [← hsecond, coordinateHessian]
    ring
  · intro j
    exact ((smooth_coordinateDerivative (smooth_coordinateDerivative hu j) j).sub
      ((smooth_coordinateDerivative hφ j).mul (smooth_coordinateDerivative hu j))).differentiable (by simp)

lemma continuous_gradientSquare {n : ℕ} {u : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) : Continuous (gradientSquare u) := by
  apply continuous_finset_sum
  intro i _
  exact (smooth_coordinateDerivative hu i).continuous.pow 2

lemma gradientSquare_hasCompactSupport {n : ℕ} {u : CoordinateSpace n → ℝ}
    (hu : HasCompactSupport u) : HasCompactSupport (gradientSquare u) := by
  apply hu.mono'
  intro x hx
  by_contra hn
  apply hx
  simp [gradientSquare, coordinateDerivative, fderiv_of_notMem_tsupport ℝ hn]

/-- Integrated Euclidean Bochner identity for a genuine compact smooth test. -/
theorem integral_weightedLaplacian_sq {n : ℕ} {φ u : CoordinateSpace n → ℝ}
    [IsFiniteMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ ∞ φ) (hu : ContDiff ℝ ∞ u) (huc : HasCompactSupport u) :
    (∫ x, (weightedLaplacian φ u x)^2 ∂potentialMeasure φ) =
      (∑ i, ∫ x, gradientSquare (coordinateDerivative i u) x ∂potentialMeasure φ) +
      ∫ x, ∑ i, ∑ j, coordinateHessian φ x j i *
        coordinateDerivative j u x * coordinateDerivative i u x ∂potentialMeasure φ := by
  let μ := potentialMeasure φ
  have hdc (i : Fin n) : HasCompactSupport (coordinateDerivative i u) :=
    huc.fderiv_apply (𝕜 := ℝ) (Pi.single i 1)
  have hs (i : Fin n) := smooth_coordinateDerivative hu i
  have hL := smooth_weightedLaplacian hφ hu
  have hLc := weightedLaplacian_hasCompactSupport φ huc
  have hgreen := integral_divergenceDiffusion_mul_compact_left (A := fun _ => 1)
    (contDiff_infty.mp hφ 1) (fun _ _ => contDiff_const)
    (contDiff_infty.mp hu 2) (contDiff_infty.mp hL 1) huc
  have hterm (i : Fin n) : Integrable
      (fun x => coordinateDerivative i u x * coordinateDerivative i (weightedLaplacian φ u) x) μ :=
    ((hs i).continuous.mul (smooth_coordinateDerivative hL i).continuous).integrable_of_hasCompactSupport
      (hdc i).mul_right
  have hsplit (i : Fin n) : Integrable
      (fun x => coordinateDerivative i u x * weightedLaplacian φ (coordinateDerivative i u) x) μ :=
    ((hs i).continuous.mul (smooth_weightedLaplacian hφ (hs i)).continuous).integrable_of_hasCompactSupport
      (hdc i).mul_right
  have hcurv (i : Fin n) : Integrable
      (fun x => coordinateDerivative i u x *
        ∑ j, coordinateHessian φ x j i * coordinateDerivative j u x) μ := by
    apply ((hs i).continuous.mul (continuous_finset_sum _ (fun j _ =>
      (smooth_coordinateHessian hφ j i).continuous.mul (hs j).continuous))).integrable_of_hasCompactSupport
    exact (hdc i).mul_right
  have hgreen' : (∫ x, (weightedLaplacian φ u x)^2 ∂μ) =
      -(∑ i, ∫ x, coordinateDerivative i u x *
        coordinateDerivative i (weightedLaplacian φ u) x ∂μ) := by
    change (∫ x, weightedLaplacian φ u x * weightedLaplacian φ u x ∂μ) =
      -(∫ x, diffusionGamma (fun _ => 1) u (weightedLaplacian φ u) x ∂μ) at hgreen
    simpa only [diffusionGamma_one, ← pow_two,
      integral_finset_sum _ (fun i _ => hterm i)] using hgreen
  rw [hgreen']
  simp_rw [coordinateDerivative_weightedLaplacian hφ hu, mul_sub]
  rw [show (∑ i, ∫ x, coordinateDerivative i u x *
      weightedLaplacian φ (coordinateDerivative i u) x -
      coordinateDerivative i u x * (∑ j, coordinateHessian φ x j i * coordinateDerivative j u x) ∂μ) =
      (∑ i, ∫ x, coordinateDerivative i u x * weightedLaplacian φ (coordinateDerivative i u) x ∂μ) -
      ∑ i, ∫ x, coordinateDerivative i u x * (∑ j, coordinateHessian φ x j i * coordinateDerivative j u x) ∂μ
      from by simp_rw [integral_sub (hsplit _) (hcurv _), Finset.sum_sub_distrib]]
  have hfirst (i : Fin n) : (∫ x, coordinateDerivative i u x *
      weightedLaplacian φ (coordinateDerivative i u) x ∂μ) =
      -(∫ x, gradientSquare (coordinateDerivative i u) x ∂μ) := by
    have h := integral_divergenceDiffusion_mul_compact_left (A := fun _ => 1) (contDiff_infty.mp hφ 1)
      (fun _ _ => contDiff_const) (contDiff_infty.mp (hs i) 2)
      (contDiff_infty.mp (hs i) 1) (hdc i)
    change (∫ x, weightedLaplacian φ (coordinateDerivative i u) x * coordinateDerivative i u x ∂μ) = _ at h
    simpa only [diffusionGamma_one, mul_comm, ← pow_two, gradientSquare] using h
  simp_rw [hfirst, Finset.sum_neg_distrib]
  rw [neg_sub, sub_neg_eq_add, add_comm]
  congr 1
  rw [← integral_finset_sum _ (fun i _ => hcurv i)]
  apply integral_congr_ae
  filter_upwards with x
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Log-convexity of the potential makes the curvature term nonnegative.
This is the Bochner coercivity used in Barthe--Klartag Proposition 10. -/
theorem sum_integral_gradientSquare_le_laplacian_sq {n : ℕ} {φ u : CoordinateSpace n → ℝ}
    [IsFiniteMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ ∞ φ) (hu : ContDiff ℝ ∞ u) (huc : HasCompactSupport u)
    (hH : ∀ x, (coordinateHessian φ x).PosSemidef) :
    (∑ i, ∫ x, gradientSquare (coordinateDerivative i u) x ∂potentialMeasure φ) ≤
      ∫ x, (weightedLaplacian φ u x)^2 ∂potentialMeasure φ := by
  rw [integral_weightedLaplacian_sq hφ hu huc]
  apply le_add_of_nonneg_right
  apply integral_nonneg
  intro x
  have h := (hH x).2 (coordinateGradient u x)
  have heq : (∑ i, ∑ j, coordinateHessian φ x j i *
      coordinateDerivative j u x * coordinateDerivative i u x) =
      star (coordinateGradient u x) ⬝ᵥ (coordinateHessian φ x).mulVec (coordinateGradient u x) := by
    simp only [dotProduct, Matrix.mulVec, star_trivial, coordinateGradient, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  change 0 ≤ ∑ i, ∑ j, _
  rw [heq]
  exact h

end GaussianTilt.Letwin
