import GaussianTilt.EllipticRegularityLocal

/-! # Distributional equation and localization for weighted harmonic L² functions -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ContDiff Topology ENNReal InnerProductSpace
namespace GaussianTilt.Letwin

/-- The actual ordinary Euclidean coordinate Laplacian. -/
def euclideanLaplacian {n : ℕ} (u : CoordinateSpace n → ℝ) (x : CoordinateSpace n) : ℝ :=
  ∑ i, coordinateDerivative i (coordinateDerivative i u) x

lemma coordinateDerivative_exp {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hφ : Differentiable ℝ φ) (i : Fin n) (x : CoordinateSpace n) :
    coordinateDerivative i (fun y => Real.exp (φ y)) x =
      Real.exp (φ x) * coordinateDerivative i φ x := by
  unfold coordinateDerivative
  rw [((hφ x).hasFDerivAt.exp).fderiv]
  simp

/-- The weighted generator conjugation is proved by actual coordinate
product rules. It turns the weighted orthogonality into an unweighted
second-order distributional equation. -/
theorem weightedLaplacian_exp_mul {n : ℕ} {φ ψ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ) (x : CoordinateSpace n) :
    weightedLaplacian φ (fun y => Real.exp (φ y) * ψ y) x =
      Real.exp (φ x) * (euclideanLaplacian ψ x +
        (∑ i, coordinateDerivative i φ x * coordinateDerivative i ψ x) +
        euclideanLaplacian φ x * ψ x) := by
  have hφd := hφ.differentiable (by simp)
  have hψd := hψ.differentiable (by simp)
  have hed : Differentiable ℝ (fun y => Real.exp (φ y)) := hφd.exp
  have hfirst (i : Fin n) : coordinateDerivative i (fun y => Real.exp (φ y) * ψ y) =
      fun y => Real.exp (φ y) * coordinateDerivative i φ y * ψ y +
        Real.exp (φ y) * coordinateDerivative i ψ y := by
    funext y
    rw [coordinateDerivative_mul hed hψd, coordinateDerivative_exp hφd]
  rw [weightedLaplacian_apply]
  simp only [hfirst]
  simp only [euclideanLaplacian, Finset.sum_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [coordinateDerivative_add
    (f := fun y => Real.exp (φ y) * coordinateDerivative i φ y * ψ y)
    (g := fun y => Real.exp (φ y) * coordinateDerivative i ψ y)
    ((hed.mul ((smooth_coordinateDerivative hφ i).differentiable (by simp))).mul hψd)
    (hed.mul ((smooth_coordinateDerivative hψ i).differentiable (by simp))),
    coordinateDerivative_mul
      (f := fun y => Real.exp (φ y) * coordinateDerivative i φ y) (g := ψ) (hed.mul ((smooth_coordinateDerivative hφ i).differentiable (by simp))) hψd,
    coordinateDerivative_mul (f := fun y => Real.exp (φ y)) (g := coordinateDerivative i φ) hed ((smooth_coordinateDerivative hφ i).differentiable (by simp)),
    coordinateDerivative_mul (f := fun y => Real.exp (φ y)) (g := coordinateDerivative i ψ) hed ((smooth_coordinateDerivative hψ i).differentiable (by simp)),
    coordinateDerivative_exp hφd]
  ring

/-- Orthogonality to the actual weighted generator implies its genuine
unweighted distributional equation. No differentiability of h is assumed. -/
theorem weighted_generator_orthogonal_distribution {n : ℕ}
    {φ h : CoordinateSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (horth : ∀ u : CoordinateSpace n → ℝ, ContDiff ℝ ∞ u → HasCompactSupport u →
      (∫ x, h x * weightedLaplacian φ u x ∂potentialMeasure φ) = 0)
    {ψ : CoordinateSpace n → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) :
    (∫ x, h x * (euclideanLaplacian ψ x +
      (∑ i, coordinateDerivative i φ x * coordinateDerivative i ψ x) +
      euclideanLaplacian φ x * ψ x)) = 0 := by
  have he := horth (fun x => Real.exp (φ x) * ψ x) (hφ.exp.mul hψ) hψc.mul_left
  rw [integral_potentialMeasure hφ.continuous] at he
  convert he using 1
  apply integral_congr_ae
  filter_upwards with x
  rw [weightedLaplacian_exp_mul hφ hψ]
  have hexp : Real.exp (-φ x) * Real.exp (φ x) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  calc
    _ = (Real.exp (-φ x) * Real.exp (φ x)) * (h x *
      (euclideanLaplacian ψ x + (∑ i, coordinateDerivative i φ x * coordinateDerivative i ψ x) +
        euclideanLaplacian φ x * ψ x)) := by rw [hexp, one_mul]
    _ = _ := by ring

lemma smooth_euclideanLaplacian {n : ℕ} {u : CoordinateSpace n → ℝ}
    (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (euclideanLaplacian u) := by
  apply ContDiff.sum
  intro i _
  exact smooth_coordinateDerivative (smooth_coordinateDerivative hu i) i

lemma hasCompactSupport_sum_coordinate {n : ℕ} {ι : Type*} [Fintype ι]
    (f : ι → CoordinateSpace n → ℝ) (hf : ∀ i, HasCompactSupport (f i)) :
    HasCompactSupport (fun x => ∑ i, f i x) := by
  classical
  have hs (s : Finset ι) : HasCompactSupport (fun x => ∑ i ∈ s, f i x) := by
    induction s using Finset.induction_on with
    | empty => simpa using (HasCompactSupport.zero : HasCompactSupport (fun _ : CoordinateSpace n => (0 : ℝ)))
    | @insert i s hi ih =>
      simpa only [Finset.sum_insert hi] using (hf i).add ih
  exact hs Finset.univ

lemma euclideanLaplacian_compact {n : ℕ} {u : CoordinateSpace n → ℝ}
    (hu : HasCompactSupport u) : HasCompactSupport (euclideanLaplacian u) := by
  apply hasCompactSupport_sum_coordinate
  intro i
  exact (hu.fderiv_apply (𝕜 := ℝ) (Pi.single i 1)).fderiv_apply (𝕜 := ℝ) (Pi.single i 1)

lemma euclideanLaplacian_mul {n : ℕ} {χ ψ : CoordinateSpace n → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ) (x : CoordinateSpace n) :
    euclideanLaplacian (fun y => χ y * ψ y) x =
      χ x * euclideanLaplacian ψ x +
        2 * (∑ i, coordinateDerivative i χ x * coordinateDerivative i ψ x) +
        euclideanLaplacian χ x * ψ x := by
  have hχd := hχ.differentiable (by simp)
  have hψd := hψ.differentiable (by simp)
  have hfirst (i : Fin n) : coordinateDerivative i (fun y => χ y * ψ y) =
      fun y => coordinateDerivative i χ y * ψ y + χ y * coordinateDerivative i ψ y :=
    funext (coordinateDerivative_mul hχd hψd i)
  simp only [euclideanLaplacian, hfirst, Finset.mul_sum, Finset.sum_mul,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [coordinateDerivative_add
    (f := fun y => coordinateDerivative i χ y * ψ y)
    (g := fun y => χ y * coordinateDerivative i ψ y)
    (((smooth_coordinateDerivative hχ i).differentiable (by simp)).mul hψd)
    (hχd.mul ((smooth_coordinateDerivative hψ i).differentiable (by simp))),
    coordinateDerivative_mul (f := coordinateDerivative i χ) (g := ψ)
      ((smooth_coordinateDerivative hχ i).differentiable (by simp)) hψd,
    coordinateDerivative_mul (f := χ) (g := coordinateDerivative i ψ)
      hχd ((smooth_coordinateDerivative hψ i).differentiable (by simp))]
  ring

/-- A genuine distributional equation Δf=div F+g, tested against actual
compact smooth functions and Lebesgue measure. -/
def HasDistributionLaplacian {n : ℕ} (f : CoordinateSpace n → ℝ)
    (F : Fin n → CoordinateSpace n → ℝ) (g : CoordinateSpace n → ℝ) : Prop :=
  ∀ ψ : CoordinateSpace n → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
    (∫ x, f x * euclideanLaplacian ψ x +
      (∑ i, F i x * coordinateDerivative i ψ x) - g x * ψ x) = 0

/-- The explicit first-order coefficient after multiplying by a cutoff. -/
def localizedEllipticFlux {n : ℕ} (φ χ h : CoordinateSpace n → ℝ)
    (i : Fin n) (x : CoordinateSpace n) : ℝ :=
  (2 * coordinateDerivative i χ x + χ x * coordinateDerivative i φ x) * h x

/-- The explicit zeroth-order coefficient after multiplying by a cutoff. -/
def localizedEllipticSource {n : ℕ} (φ χ h : CoordinateSpace n → ℝ)
    (x : CoordinateSpace n) : ℝ :=
  -(euclideanLaplacian χ x +
    (∑ i, coordinateDerivative i φ x * coordinateDerivative i χ x) +
      euclideanLaplacian φ x * χ x) * h x

/-- A weighted-generator annihilator has, after arbitrary compact smooth
localization, an actual unweighted divergence-form equation. -/
theorem weighted_generator_orthogonal_localized {n : ℕ}
    {φ h χ : CoordinateSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (horth : ∀ u : CoordinateSpace n → ℝ, ContDiff ℝ ∞ u → HasCompactSupport u →
      (∫ x, h x * weightedLaplacian φ u x ∂potentialMeasure φ) = 0) :
    HasDistributionLaplacian (fun x => χ x * h x)
      (localizedEllipticFlux φ χ h) (localizedEllipticSource φ χ h) := by
  intro ψ hψ hψc
  have he := weighted_generator_orthogonal_distribution hφ horth (hχ.mul hψ) hχc.mul_right
  convert he using 1
  apply integral_congr_ae
  filter_upwards with x
  rw [euclideanLaplacian_mul hχ hψ]
  simp only [localizedEllipticFlux, localizedEllipticSource,
    coordinateDerivative_mul (hχ.differentiable (by simp)) (hψ.differentiable (by simp))]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_add, add_mul, mul_neg, sub_neg_eq_add,
    Finset.sum_add_distrib]
  ring_nf
  simp only [Finset.mul_sum, Finset.sum_mul]
  ring_nf

/-- Every coefficient in that localized equation is a genuine compactly
supported Lebesgue L² function, proved from the original weighted L² input. -/
theorem localizedElliptic_memLp {n : ℕ}
    {φ h χ : CoordinateSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hh : MemLp h 2 (potentialMeasure φ)) :
    MemLp (fun x => χ x * h x) 2 volume ∧
      (∀ i, MemLp (localizedEllipticFlux φ χ h i) 2 volume) ∧
      MemLp (localizedEllipticSource φ χ h) 2 volume := by
  refine ⟨memLp_compact_mul_of_potential hφ.continuous hh hχ.continuous hχc, ?_, ?_⟩
  · intro i
    apply memLp_compact_mul_of_potential hφ.continuous hh
    · exact (continuous_const.mul (smooth_coordinateDerivative hχ i).continuous).add
        (hχ.continuous.mul (smooth_coordinateDerivative hφ i).continuous)
    · exact ((hχc.fderiv_apply (𝕜 := ℝ) (Pi.single i 1)).mul_left).add hχc.mul_right
  · apply memLp_compact_mul_of_potential hφ.continuous hh
    · exact (((smooth_euclideanLaplacian hχ).continuous.add
        (continuous_finset_sum _ fun i _ =>
          (smooth_coordinateDerivative hφ i).continuous.mul
            (smooth_coordinateDerivative hχ i).continuous)).add
        ((smooth_euclideanLaplacian hφ).continuous.mul hχ.continuous)).neg
    · apply HasCompactSupport.neg
      apply HasCompactSupport.add
      · apply HasCompactSupport.add (euclideanLaplacian_compact hχc)
        apply hasCompactSupport_sum_coordinate
        intro i
        exact (hχc.fderiv_apply (𝕜 := ℝ) (Pi.single i 1)).mul_left
      · exact hχc.mul_left

/-- All localized data have actual compact support, including rough h. -/
theorem localizedElliptic_compact {n : ℕ}
    (φ h : CoordinateSpace n → ℝ) {χ : CoordinateSpace n → ℝ}
    (hχc : HasCompactSupport χ) :
    HasCompactSupport (fun x => χ x * h x) ∧
      (∀ i, HasCompactSupport (localizedEllipticFlux φ χ h i)) ∧
      HasCompactSupport (localizedEllipticSource φ χ h) := by
  refine ⟨hχc.mul_right, ?_, ?_⟩
  · intro i
    apply HasCompactSupport.mul_right
    exact ((hχc.fderiv_apply (𝕜 := ℝ) (Pi.single i 1)).mul_left).add hχc.mul_right
  · apply HasCompactSupport.mul_right
    apply HasCompactSupport.neg
    apply HasCompactSupport.add
    · apply HasCompactSupport.add (euclideanLaplacian_compact hχc)
      apply hasCompactSupport_sum_coordinate
      intro i
      exact (hχc.fderiv_apply (𝕜 := ℝ) (Pi.single i 1)).mul_left
    · exact hχc.mul_left

end GaussianTilt.Letwin
