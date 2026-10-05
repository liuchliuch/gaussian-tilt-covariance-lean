import GaussianTilt.EllipticRegularityDistribution
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-! # The a priori L² gradient estimate for compact elliptic equations -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ContDiff Topology ENNReal InnerProductSpace
namespace GaussianTilt.Letwin

/-- Ordinary whole-space Green identity, with compact support supplying
all boundary control. -/
theorem integral_mul_euclideanLaplacian {n : ℕ} {f : CoordinateSpace n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    (∫ x, f x * euclideanLaplacian f x) = -(∫ x, gradientSquare f x) := by
  have hi (i : Fin n) : (∫ x, f x * coordinateDerivative i (coordinateDerivative i f) x) =
      -(∫ x, (coordinateDerivative i f x)^2) := by
    have hdi := smooth_coordinateDerivative hf i
    have hdic := hfc.fderiv_apply (𝕜 := ℝ) (Pi.single i 1)
    have hddi := smooth_coordinateDerivative hdi i
    have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := (volume : Measure (CoordinateSpace n))) (f := f) (g := coordinateDerivative i f)
      (v := Pi.single i 1)
      ((hdi.continuous.mul hdi.continuous).integrable_of_hasCompactSupport hdic.mul_right)
      ((hf.continuous.mul hddi.continuous).integrable_of_hasCompactSupport hfc.mul_right)
      ((hf.continuous.mul hdi.continuous).integrable_of_hasCompactSupport hfc.mul_right)
      (hf.differentiable (by simp)) (hdi.differentiable (by simp))
    simpa only [coordinateDerivative, pow_two] using h
  have hI (i : Fin n) : Integrable (fun x => f x *
      coordinateDerivative i (coordinateDerivative i f) x) volume :=
    (hf.continuous.mul (smooth_coordinateDerivative (smooth_coordinateDerivative hf i) i).continuous).integrable_of_hasCompactSupport hfc.mul_right
  have hG (i : Fin n) : Integrable (fun x => (coordinateDerivative i f x)^2) volume :=
    ((smooth_coordinateDerivative hf i).continuous.pow 2).integrable_of_hasCompactSupport (by
      simpa only [pow_two] using
        (hfc.fderiv_apply (𝕜 := ℝ) (Pi.single i 1)).mul_right
          (f' := coordinateDerivative i f))
  simp only [euclideanLaplacian, Finset.mul_sum, gradientSquare]
  rw [integral_finset_sum _ (fun i _ => hI i), integral_finset_sum _ (fun i _ => hG i)]
  simp only [hi, Finset.sum_neg_distrib]

/-- The actual elliptic equation Δf=div F+g controls the whole gradient.
This is the estimate applied to mollifications before taking their limit. -/
theorem distributionLaplacian_gradient_energy_le {n : ℕ}
    {f g : CoordinateSpace n → ℝ} {F : Fin n → CoordinateSpace n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hF : ∀ i, MemLp (F i) 2 volume) (hg : MemLp g 2 volume)
    (heq : HasDistributionLaplacian f F g) :
    (∫ x, gradientSquare f x) ≤
      (∑ i, ∫ x, (F i x)^2) + (∫ x, f x^2) + ∫ x, g x^2 := by
  have hdf (i : Fin n) : MemLp (coordinateDerivative i f) 2 volume :=
    smooth_compact_memLp (smooth_coordinateDerivative hf i)
      (hfc.fderiv_apply (𝕜 := ℝ) (Pi.single i 1))
  have hf2 : MemLp f 2 volume := smooth_compact_memLp hf hfc
  have hI : Integrable (fun x => f x * euclideanLaplacian f x) volume :=
    (hf.continuous.mul (smooth_euclideanLaplacian hf).continuous).integrable_of_hasCompactSupport
      hfc.mul_right
  have hP : Integrable (fun x => ∑ i, F i x * coordinateDerivative i f x) volume :=
    integrable_finset_sum _ fun i _ => (hF i).integrable_mul (hdf i)
  have hgf : Integrable (fun x => g x * f x) volume := hg.integrable_mul hf2
  have he := heq f hf hfc
  rw [integral_sub (f := fun x => f x * euclideanLaplacian f x + ∑ i, F i x * coordinateDerivative i f x)
    (g := fun x => g x * f x) (hI.add hP) hgf, integral_add hI hP,
    integral_mul_euclideanLaplacian hf hfc] at he
  have hgrad : Integrable (gradientSquare f) volume :=
    (continuous_gradientSquare hf).integrable_of_hasCompactSupport (gradientSquare_hasCompactSupport hfc)
  have hFs : Integrable (fun x => ∑ i, (F i x)^2) volume :=
    integrable_finset_sum _ fun i _ => (hF i).integrable_sq
  have hp : 0 ≤ ∫ x, (∑ i : Fin n, (F i x - coordinateDerivative i f x)^2) +
      (f x + g x)^2 := integral_nonneg (μ := (volume : Measure (CoordinateSpace n)))
    (fun x => add_nonneg
      (Finset.sum_nonneg (fun i _ => sq_nonneg (F i x - coordinateDerivative i f x)))
      (sq_nonneg (f x + g x)))
  have hident (x : CoordinateSpace n) :
      (∑ i, (F i x - coordinateDerivative i f x)^2) + (f x + g x)^2 =
        (∑ i, (F i x)^2) + gradientSquare f x -
          2 * (∑ i, F i x * coordinateDerivative i f x) +
          (f x)^2 + (g x)^2 + 2 * (g x * f x) := by
    simp only [gradientSquare, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    have hs : (∑ i, (F i x - coordinateDerivative i f x)^2) =
        ∑ i, ((F i x)^2 + (coordinateDerivative i f x)^2 -
          2 * (F i x * coordinateDerivative i f x)) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hs]
    ring
  simp_rw [hident] at hp
  rw [integral_add
    (f := fun x => (∑ i, (F i x)^2) + gradientSquare f x -
      2 * (∑ i, F i x * coordinateDerivative i f x) + (f x)^2 + (g x)^2)
    (g := fun x => 2 * (g x * f x))
    ((((hFs.add hgrad).sub (hP.const_mul 2)).add hf2.integrable_sq).add hg.integrable_sq)
    (hgf.const_mul 2),
    integral_add
    (f := fun x => (∑ i, (F i x)^2) + gradientSquare f x -
      2 * (∑ i, F i x * coordinateDerivative i f x) + (f x)^2)
    (g := fun x => (g x)^2)
    (((hFs.add hgrad).sub (hP.const_mul 2)).add hf2.integrable_sq) hg.integrable_sq,
    integral_add
    (f := fun x => (∑ i, (F i x)^2) + gradientSquare f x -
      2 * (∑ i, F i x * coordinateDerivative i f x))
    (g := fun x => (f x)^2)
    ((hFs.add hgrad).sub (hP.const_mul 2)) hf2.integrable_sq,
    integral_sub
    (f := fun x => (∑ i, (F i x)^2) + gradientSquare f x)
    (g := fun x => 2 * (∑ i, F i x * coordinateDerivative i f x))
    (hFs.add hgrad) (hP.const_mul 2),
    integral_add hFs hgrad,
    integral_const_mul, integral_const_mul,
    integral_finset_sum _ (fun i _ => (hF i).integrable_sq)] at hp
  linarith

end GaussianTilt.Letwin
