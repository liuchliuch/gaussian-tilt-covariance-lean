import GaussianTilt.LetwinSteinBounds

/-! # Linear-functional duality for an actual integrable Stein coupling -/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators ENNReal
namespace GaussianTilt.Letwin

set_option maxHeartbeats 600000 in
/-- Integral Cauchy–Schwarz after the coordinate Stein identities. All
integrability hypotheses concern actual functions on the same probability
space; the conclusion is a test pairing, not a variance assertion. -/
theorem stein_coupling_dual_sq {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} {Z D : Ω → ι → ℝ} {A : Ω → Matrix ι ι ℝ} {q : Ω → ℝ}
    (hZ : ∀ i, MemLp (fun x => Z x i) 2 μ)
    (hA : ∀ i j, MemLp (fun x => A x i j) 2 μ)
    (hD : ∀ i, MemLp (fun x => D x i) 2 μ) (hq : MemLp q 2 μ)
    (hstein : ∀ i, (∫ x, Z x i * q x ∂μ) = ∫ x, (A x *ᵥ D x) i ∂μ)
    (v : ι → ℝ) :
    (∫ x, (v ⬝ᵥ Z x) * q x ∂μ)^2 ≤
      (∫ x, ∑ j, (A x |>.transpose |>.mulVec v) j ^ 2 ∂μ) *
      ∫ x, ∑ j, D x j ^ 2 ∂μ := by
  have hFi (i : ι) := (hZ i).integrable_mul hq
  have hGi (i : ι) : Integrable (fun x => (A x *ᵥ D x) i) μ := by
    simp only [Matrix.mulVec, dotProduct]
    exact integrable_finset_sum _ (fun j _ => (hA i j).integrable_mul (hD j))
  have heq : (∫ x, (v ⬝ᵥ Z x) * q x ∂μ) =
      ∫ x, (A x |>.transpose |>.mulVec v) ⬝ᵥ D x ∂μ := by
    calc
      _ = ∫ x, v ⬝ᵥ (fun i => Z x i * q x) ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        simp only [dotProduct, Finset.sum_mul, mul_assoc]
      _ = v ⬝ᵥ (fun i => ∫ x, Z x i * q x ∂μ) := integral_dotProduct hFi v
      _ = v ⬝ᵥ (fun i => ∫ x, (A x *ᵥ D x) i ∂μ) := by simp only [hstein]
      _ = ∫ x, v ⬝ᵥ (A x *ᵥ D x) ∂μ := (integral_dotProduct hGi v).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with x
        rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
  rw [heq]
  apply integral_sum_mul_sq_le
  · intro j
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    exact memLp_finset_sum _ (fun i _ => (hA i j).mul_const (v i))
  · exact hD

end GaussianTilt.Letwin
