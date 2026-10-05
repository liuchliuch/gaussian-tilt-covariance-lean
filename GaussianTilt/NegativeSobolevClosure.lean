import GaussianTilt.NegativeSobolevGenerator

/-!
# Passage of the proved duality estimate to the actual generator closure

This is the continuous extension step. It does not assert that the generator
closure exhausts mean-zero L²; that is the separate elliptic range theorem.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ContDiff Topology ENNReal InnerProductSpace
namespace GaussianTilt.Letwin

lemma norm_toLp_sq_eq_integral {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖^2 = ∫ x, f x^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  simp [hx, RCLike.inner_apply, pow_two]

lemma inner_toLp_weightedLaplacian {n : ℕ} {φ f : CoordinateSpace n → ℝ}
    [IsFiniteMeasure (potentialMeasure φ)] (hφ : ContDiff ℝ ∞ φ)
    (hf : MemLp f 2 (potentialMeasure φ)) (u : smoothCompactCore n) :
    inner ℝ (hf.toLp f) (weightedLaplacianToL2 hφ u) =
      ∫ x, f x * weightedLaplacian φ u.1 x ∂potentialMeasure φ := by
  rw [L2.inner_def]
  have hu := smoothCompactToL2_ae (potentialMeasure φ) (smoothCompactWeightedLaplacian hφ u)
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hu] with x hx hy
  change weightedLaplacianToL2 hφ u x = weightedLaplacian φ u.1 x at hy
  simp only [hx, hy, RCLike.inner_apply, conj_trivial]
  ring

lemma norm_weightedLaplacianToL2_sq {n : ℕ} {φ : CoordinateSpace n → ℝ}
    [IsFiniteMeasure (potentialMeasure φ)] (hφ : ContDiff ℝ ∞ φ) (u : smoothCompactCore n) :
    ‖weightedLaplacianToL2 hφ u‖^2 =
      ∫ x, (weightedLaplacian φ u.1 x)^2 ∂potentialMeasure φ :=
  norm_toLp_sq_eq_integral (smooth_compact_memLp
    (smooth_weightedLaplacian hφ u.2.1) (weightedLaplacian_hasCompactSupport φ u.2.2))

/-- The full dual estimate for every smooth L² observable in the actual
norm-closed generator range. No Poincaré or variance inequality is assumed. -/
theorem variance_le_dual_sq_of_mem_generatorClosure {n : ℕ} {φ f : CoordinateSpace n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ ∞ φ) (hf : ContDiff ℝ ∞ f)
    (hfL : MemLp f 2 (potentialMeasure φ))
    (hH : ∀ x, (coordinateHessian φ x).PosSemidef)
    (hclosure : hfL.toLp f ∈ (LinearMap.range (weightedLaplacianToL2 hφ)).topologicalClosure)
    (C : Fin n → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hB : ∀ i, CompactNegativeSobolevBound (potentialMeasure φ) (coordinateDerivative i f) (C i)) :
    variance f (potentialMeasure φ) ≤ ∑ i, C i^2 := by
  have hnorm : ‖hfL.toLp f‖^2 ≤ ∑ i, C i^2 := by
    apply sq_norm_le_of_core_pairing (LinearMap.range (weightedLaplacianToL2 hφ))
      (hfL.toLp f) (∑ i, C i^2) (Finset.sum_nonneg fun _ _ => sq_nonneg _) hclosure
    rintro _ ⟨u, rfl⟩
    rw [inner_toLp_weightedLaplacian, norm_weightedLaplacianToL2_sq]
    exact generator_pairing_sq_le hφ hf u.2.1 u.2.2 hH C hC hB
  rw [norm_toLp_sq_eq_integral] at hnorm
  calc
    variance f (potentialMeasure φ) ≤ ∫ x, f x^2 ∂potentialMeasure φ := by
      rw [variance_eq_sub hfL]
      exact sub_le_self _ (sq_nonneg _)
    _ ≤ _ := hnorm

/-- If the elliptic theorem identifies the actual range closure, centering
and the proved duality machinery yield the desired variance inequality. This
lemma isolates only the final composition; the range identity must itself be
proved before an application can use the final result. -/
theorem variance_le_dual_sq_of_generatorClosure_eq {n : ℕ} {φ f : CoordinateSpace n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ ∞ φ) (hf : ContDiff ℝ ∞ f)
    (hfL : MemLp f 2 (potentialMeasure φ))
    (hH : ∀ x, (coordinateHessian φ x).PosSemidef)
    (hrange : (LinearMap.range (weightedLaplacianToL2 hφ)).topologicalClosure =
      meanZeroL2 (potentialMeasure φ))
    (C : Fin n → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hB : ∀ i, CompactNegativeSobolevBound (potentialMeasure φ) (coordinateDerivative i f) (C i)) :
    variance f (potentialMeasure φ) ≤ ∑ i, C i^2 := by
  let μ := potentialMeasure φ
  let m := ∫ x, f x ∂μ
  let g := fun x => f x - m
  have hg : ContDiff ℝ ∞ g := hf.sub contDiff_const
  have hgL : MemLp g 2 μ := hfL.sub (memLp_const m)
  have hg0 : (∫ x, g x ∂μ) = 0 := by
    rw [integral_sub (hfL.integrable (by norm_num)) (integrable_const m)]
    simp only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul]
    exact sub_self m
  have hgc : hgL.toLp g ∈ (LinearMap.range (weightedLaplacianToL2 hφ)).topologicalClosure := by
    rw [hrange, mem_meanZeroL2_iff]
    exact (integral_congr_ae hgL.coeFn_toLp).trans hg0
  have hd (i : Fin n) : coordinateDerivative i g = coordinateDerivative i f := by
    funext x
    simp [g, coordinateDerivative, fderiv_sub_const]
  have hb := variance_le_dual_sq_of_mem_generatorClosure hφ hg hgL hH hgc C hC
    (fun i => by rw [hd]; exact hB i)
  simpa only [g, variance_sub_const hfL.aestronglyMeasurable m] using hb

end GaussianTilt.Letwin
