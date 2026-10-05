import GaussianTilt.NegativeSobolevClosure

/-! # Negative Sobolev duality for the constructed weak Sobolev space -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ContDiff Topology ENNReal InnerProductSpace
namespace GaussianTilt.Letwin

lemma inner_smoothCompact_right {n : ℕ} (μ : Measure (CoordinateSpace n))
    [IsFiniteMeasureOnCompacts μ] (f : Lp ℝ 2 μ) (g : smoothCompactCore n) :
    inner ℝ f (smoothCompactToL2 μ g) = ∫ x, f x * g.1 x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [smoothCompactToL2_ae μ g] with x hx
  simp only [hx, RCLike.inner_apply, conj_trivial]
  ring

lemma sum_adjoint_derivative_eq_neg_laplacian {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (v : smoothCompactCore n) :
    (∑ i : Fin n, smoothCompactDerivativeAdjoint hφ i (smoothCompactDerivative i v)) =
      -smoothCompactWeightedLaplacian hφ v := by
  apply Subtype.ext
  funext x
  simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_neg, Pi.neg_apply]
  change (∑ i : Fin n, (coordinateDerivative i φ x * coordinateDerivative i v.1 x -
    coordinateDerivative i (coordinateDerivative i v.1) x)) = -weightedLaplacian φ v.1 x
  rw [weightedLaplacian_apply, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Green's formula for every function of the constructed weak Sobolev
space, derived from its proved integration-by-parts identity. -/
theorem weightedSobolev_generator_green {n : ℕ} {φ : CoordinateSpace n → ℝ}
    [IsFiniteMeasure (potentialMeasure φ)] (hφ : ContDiff ℝ ∞ φ)
    (u : weightedSobolev (potentialMeasure φ)) (v : smoothCompactCore n) :
    inner ℝ (u.1 0) (weightedLaplacianToL2 hφ v) =
      -(∑ i : Fin n, inner ℝ (u.1 i.succ)
        (smoothCompactToL2 (potentialMeasure φ) (smoothCompactDerivative i v))) := by
  simp_rw [weightedSobolev_integration_by_parts hφ u]
  rw [← inner_sum, ← map_sum, sum_adjoint_derivative_eq_neg_laplacian, map_neg,
    inner_neg_right, neg_neg]
  rfl

/-- The true core test estimate also holds for nonsmooth weak H¹ functions;
there is no smoothness hypothesis on the observable represented by u. -/
theorem weightedSobolev_generator_pairing_sq_le {n : ℕ} {φ : CoordinateSpace n → ℝ}
    [IsFiniteMeasure (potentialMeasure φ)] (hφ : ContDiff ℝ ∞ φ)
    (hH : ∀ x, (coordinateHessian φ x).PosSemidef)
    (u : weightedSobolev (potentialMeasure φ)) (v : smoothCompactCore n)
    (C : Fin n → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hB : ∀ i, CompactNegativeSobolevBound (potentialMeasure φ) (u.1 i.succ) (C i)) :
    (inner ℝ (u.1 0) (weightedLaplacianToL2 hφ v))^2 ≤
      (∑ i, C i^2) * ‖weightedLaplacianToL2 hφ v‖^2 := by
  rw [weightedSobolev_generator_green, neg_sq, norm_weightedLaplacianToL2_sq]
  have hpair (i : Fin n) : |inner ℝ (u.1 i.succ)
      (smoothCompactToL2 (potentialMeasure φ) (smoothCompactDerivative i v))| ≤
      C i * Real.sqrt (∫ x, gradientSquare (coordinateDerivative i v.1) x ∂potentialMeasure φ) := by
    rw [inner_smoothCompact_right]
    exact (hB i).pairing_le (hC i) (smooth_coordinateDerivative v.2.1 i)
      (v.2.2.fderiv_apply (𝕜 := ℝ) (Pi.single i 1))
  have hs := sum_pairings_sq_le _ C _ hC
    (fun i => integral_nonneg fun x => Finset.sum_nonneg fun _ _ => sq_nonneg _) hpair
  exact hs.trans (mul_le_mul_of_nonneg_left
    (sum_integral_gradientSquare_le_laplacian_sq hφ v.2.1 v.2.2 hH)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _))

/-- Extension of the true test inequality to the actual generator closure
for arbitrary weak H¹ observables. -/
theorem weightedSobolev_norm_le_dual_sq {n : ℕ} {φ : CoordinateSpace n → ℝ}
    [IsFiniteMeasure (potentialMeasure φ)] (hφ : ContDiff ℝ ∞ φ)
    (hH : ∀ x, (coordinateHessian φ x).PosSemidef)
    (u : weightedSobolev (potentialMeasure φ))
    (hu : u.1 0 ∈ (LinearMap.range (weightedLaplacianToL2 hφ)).topologicalClosure)
    (C : Fin n → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hB : ∀ i, CompactNegativeSobolevBound (potentialMeasure φ) (u.1 i.succ) (C i)) :
    ‖u.1 0‖^2 ≤ ∑ i, C i^2 := by
  apply sq_norm_le_of_core_pairing (LinearMap.range (weightedLaplacianToL2 hφ))
    (u.1 0) _ (Finset.sum_nonneg fun _ _ => sq_nonneg _) hu
  rintro _ ⟨v, rfl⟩
  exact weightedSobolev_generator_pairing_sq_le hφ hH u v C hC hB

end GaussianTilt.Letwin
