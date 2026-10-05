import GaussianTilt.EllipticRegularityWeightedLocal
import GaussianTilt.EllipticRegularityCutoffPairing
import GaussianTilt.EllipticRegularityPairing
import GaussianTilt.EllipticRegularityZeroGradient

/-!
# The genuine rough weighted L² Liouville theorem

A rough L² annihilator of the actual compact smooth generator is locally H¹
by proved elliptic regularity. The actual η²h test gives Caccioppoli; growing
constructed cutoffs force each distributional derivative to vanish. The
mollification/Lebesgue-point argument then proves that h is a.e. constant.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ContDiff Topology ENNReal InnerProductSpace
namespace GaussianTilt.Letwin

lemma weighted_annihilator_derivative_pairing_sq_le {n : ℕ}
    {φ h ψ : CoordinateSpace n → ℝ} [IsFiniteMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ ∞ φ) (hh : MemLp h 2 (potentialMeasure φ))
    (horth : ∀ f : CoordinateSpace n → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      (∫ x, h x * weightedLaplacian φ f x ∂potentialMeasure φ) = 0)
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    {C : ℝ} (hC : 0 ≤ C)
    (hCb : ∀ S : ℝ, ∀ x : CoordinateSpace n, gradientSquare (ellipticCutoff n S) x ≤ S⁻¹^2*C)
    {R : ℝ} (hR : 0 < R) (hψR : ∀ x ∈ tsupport ψ, ‖x‖ ≤ R) (i : Fin n) :
    (∫ x, h x * coordinateDerivative i ψ x)^2 ≤
      4 * (R⁻¹^2*C) * (∫ x, h x^2 ∂potentialMeasure φ) *
        (∫ x, (weightedExponentTest hφ hψ hψc).1 x^2 ∂potentialMeasure φ) := by
  let μ := potentialMeasure φ
  obtain ⟨u, hu⟩ := weighted_generator_orthogonal_local_weighted_H1 hφ hh
    (ellipticCutoff_contDiff n (2*R)) (ellipticCutoff_compact n (by positivity)) horth
  have hχ : ∀ x ∈ tsupport ψ, ellipticCutoff n (2*R) x = 1 := by
    intro x hx
    apply ellipticCutoff_eq_one (by positivity)
    linarith [hψR x hx]
  have hE := localized_weightedSobolev_caccioppoli hφ (ellipticCutoff_contDiff n R)
    (ellipticCutoff_compact n hR.ne') u hu horth (ellipticCutoff_one_on_tsupport hR)
  have hE2 := integral_value_sq_gradient_le μ (u.1 0) (ellipticCutoff_contDiff n R)
    (ellipticCutoff_compact n hR.ne') (hCb R)
  have hv := integral_cutoff_value_sq_le μ (u.1 0) hh hu
    (ellipticCutoff_nonneg n (2*R)) (ellipticCutoff_le_one n (2*R))
  have henergy : (∫ x, ellipticCutoff n R x^2 * (∑ j : Fin n, (u.1 j.succ x)^2) ∂μ) ≤
      4 * (R⁻¹^2*C) * ∫ x, h x^2 ∂μ := by
    calc
      _ ≤ 4 * ∫ x, (u.1 0 x)^2 * gradientSquare (ellipticCutoff n R) x ∂μ := hE
      _ ≤ 4 * ((R⁻¹^2*C) * ∫ x, (u.1 0 x)^2 ∂μ) :=
        mul_le_mul_of_nonneg_left hE2 (by norm_num)
      _ ≤ 4 * ((R⁻¹^2*C) * ∫ x, h x^2 ∂μ) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hv (mul_nonneg (sq_nonneg _) hC)) (by norm_num)
      _ = _ := by ring
  have hcs := cutoff_gradient_pairing_sq_le μ (fun j : Fin n => u.1 j.succ) i
    (weightedExponentTest hφ hψ hψc) (ellipticCutoff_contDiff n R)
    (ellipticCutoff_compact n hR.ne') (fun x hx => by
      apply ellipticCutoff_eq_one hR
      apply hψR x
      exact tsupport_mul_subset_right (f := fun y => Real.exp (φ y)) (g := ψ) hx)
  rw [localized_weightedSobolev_unweighted_derivative_pairing hφ hψ hψc u hu hχ i, neg_sq]
  exact hcs.trans (mul_le_mul_of_nonneg_right henergy (integral_nonneg fun x => sq_nonneg _))

/-- Every rough weighted L² generator annihilator has actual zero
unweighted distributional gradient. The growing-radius limit is proved. -/
theorem weighted_generator_orthogonal_zeroDistributionGradient {n : ℕ}
    {φ h : CoordinateSpace n → ℝ} [IsFiniteMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ ∞ φ) (hh : MemLp h 2 (potentialMeasure φ))
    (horth : ∀ f : CoordinateSpace n → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      (∫ x, h x * weightedLaplacian φ f x ∂potentialMeasure φ) = 0) :
    HasZeroDistributionGradient h := by
  intro i ψ hψ hψc
  obtain ⟨C, hC, hCb⟩ := ellipticCutoff_gradient_bound n
  obtain ⟨S, hS, hψS⟩ := hψc.isBounded.subset_closedBall_lt 0 (0 : CoordinateSpace n)
  obtain ⟨N, hN⟩ := exists_nat_gt S
  let M := ∫ x, h x^2 ∂potentialMeasure φ
  let Q := ∫ x, (weightedExponentTest hφ hψ hψc).1 x^2 ∂potentialMeasure φ
  have ht : Tendsto (fun k : ℕ => 4 * (((k : ℝ)+1)⁻¹^2*C) * M * Q) atTop (𝓝 0) := by
    convert ((((tendsto_one_div_add_atTop_nhds_zero_nat.pow 2).mul_const C).const_mul 4).mul_const M).mul_const Q using 1 <;> simp [one_div]
  have hs : (∫ x, h x * coordinateDerivative i ψ x)^2 ≤ 0 := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds ht
    filter_upwards [eventually_ge_atTop N] with k hk
    apply weighted_annihilator_derivative_pairing_sq_le hφ hh horth hψ hψc hC hCb (by positivity) _ i
    intro x hx
    have hxS : ‖x‖ ≤ S := by simpa only [Metric.mem_closedBall, dist_zero_right] using hψS hx
    have hNk : (N : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  nlinarith [sq_nonneg (∫ x, h x * coordinateDerivative i ψ x)]

/-- Genuine rough weighted Liouville: annihilating L(C∞c) forces a constant,
with all local regularity, cutoff testing and convergence steps proved. -/
theorem weighted_generator_orthogonal_ae_const {n : ℕ}
    {φ h : CoordinateSpace n → ℝ} [IsFiniteMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ ∞ φ) (hh : MemLp h 2 (potentialMeasure φ))
    (horth : ∀ f : CoordinateSpace n → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      (∫ x, h x * weightedLaplacian φ f x ∂potentialMeasure φ) = 0) :
    ∃ c : ℝ, h =ᵐ[potentialMeasure φ] fun _ => c := by
  obtain ⟨c, hc⟩ := (weighted_generator_orthogonal_zeroDistributionGradient hφ hh horth).ae_eq_const
    (locallyIntegrable_of_potential_memLp hφ.continuous hh)
  exact ⟨c, (potentialMeasure_absolutelyContinuous φ).ae_eq hc⟩

end GaussianTilt.Letwin
