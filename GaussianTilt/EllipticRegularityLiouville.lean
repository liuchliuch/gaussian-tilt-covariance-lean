import GaussianTilt.EllipticRegularityCutoffs
import GaussianTilt.EllipticRegularityLocal

/-! # Smooth L² Liouville theorem from constructed cutoffs -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ContDiff Topology ENNReal InnerProductSpace
namespace GaussianTilt.Letwin

/-- Every fixed compact cutoff is eventually dominated by the constructed
large-scale cutoff. This uses the actual support radius, not a cutoff axiom. -/
lemma ellipticCutoff_sq_eventually_le {n : ℕ} {R : ℝ} (hR : 0 < R) :
    ∀ᶠ k : ℕ in atTop, ∀ x : CoordinateSpace n,
      ellipticCutoff n R x ^ 2 ≤ ellipticCutoff n ((k : ℝ) + 1) x ^ 2 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * R)
  filter_upwards [eventually_ge_atTop N] with k hk x
  by_cases hx : 2 * R ≤ ‖x‖
  · rw [ellipticCutoff_eq_zero hR hx, zero_pow (by norm_num)]
    exact sq_nonneg _
  · have hnorm : ‖x‖ ≤ (k : ℝ) + 1 := by
      have : (N : ℝ) ≤ k := by exact_mod_cast hk
      push_neg at hx
      linarith
    rw [ellipticCutoff_eq_one (by positivity) hnorm, one_pow]
    nlinarith [ellipticCutoff_nonneg n R x, ellipticCutoff_le_one n R x]

/-- Every fixed cutoff energy of a smooth L² weakly harmonic function vanishes. -/
theorem integral_ellipticCutoff_gradientSquare_eq_zero {n : ℕ}
    (μ : Measure (CoordinateSpace n)) [IsFiniteMeasureOnCompacts μ]
    {h : CoordinateSpace n → ℝ} (hh : ContDiff ℝ ∞ h)
    (hL2 : Integrable (fun x => h x ^ 2) μ)
    (hweak : ∀ v : CoordinateSpace n → ℝ, ContDiff ℝ ∞ v → HasCompactSupport v →
      (∫ x, ∑ i, coordinateDerivative i h x * coordinateDerivative i v x ∂μ) = 0)
    {R : ℝ} (hR : 0 < R) :
    (∫ x, ellipticCutoff n R x ^ 2 * gradientSquare h x ∂μ) = 0 := by
  obtain ⟨C, hC, hCb⟩ := ellipticCutoff_gradient_bound n
  have hint (S : ℝ) (hS : S ≠ 0) : Integrable
      (fun x => ellipticCutoff n S x ^ 2 * gradientSquare h x) μ :=
    (((ellipticCutoff_contDiff n S).continuous.pow 2).mul
      (continuous_gradientSquare hh)).integrable_of_hasCompactSupport (by
        simpa only [pow_two] using
          ((ellipticCutoff_compact n hS).mul_right
            (f' := ellipticCutoff n S)).mul_right (f' := gradientSquare h))
  have hbound (S : ℝ) (hS : 0 < S) :
      (∫ x, ellipticCutoff n S x ^ 2 * gradientSquare h x ∂μ) ≤
        4 * (S⁻¹ ^ 2 * C) * ∫ x, h x ^ 2 ∂μ := by
    apply (integral_cutoff_gradientSquare_le μ hh (ellipticCutoff_contDiff n S)
      (ellipticCutoff_compact n hS.ne') hweak).trans
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    rw [← integral_const_mul]
    have hi : Integrable (fun x => h x ^ 2 * gradientSquare (ellipticCutoff n S) x) μ :=
      ((hh.continuous.pow 2).mul (continuous_gradientSquare (ellipticCutoff_contDiff n S))).integrable_of_hasCompactSupport
        (gradientSquare_hasCompactSupport (ellipticCutoff_compact n hS.ne')).mul_left
    apply integral_mono hi (hL2.const_mul _)
    intro x
    nlinarith [mul_le_mul_of_nonneg_left (hCb S x) (sq_nonneg (h x))]
  apply le_antisymm ?_ (integral_nonneg fun x =>
    mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  have ht : Tendsto (fun k : ℕ =>
      4 * (((k : ℝ) + 1)⁻¹ ^ 2 * C) * ∫ x, h x ^ 2 ∂μ) atTop (𝓝 0) := by
    convert ((tendsto_one_div_add_atTop_nhds_zero_nat.pow 2).mul_const C).const_mul 4
      |>.mul_const (∫ x, h x ^ 2 ∂μ) using 1 <;> simp [one_div]
  apply le_of_tendsto_of_tendsto tendsto_const_nhds ht
  filter_upwards [ellipticCutoff_sq_eventually_le hR] with k hk
  apply (integral_mono (hint R hR.ne') (hint ((k : ℝ) + 1) (by positivity))
    (fun x => mul_le_mul_of_nonneg_right (hk x)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _))).trans
  exact hbound _ (by positivity)

/-- A smooth weakly harmonic L² function on the full-support weighted space
is constant. The proof uses only the constructed cutoffs and Caccioppoli. -/
theorem smooth_L2_weak_harmonic_const {n : ℕ}
    (μ : Measure (CoordinateSpace n)) [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    {h : CoordinateSpace n → ℝ} (hh : ContDiff ℝ ∞ h)
    (hL2 : Integrable (fun x => h x ^ 2) μ)
    (hweak : ∀ v : CoordinateSpace n → ℝ, ContDiff ℝ ∞ v → HasCompactSupport v →
      (∫ x, ∑ i, coordinateDerivative i h x * coordinateDerivative i v x ∂μ) = 0) :
    ∀ x y, h x = h y := by
  have hz (x : CoordinateSpace n) : gradientSquare h x = 0 := by
    let R := ‖x‖ + 1
    have hR : 0 < R := by dsimp [R]; positivity
    have hi : Integrable (fun y => ellipticCutoff n R y ^ 2 * gradientSquare h y) μ :=
      (((ellipticCutoff_contDiff n R).continuous.pow 2).mul
        (continuous_gradientSquare hh)).integrable_of_hasCompactSupport (by
          simpa only [pow_two] using
            ((ellipticCutoff_compact n hR.ne').mul_right
              (f' := ellipticCutoff n R)).mul_right (f' := gradientSquare h))
    have he : (fun y => ellipticCutoff n R y ^ 2 * gradientSquare h y) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun y => mul_nonneg (sq_nonneg _)
        (Finset.sum_nonneg fun _ _ => sq_nonneg _)) hi).mp
        (integral_ellipticCutoff_gradientSquare_eq_zero μ hh hL2 hweak hR)
    have hf := Measure.eq_of_ae_eq he
      (((ellipticCutoff_contDiff n R).continuous.pow 2).mul (continuous_gradientSquare hh))
      continuous_const
    have hx := congrFun hf x
    rw [ellipticCutoff_eq_one hR (by dsimp [R]; linarith), one_pow, one_mul] at hx
    exact hx
  have hd (x : CoordinateSpace n) (i : Fin n) : coordinateDerivative i h x = 0 := by
    have hi : (coordinateDerivative i h x)^2 ≤ gradientSquare h x :=
      Finset.single_le_sum (fun j _ => sq_nonneg (coordinateDerivative j h x)) (Finset.mem_univ i)
    rw [hz x] at hi
    nlinarith [sq_nonneg (coordinateDerivative i h x)]
  apply is_const_of_fderiv_eq_zero (hh.differentiable (by simp))
  intro x
  ext v
  rw [← Finset.univ_sum_single v, map_sum]
  simp only [ContinuousLinearMap.zero_apply]
  have hv (i : Fin n) : (fderiv ℝ h x) (Pi.single i (v i)) = 0 := by
    have he : Pi.single i (v i) = v i • (Pi.single i 1 : CoordinateSpace n) := by
      ext j
      by_cases hj : j = i
      · subst j; simp
      · simp [hj]
    rw [he, map_smul]
    change v i * coordinateDerivative i h x = 0
    rw [hd x i, mul_zero]
  exact Finset.sum_eq_zero fun i _ => hv i

/-- The actual weighted elliptic equation has no nonconstant smooth L²
solutions, for every smooth potential giving a finite measure. -/
theorem smooth_L2_weightedLaplacian_zero_const {n : ℕ} {φ h : CoordinateSpace n → ℝ}
    [IsFiniteMeasure (potentialMeasure φ)] (hφ : ContDiff ℝ ∞ φ)
    (hh : ContDiff ℝ ∞ h) (hL2 : MemLp h 2 (potentialMeasure φ))
    (heq : ∀ x, weightedLaplacian φ h x = 0) : ∀ x y, h x = h y := by
  letI := potentialMeasure_isOpenPosMeasure hφ.continuous
  apply smooth_L2_weak_harmonic_const (potentialMeasure φ) hh hL2.integrable_sq
  intro v hv hvc
  exact weightedLaplacian_zero_weak hφ hh heq hv hvc

end GaussianTilt.Letwin
