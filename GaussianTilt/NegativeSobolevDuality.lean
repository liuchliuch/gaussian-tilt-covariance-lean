import GaussianTilt.NegativeSobolevBochner

/-!
# Negative Sobolev test duality

The norm is the actual supremum over locally Lipschitz L² tests of unit
Dirichlet energy (absolute value is harmless because tests are closed under
negation).  Compact smooth tests are only used in the proof, and their
normalization, including the zero-energy case, is established here.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix Filter
open scoped BigOperators ContDiff Topology ENNReal
namespace GaussianTilt.Letwin

/-- The H⁻¹ norm with the full locally Lipschitz L² test class, as an extended
nonnegative real so that the infinite case is not lost by a real supremum. -/
def negativeSobolevNorm {n : ℕ} (μ : Measure (CoordinateSpace n))
    (f : CoordinateSpace n → ℝ) : ℝ≥0∞ :=
  ⨆ (g : CoordinateSpace n → ℝ) (_ : MemLp g 2 μ) (_ : LocallyLipschitz g)
    (_ : Integrable (gradientSquare g) μ)
    (_ : (∫ x, gradientSquare g x ∂μ) ≤ 1), ENNReal.ofReal |∫ x, f x * g x ∂μ|

/-- A real bound for the unit-energy compact smooth tests. This records only
individual pairings, not any variance or Poincaré assertion. -/
def CompactNegativeSobolevBound {n : ℕ} (μ : Measure (CoordinateSpace n))
    (f : CoordinateSpace n → ℝ) (C : ℝ) : Prop :=
  ∀ (g : CoordinateSpace n → ℝ), ContDiff ℝ ∞ g → HasCompactSupport g →
    (∫ x, gradientSquare g x ∂μ) ≤ 1 → |∫ x, f x * g x ∂μ| ≤ C

lemma smooth_compact_memLp {n : ℕ} {μ : Measure (CoordinateSpace n)} [IsFiniteMeasureOnCompacts μ]
    {g : CoordinateSpace n → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    MemLp g 2 μ :=
  hg.continuous.memLp_of_hasCompactSupport hgc

lemma compactNegativeSobolevBound_of_norm_le {n : ℕ}
    {μ : Measure (CoordinateSpace n)} [IsFiniteMeasure μ]
    {f : CoordinateSpace n → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hN : negativeSobolevNorm μ f ≤ ENNReal.ofReal C) :
    CompactNegativeSobolevBound μ f C := by
  intro g hg hgc hge
  have hb : ENNReal.ofReal |∫ x, f x * g x ∂μ| ≤ negativeSobolevNorm μ f := by
    exact le_iSup_of_le g (le_iSup_of_le (smooth_compact_memLp hg hgc)
      (le_iSup_of_le ((contDiff_infty.mp hg 1).locallyLipschitz)
        (le_iSup_of_le ((continuous_gradientSquare hg).integrable_of_hasCompactSupport
          (gradientSquare_hasCompactSupport hgc)) (le_iSup_of_le hge le_rfl))))
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp (hb.trans hN)

lemma gradientSquare_const_mul {n : ℕ} {g : CoordinateSpace n → ℝ}
    (hg : ContDiff ℝ ∞ g) (c : ℝ) (x : CoordinateSpace n) :
    gradientSquare (fun y => c * g y) x = c^2 * gradientSquare g x := by
  have hd (i : Fin n) : coordinateDerivative i (fun y => c * g y) x = c * coordinateDerivative i g x := by
    unfold coordinateDerivative
    rw [((hg.differentiable (by simp) x).hasFDerivAt.const_mul c).fderiv]
    simp
  simp only [gradientSquare, hd, mul_pow, Finset.mul_sum]

/-- Homogeneity upgrades unit-test duality to arbitrary compact smooth tests.
The proof treats zero Dirichlet energy by rescaling, rather than dividing by
zero or presupposing a Poincaré inequality. -/
theorem CompactNegativeSobolevBound.pairing_le {n : ℕ}
    {μ : Measure (CoordinateSpace n)} {f g : CoordinateSpace n → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hB : CompactNegativeSobolevBound μ f C)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    |∫ x, f x * g x ∂μ| ≤ C * Real.sqrt (∫ x, gradientSquare g x ∂μ) := by
  let E := ∫ x, gradientSquare g x ∂μ
  let P := |∫ x, f x * g x ∂μ|
  have hE : 0 ≤ E := integral_nonneg fun x => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hscale (c : ℝ) (hc : c^2 * E ≤ 1) : |c| * P ≤ C := by
    have ht := hB (fun x => c * g x) (contDiff_const.mul hg) hgc.mul_left
      (by simpa only [gradientSquare_const_mul hg, integral_const_mul] using hc)
    have hp : (∫ x, f x * (c * g x) ∂μ) = c * ∫ x, f x * g x ∂μ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      ring
    simpa only [hp, abs_mul] using ht
  by_cases hE0 : E = 0
  · have hP : P = 0 := by
      by_contra hP
      have hPpos : 0 < P := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hP)
      have ht := hscale ((C + 1) / P) (by simp [hE0])
      rw [abs_of_pos (div_pos (by linarith) hPpos)] at ht
      have he : (C + 1) / P * P = C + 1 := div_mul_cancel₀ _ hP
      rw [he] at ht
      linarith
    change P ≤ C * Real.sqrt E
    simp [hP, hE0]
  · have hEs : 0 < Real.sqrt E := Real.sqrt_pos.2 (lt_of_le_of_ne hE (Ne.symm hE0))
    have hs := Real.sq_sqrt hE
    have hc : (Real.sqrt E)⁻¹ ^2 * E = 1 := by
      calc
        _ = (Real.sqrt E)⁻¹ ^2 * (Real.sqrt E)^2 := by rw [hs]
        _ = 1 := by rw [← mul_pow, inv_mul_cancel₀ hEs.ne']; norm_num
    have ht := hscale ((Real.sqrt E)⁻¹) hc.le
    rw [abs_of_pos (inv_pos.mpr hEs)] at ht
    have hm := mul_le_mul_of_nonneg_left ht hEs.le
    have he : Real.sqrt E * ((Real.sqrt E)⁻¹ * P) = P := by field_simp
    rw [he] at hm
    simpa only [mul_comm] using hm

/-- The finite-dimensional Cauchy step in the negative-Sobolev proof. -/
lemma sum_pairings_sq_le {ι : Type*} [Fintype ι]
    (a C E : ι → ℝ) (hC : ∀ i, 0 ≤ C i) (hE : ∀ i, 0 ≤ E i)
    (ha : ∀ i, |a i| ≤ C i * Real.sqrt (E i)) :
    (∑ i, a i)^2 ≤ (∑ i, C i ^2) * ∑ i, E i := by
  have h₁ : |∑ i, a i| ≤ ∑ i, C i * Real.sqrt (E i) :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ha i)
  have h₂ : (∑ i, C i * Real.sqrt (E i))^2 ≤ (∑ i, C i^2) * ∑ i, E i := by
    simpa only [Real.sq_sqrt (hE _)] using
      (Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ) C (fun i => Real.sqrt (E i)))
  have hsum : 0 ≤ ∑ i, C i * Real.sqrt (E i) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hC i) (Real.sqrt_nonneg _)
  nlinarith [sq_abs (∑ i, a i), abs_nonneg (∑ i, a i)]

/-- Negative Sobolev duality for a function that is the actual weighted
Laplacian of a compact smooth function. Both Green and Bochner are proved
analytic theorems, not premises in this statement. -/
theorem laplacian_variance_le_sum_dual_sq {n : ℕ} {φ u : CoordinateSpace n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ ∞ φ) (hu : ContDiff ℝ ∞ u) (huc : HasCompactSupport u)
    (hH : ∀ x, (coordinateHessian φ x).PosSemidef)
    (C : Fin n → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hB : ∀ i, CompactNegativeSobolevBound (potentialMeasure φ)
      (coordinateDerivative i (weightedLaplacian φ u)) (C i)) :
    variance (weightedLaplacian φ u) (potentialMeasure φ) ≤ ∑ i, C i^2 := by
  let μ := potentialMeasure φ
  let f := weightedLaplacian φ u
  let V := ∫ x, f x ^2 ∂μ
  let E := fun i => ∫ x, gradientSquare (coordinateDerivative i u) x ∂μ
  let a := fun i => ∫ x, coordinateDerivative i f x * coordinateDerivative i u x ∂μ
  have hs := smooth_weightedLaplacian hφ hu
  have hsc := weightedLaplacian_hasCompactSupport φ huc
  have hdc (i : Fin n) : HasCompactSupport (coordinateDerivative i u) :=
    huc.fderiv_apply (𝕜 := ℝ) (Pi.single i 1)
  have hdi (i : Fin n) : Integrable
      (fun x => coordinateDerivative i u x * coordinateDerivative i f x) μ :=
    ((smooth_coordinateDerivative hu i).continuous.mul
      (smooth_coordinateDerivative hs i).continuous).integrable_of_hasCompactSupport (hdc i).mul_right
  have hgreen := integral_divergenceDiffusion_mul_compact_left (A := fun _ => 1)
    (contDiff_infty.mp hφ 1) (fun _ _ => contDiff_const) (contDiff_infty.mp hu 2)
    (contDiff_infty.mp hs 1) huc
  have hV : V = -(∑ i, a i) := by
    change (∫ x, f x * f x ∂μ) = -(∫ x, diffusionGamma (fun _ => 1) u f x ∂μ) at hgreen
    simpa only [V, a, diffusionGamma_one, ← pow_two,
      integral_finset_sum _ (fun i _ => hdi i), mul_comm] using hgreen
  have hb : (∑ i, a i)^2 ≤ (∑ i, C i^2) * ∑ i, E i :=
    sum_pairings_sq_le a C E hC
      (fun i => integral_nonneg fun x => Finset.sum_nonneg fun _ _ => sq_nonneg _)
      (fun i => (hB i).pairing_le (hC i) (smooth_coordinateDerivative hu i) (hdc i))
  have hbochner : (∑ i, E i) ≤ V :=
    sum_integral_gradientSquare_le_laplacian_sq hφ hu huc hH
  have hCs : 0 ≤ ∑ i, C i^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hV0 : 0 ≤ V := integral_nonneg fun _ => sq_nonneg _
  have hVb : V ≤ ∑ i, C i^2 := by
    have hb' := hb.trans (mul_le_mul_of_nonneg_left hbochner hCs)
    rw [← neg_eq_iff_eq_neg.mpr hV, neg_sq] at hb'
    nlinarith
  calc
    variance f μ ≤ ∫ x, f x^2 ∂μ := by
      rw [variance_eq_sub (smooth_compact_memLp hs hsc)]
      exact sub_le_self _ (sq_nonneg _)
    _ ≤ _ := hVb

/-- The genuine extended-real H⁻¹ inequality on the smooth compact generator
range. The remaining extension to all centered L² observables is a separate
range-density theorem; this statement does not assume that extension. -/
theorem laplacian_variance_le_negativeSobolev {n : ℕ} {φ u : CoordinateSpace n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ ∞ φ) (hu : ContDiff ℝ ∞ u) (huc : HasCompactSupport u)
    (hH : ∀ x, (coordinateHessian φ x).PosSemidef) :
    ENNReal.ofReal (variance (weightedLaplacian φ u) (potentialMeasure φ)) ≤
      ∑ i, (negativeSobolevNorm (potentialMeasure φ)
        (coordinateDerivative i (weightedLaplacian φ u)))^2 := by
  let N := fun i => negativeSobolevNorm (potentialMeasure φ)
    (coordinateDerivative i (weightedLaplacian φ u))
  by_cases hfin : ∀ i, N i ≠ ⊤
  · have hb := laplacian_variance_le_sum_dual_sq hφ hu huc hH
      (fun i => (N i).toReal) (fun i => ENNReal.toReal_nonneg)
      (fun i => compactNegativeSobolevBound_of_norm_le ENNReal.toReal_nonneg
        (by rw [ENNReal.ofReal_toReal (hfin i)]))
    have hcast := ENNReal.ofReal_le_ofReal hb
    simpa only [ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg ((N i).toReal)),
      ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hfin _)] using hcast
  · push_neg at hfin
    obtain ⟨i, hi⟩ := hfin
    have ht : (∑ j, N j ^2) = ⊤ := by
      apply (ENNReal.sum_eq_top).2
      exact ⟨i, Finset.mem_univ i, by simp [hi]⟩
    change _ ≤ ∑ j, N j ^2
    rw [ht]
    exact le_top

end GaussianTilt.Letwin
