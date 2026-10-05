import GaussianTilt.EllipticRegularitySobolevProduct

/-! # Compact Sobolev localization from volume to the genuine Gibbs weight -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ContDiff Topology ENNReal InnerProductSpace
namespace GaussianTilt.Letwin

lemma potentialMeasure_absolutelyContinuous {n : ℕ} (φ : CoordinateSpace n → ℝ) :
    potentialMeasure φ ≪ volume :=
  withDensity_absolutelyContinuous volume (fun x => ENNReal.ofReal (Real.exp (-φ x)))

/-- Pointwise multiplication between two actual L² spaces when its
integrability has been established and the target is absolutely continuous. -/
def l2MultiplierLinearBetween {Ω : Type*} [MeasurableSpace Ω] {μ ν : Measure Ω}
    (hνμ : ν ≪ μ) (a : Ω → ℝ)
    (hmem : ∀ f : Lp ℝ 2 μ, MemLp (fun x => a x*f x) 2 ν) : Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 ν where
  toFun f := (hmem f).toLp (fun x => a x*f x)
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(hmem (f+g)).coeFn_toLp, (hmem f).coeFn_toLp, (hmem g).coeFn_toLp,
      hνμ.ae_eq (Lp.coeFn_add f g), Lp.coeFn_add ((hmem f).toLp (fun x => a x*f x))
        ((hmem g).toLp (fun x => a x*g x))] with x hfg hf hg hadd hsum
    simp only [Pi.add_apply] at hadd hsum
    rw [hfg, hsum, hf, hg, hadd]
    ring
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(hmem (c • f)).coeFn_toLp, (hmem f).coeFn_toLp,
      hνμ.ae_eq (Lp.coeFn_smul c f), Lp.coeFn_smul c ((hmem f).toLp (fun x => a x*f x))] with x hcf hf hsm hsm'
    simp only [Pi.smul_apply, smul_eq_mul] at hsm hsm'
    simp only [RingHom.id_apply]
    rw [hcf, hsm', hf, hsm]
    ring

lemma l2MultiplierLinearBetween_ae {Ω : Type*} [MeasurableSpace Ω] {μ ν : Measure Ω}
    (hνμ : ν ≪ μ) (a : Ω → ℝ)
    (hmem : ∀ f : Lp ℝ 2 μ, MemLp (fun x => a x*f x) 2 ν) (f : Lp ℝ 2 μ) :
    l2MultiplierLinearBetween hνμ a hmem f =ᵐ[ν] fun x => a x*f x :=
  (hmem f).coeFn_toLp

/-- Square-root weighting converts the actual Gibbs L² integral into the
ordinary volume L² integral. -/
lemma potential_squareRoot_weight_identity {n : ℕ} (φ a f : CoordinateSpace n → ℝ)
    (x : CoordinateSpace n) :
    Real.exp (-φ x) * (a x*f x)^2 = (Real.exp (-φ x/2)*a x*f x)^2 := by
  have he : Real.exp (-φ x/2)^2 = Real.exp (-φ x) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  simp only [mul_pow, he]
  ring

lemma potentialMultiplier_memLp {n : ℕ} {φ a : CoordinateSpace n → ℝ}
    (hφ : Continuous φ) (ha : Continuous a) {B : ℝ}
    (hB : ∀ x, ‖Real.exp (-φ x/2)*a x‖ ≤ B) (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n))) :
    MemLp (fun x => a x*f x) 2 (potentialMeasure φ) := by
  have hq : Continuous (fun x => Real.exp (-φ x/2)*a x) := by fun_prop
  have hm := boundedMultiplier_memLp hq.aestronglyMeasurable (Filter.Eventually.of_forall hB) f
  have hfm : AEStronglyMeasurable (fun x => a x*f x) (potentialMeasure φ) :=
    AEStronglyMeasurable.mono_ac (potentialMeasure_absolutelyContinuous φ)
      (ha.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
  apply (memLp_two_iff_integrable_sq hfm).2
  rw [integrable_potentialMeasure_iff hφ]
  simpa only [potential_squareRoot_weight_identity] using hm.integrable_sq

lemma potentialMultiplier_norm_le {n : ℕ} {φ a : CoordinateSpace n → ℝ}
    (hφ : Continuous φ) (ha : Continuous a) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x, ‖Real.exp (-φ x/2)*a x‖ ≤ B)
    (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n))) :
    ‖(potentialMultiplier_memLp hφ ha hB f).toLp (fun x => a x*f x)‖ ≤ B*‖f‖ := by
  have hq : Continuous (fun x => Real.exp (-φ x/2)*a x) := by fun_prop
  let M := boundedL2Multiplier (μ := volume) hq.aestronglyMeasurable hB0 (Filter.Eventually.of_forall hB)
  have hMbound : ‖M f‖ ≤ B*‖f‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [boundedL2Multiplier_ae hq.aestronglyMeasurable hB0
      (Filter.Eventually.of_forall hB) f] with x hx
    rw [hx, norm_mul]
    exact mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _)
  have hsq : ‖(potentialMultiplier_memLp hφ ha hB f).toLp (fun x => a x*f x)‖^2 = ‖M f‖^2 := by
    rw [norm_toLp_sq_eq_integral, integral_potentialMeasure hφ]
    change (∫ x, Real.exp (-φ x)*(a x*f x)^2) =
      ‖(boundedMultiplier_memLp hq.aestronglyMeasurable (Filter.Eventually.of_forall hB) f).toLp
        (fun x => Real.exp (-φ x/2)*a x*f x)‖^2
    rw [norm_toLp_sq_eq_integral]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (potential_squareRoot_weight_identity φ a f)
  have heq : ‖(potentialMultiplier_memLp hφ ha hB f).toLp (fun x => a x*f x)‖ = ‖M f‖ := by
    nlinarith [norm_nonneg ((potentialMultiplier_memLp hφ ha hB f).toLp (fun x => a x*f x)), norm_nonneg (M f)]
  rw [heq]
  exact hMbound

/-- Actual compact localization from Lebesgue L² into Gibbs L². The bound
comes from compactness, not from a globally bounded density hypothesis. -/
def compactPotentialMultiplier {n : ℕ} {φ a : CoordinateSpace n → ℝ}
    (hφ : Continuous φ) (ha : Continuous a) (hac : HasCompactSupport a) :
    Lp ℝ 2 (volume : Measure (CoordinateSpace n)) →L[ℝ] Lp ℝ 2 (potentialMeasure φ) := by
  have hq : Continuous (fun x => Real.exp (-φ x/2)*a x) := by fun_prop
  let hb := hac.mul_left.exists_bound_of_continuous hq
  let B := Classical.choose hb
  have hB : ∀ x, ‖Real.exp (-φ x/2)*a x‖ ≤ B := Classical.choose_spec hb
  exact (l2MultiplierLinearBetween (potentialMeasure_absolutelyContinuous φ) a
    (potentialMultiplier_memLp hφ ha hB)).mkContinuous B
      (potentialMultiplier_norm_le hφ ha ((norm_nonneg _).trans (hB 0)) hB)

lemma compactPotentialMultiplier_ae {n : ℕ} {φ a : CoordinateSpace n → ℝ}
    (hφ : Continuous φ) (ha : Continuous a) (hac : HasCompactSupport a)
    (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n))) :
    compactPotentialMultiplier hφ ha hac f =ᵐ[potentialMeasure φ] fun x => a x*f x := by
  unfold compactPotentialMultiplier
  dsimp only
  exact l2MultiplierLinearBetween_ae (potentialMeasure_absolutelyContinuous φ) _ _ f

attribute [irreducible] compactPotentialMultiplier

set_option maxHeartbeats 400000 in
/-- Compact smooth localization transports genuine volume H¹ functions
into genuine weighted H¹ functions with the actual derivative product rule. -/
theorem exists_weightedSobolev_mul_from_volume {n : ℕ} {φ a : CoordinateSpace n → ℝ}
    [IsFiniteMeasureOnCompacts (potentialMeasure φ)]
    (hφ : Continuous φ) (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a)
    (u : weightedSobolev (volume : Measure (CoordinateSpace n))) :
    ∃ v : weightedSobolev (potentialMeasure φ),
      (v.1 0 =ᵐ[potentialMeasure φ] fun x => a x*u.1 0 x) ∧
      ∀ i, v.1 i.succ =ᵐ[potentialMeasure φ] fun x =>
        a x*u.1 i.succ x + coordinateDerivative i a x*u.1 0 x := by
  apply exists_weightedSobolev_of_multipliers (μ := volume) (ν := potentialMeasure φ)
    ha (potentialMeasure_absolutelyContinuous φ)
    (compactPotentialMultiplier hφ ha.continuous hac)
    (fun i => compactPotentialMultiplier hφ (smooth_coordinateDerivative ha i).continuous
      (hac.fderiv_apply (𝕜 := ℝ) (Pi.single i 1)))
  · intro f
    exact compactPotentialMultiplier_ae hφ ha.continuous hac f
  · intro i f
    exact compactPotentialMultiplier_ae hφ (smooth_coordinateDerivative ha i).continuous
      (hac.fderiv_apply (𝕜 := ℝ) (Pi.single i 1)) f

end GaussianTilt.Letwin
