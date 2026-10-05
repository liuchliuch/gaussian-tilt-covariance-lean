import GaussianTilt.EllipticRegularityWeak
import GaussianTilt.EllipticRegularitySobolevProduct
import GaussianTilt.EllipticRegularityEnergy

/-! # Testing local weakly harmonic Sobolev representatives -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ContDiff Topology ENNReal InnerProductSpace
namespace GaussianTilt.Letwin

/-- Core local harmonicity extends to compactly multiplied H¹ tests through
the actual continuous product-rule jet map. -/
theorem localized_weightedSobolev_product_pairing {n : ℕ}
    {φ χ h a : CoordinateSpace n → ℝ} [IsFiniteMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ ∞ φ) (ha : ContDiff ℝ ∞ a)
    (u v : weightedSobolev (potentialMeasure φ))
    (hval : u.1 0 =ᵐ[potentialMeasure φ] fun x => χ x * h x)
    (horth : ∀ f : CoordinateSpace n → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      (∫ x, h x * weightedLaplacian φ f x ∂potentialMeasure φ) = 0)
    (hχ : ∀ x ∈ tsupport a, χ x = 1)
    (M : Lp ℝ 2 (potentialMeasure φ) →L[ℝ] Lp ℝ 2 (potentialMeasure φ))
    (D : Fin n → Lp ℝ 2 (potentialMeasure φ) →L[ℝ] Lp ℝ 2 (potentialMeasure φ))
    (hM : ∀ f, M f =ᵐ[potentialMeasure φ] fun x => a x*f x)
    (hD : ∀ i f, D i f =ᵐ[potentialMeasure φ] fun x => coordinateDerivative i a x*f x) :
    (∑ i : Fin n, inner ℝ (u.1 i.succ) (sobolevJetMultiply M D v.1 i.succ)) = 0 := by
  let μ := potentialMeasure φ
  let T := sobolevJetMultiply M D
  have hclosed : IsClosed {z : SobolevJet μ | (∑ i : Fin n, inner ℝ (u.1 i.succ) (T z i.succ)) = 0} := by
    apply isClosed_eq _ continuous_const
    apply continuous_finset_sum
    intro i _
    exact continuous_const.inner
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (n+1) => Lp ℝ 2 μ) i.succ).continuous.comp T.continuous)
  have hcore : (LinearMap.range (smoothCompactJet μ) : Set (SobolevJet μ)) ⊆
      {z | (∑ i : Fin n, inner ℝ (u.1 i.succ) (T z i.succ)) = 0} := by
    rintro _ ⟨f, rfl⟩
    change (∑ i : Fin n, inner ℝ (u.1 i.succ) (sobolevJetMultiply M D (smoothCompactJet μ f) i.succ)) = 0
    rw [sobolevJetMultiply_core ha (Measure.AbsolutelyContinuous.refl μ) M D hM hD]
    apply localized_weightedSobolev_weak_harmonic hφ u hval horth (smoothCompactMultiply ha f)
    intro x hx
    exact hχ x (tsupport_mul_subset_left hx)
  exact closure_minimal hcore hclosed v.2

lemma coordinateDerivative_sq {n : ℕ} {η : CoordinateSpace n → ℝ}
    (hη : ContDiff ℝ ∞ η) (i : Fin n) (x : CoordinateSpace n) :
    coordinateDerivative i (fun y => η y ^ 2) x = 2 * η x * coordinateDerivative i η x := by
  have he : (fun y => η y ^ 2) = fun y => η y * η y := by funext y; ring
  rw [he, coordinateDerivative_mul (hη.differentiable (by simp)) (hη.differentiable (by simp))]
  ring

/-- The exact rough cutoff energy identity. This is the previously missing
η²h test; it is obtained from actual H¹ closure rather than assumed. -/
theorem localized_weightedSobolev_cutoff_energy {n : ℕ}
    {φ χ h η : CoordinateSpace n → ℝ} [IsFiniteMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ ∞ φ) (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (u : weightedSobolev (potentialMeasure φ))
    (hval : u.1 0 =ᵐ[potentialMeasure φ] fun x => χ x * h x)
    (horth : ∀ f : CoordinateSpace n → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      (∫ x, h x * weightedLaplacian φ f x ∂potentialMeasure φ) = 0)
    (hχ : ∀ x ∈ tsupport η, χ x = 1) :
    (∫ x, ∑ i : Fin n, u.1 i.succ x * (η x^2 * u.1 i.succ x +
      (2 * η x * coordinateDerivative i η x) * u.1 0 x) ∂potentialMeasure φ) = 0 := by
  let μ := potentialMeasure φ
  let a := fun x => η x^2
  have ha : ContDiff ℝ ∞ a := hη.pow 2
  have hac : HasCompactSupport a := by simpa only [a, pow_two] using hηc.mul_right (f' := η)
  obtain ⟨B, hB⟩ := hac.exists_bound_of_continuous ha.continuous
  have hdb (i : Fin n) : ∃ C : ℝ, ∀ x, ‖coordinateDerivative i a x‖ ≤ C :=
    (hac.fderiv_apply (𝕜 := ℝ) (Pi.single i 1)).exists_bound_of_continuous
      (smooth_coordinateDerivative ha i).continuous
  choose C hC using hdb
  let M := boundedL2Multiplier (μ := μ) ha.continuous.aestronglyMeasurable
    ((norm_nonneg (a 0)).trans (hB 0)) (Eventually.of_forall hB)
  let D := fun i => boundedL2Multiplier (μ := μ)
    (smooth_coordinateDerivative ha i).continuous.aestronglyMeasurable
    ((norm_nonneg (coordinateDerivative i a 0)).trans (hC i 0)) (Eventually.of_forall (hC i))
  have hM (f : Lp ℝ 2 μ) : M f =ᵐ[μ] fun x => a x*f x := boundedL2Multiplier_ae _ _ _ _
  have hD (i : Fin n) (f : Lp ℝ 2 μ) : D i f =ᵐ[μ] fun x => coordinateDerivative i a x*f x :=
    boundedL2Multiplier_ae _ _ _ _
  have he := localized_weightedSobolev_product_pairing hφ ha u u hval horth
    (fun x hx => hχ x (by
      have hxa : x ∈ tsupport (fun y => η y * η y) := by simpa only [a, pow_two] using hx
      exact tsupport_mul_subset_left (f := η) (g := η) hxa)) M D hM hD
  have hpair (i : Fin n) : inner ℝ (u.1 i.succ) (sobolevJetMultiply M D u.1 i.succ) =
      ∫ x, u.1 i.succ x * (η x^2 * u.1 i.succ x +
        (2 * η x * coordinateDerivative i η x) * u.1 0 x) ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add (M (u.1 i.succ)) (D i (u.1 0)), hM (u.1 i.succ), hD i (u.1 0)]
      with x hx hm hd
    change inner ℝ (u.1 i.succ x) ((M (u.1 i.succ) + D i (u.1 0)) x) = _
    simp only [hx, Pi.add_apply, hm, hd, a, coordinateDerivative_sq hη, RCLike.inner_apply, conj_trivial]
    ring
  have hI (i : Fin n) : Integrable (fun x => u.1 i.succ x *
      (η x^2 * u.1 i.succ x + (2 * η x * coordinateDerivative i η x) * u.1 0 x)) μ := by
    have hi := (Lp.memLp (u.1 i.succ)).integrable_mul
      (Lp.memLp (sobolevJetMultiply M D u.1 i.succ))
    apply hi.congr
    filter_upwards [Lp.coeFn_add (M (u.1 i.succ)) (D i (u.1 0)), hM (u.1 i.succ), hD i (u.1 0)]
      with x hx hm hd
    change u.1 i.succ x * ((M (u.1 i.succ) + D i (u.1 0)) x) = _
    simp only [hx, Pi.add_apply, hm, hd, a, coordinateDerivative_sq hη]
  rw [integral_finset_sum _ (fun i _ => hI i)]
  exact (Finset.sum_congr rfl (fun i _ => (hpair i).symm)).trans he

lemma integrable_continuous_compact_mul {n : ℕ} {μ : Measure (CoordinateSpace n)}
    {a f : CoordinateSpace n → ℝ} (ha : Continuous a) (hac : HasCompactSupport a)
    (hf : Integrable f μ) : Integrable (fun x => a x * f x) μ :=
  hf.bdd_mul ha.aestronglyMeasurable (hac.exists_bound_of_continuous ha)

/-- Square completion gives Caccioppoli for actual rough L² coordinates;
no differentiability of the unknown is present in this statement. -/
theorem rough_caccioppoli_of_energy_zero {n : ℕ} (μ : Measure (CoordinateSpace n))
    (v : Lp ℝ 2 μ) (U : Fin n → Lp ℝ 2 μ)
    {η : CoordinateSpace n → ℝ} (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (he : (∫ x, ∑ i : Fin n, U i x * (η x^2 * U i x +
      (2 * η x * coordinateDerivative i η x) * v x) ∂μ) = 0) :
    (∫ x, η x^2 * (∑ i : Fin n, (U i x)^2) ∂μ) ≤
      4 * ∫ x, (v x)^2 * gradientSquare η x ∂μ := by
  have ha : HasCompactSupport (fun x => η x^2) := by
    simpa only [pow_two] using hηc.mul_right (f' := η)
  have hL : Integrable (fun x => η x^2 * (∑ i : Fin n, (U i x)^2)) μ :=
    integrable_continuous_compact_mul (hη.continuous.pow 2) ha
      (integrable_finset_sum _ fun i _ => (Lp.memLp (U i)).integrable_sq)
  have hR : Integrable (fun x => (v x)^2 * gradientSquare η x) μ := by
    simpa only [mul_comm] using integrable_continuous_compact_mul (continuous_gradientSquare hη)
      (gradientSquare_hasCompactSupport hηc) (Lp.memLp v).integrable_sq
  have hT (i : Fin n) : Integrable (fun x => U i x * (η x^2 * U i x +
      (2 * η x * coordinateDerivative i η x) * v x)) μ := by
    have h1 := integrable_continuous_compact_mul (hη.continuous.pow 2) ha
      (Lp.memLp (U i)).integrable_sq
    have h2 := integrable_continuous_compact_mul
      ((continuous_const.mul hη.continuous).mul (smooth_coordinateDerivative hη i).continuous)
      ((hηc.mul_left (f := fun _ => (2 : ℝ))).mul_right
        (f' := coordinateDerivative i η))
      ((Lp.memLp (U i)).integrable_mul (Lp.memLp v))
    convert h1.add h2 using 1
    funext x
    simp only [Pi.add_apply, Pi.mul_apply]
    ring
  have hS : Integrable (fun x => ∑ i : Fin n, U i x * (η x^2 * U i x +
      (2 * η x * coordinateDerivative i η x) * v x)) μ :=
    integrable_finset_sum _ fun i _ => hT i
  have hp (x : CoordinateSpace n) : η x^2 * (∑ i : Fin n, (U i x)^2) ≤
      2 * (∑ i : Fin n, U i x * (η x^2 * U i x +
        (2 * η x * coordinateDerivative i η x) * v x)) +
        4 * ((v x)^2 * gradientSquare η x) := by
    simp only [gradientSquare, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    nlinarith [sq_nonneg (η x * U i x + 2 * v x * coordinateDerivative i η x)]
  have hi := integral_mono hL ((hS.const_mul 2).add (hR.const_mul 4)) hp
  change (∫ x, η x^2 * (∑ i : Fin n, (U i x)^2) ∂μ) ≤
    ∫ x, 2 * (∑ i : Fin n, U i x * (η x^2 * U i x +
      (2 * η x * coordinateDerivative i η x) * v x)) +
      4 * ((v x)^2 * gradientSquare η x) ∂μ at hi
  rw [integral_add (hS.const_mul 2) (hR.const_mul 4), integral_const_mul,
    integral_const_mul, he, mul_zero, zero_add] at hi
  exact hi

/-- Caccioppoli for the actual local H¹ representative of a rough weighted
L² generator annihilator, with its weak energy identity proved above. -/
theorem localized_weightedSobolev_caccioppoli {n : ℕ}
    {φ χ h η : CoordinateSpace n → ℝ} [IsFiniteMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ ∞ φ) (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (u : weightedSobolev (potentialMeasure φ))
    (hval : u.1 0 =ᵐ[potentialMeasure φ] fun x => χ x * h x)
    (horth : ∀ f : CoordinateSpace n → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      (∫ x, h x * weightedLaplacian φ f x ∂potentialMeasure φ) = 0)
    (hχ : ∀ x ∈ tsupport η, χ x = 1) :
    (∫ x, η x^2 * (∑ i : Fin n, (u.1 i.succ x)^2) ∂potentialMeasure φ) ≤
      4 * ∫ x, (u.1 0 x)^2 * gradientSquare η x ∂potentialMeasure φ :=
  rough_caccioppoli_of_energy_zero (potentialMeasure φ) (u.1 0) (fun i => u.1 i.succ) hη hηc
    (localized_weightedSobolev_cutoff_energy hφ hη hηc u hval horth hχ)

end GaussianTilt.Letwin
