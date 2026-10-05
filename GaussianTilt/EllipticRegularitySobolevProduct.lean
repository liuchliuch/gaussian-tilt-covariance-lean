import GaussianTilt.NegativeSobolevClosure

/-! # Actual bounded multiplication on weighted Sobolev spaces -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ContDiff Topology ENNReal InnerProductSpace
namespace GaussianTilt.Letwin

lemma boundedMultiplier_memLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {a : Ω → ℝ} (ha : AEStronglyMeasurable a μ) {B : ℝ}
    (hB : ∀ᵐ x ∂μ, ‖a x‖ ≤ B) (f : Lp ℝ 2 μ) :
    MemLp (fun x => a x * f x) 2 μ := by
  apply (Lp.memLp f).of_le_mul (c := B) (ha.mul (Lp.aestronglyMeasurable f))
  filter_upwards [hB] with x hx
  simp only [Pi.mul_apply, norm_mul]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

/-- Multiplication by a genuinely bounded measurable function as an actual
linear operator on L². -/
def boundedL2MultiplierLinear {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {a : Ω → ℝ} (ha : AEStronglyMeasurable a μ) {B : ℝ}
    (hB : ∀ᵐ x ∂μ, ‖a x‖ ≤ B) : Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 μ where
  toFun f := (boundedMultiplier_memLp ha hB f).toLp (fun x => a x*f x)
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(boundedMultiplier_memLp ha hB (f+g)).coeFn_toLp,
      (boundedMultiplier_memLp ha hB f).coeFn_toLp, (boundedMultiplier_memLp ha hB g).coeFn_toLp,
      Lp.coeFn_add f g,
      Lp.coeFn_add ((boundedMultiplier_memLp ha hB f).toLp (fun x => a x*f x))
        ((boundedMultiplier_memLp ha hB g).toLp (fun x => a x*g x))] with x hfg hf hg hadd hsum
    simp only [Pi.add_apply] at hadd hsum
    rw [hfg, hsum, hf, hg, hadd]
    ring
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(boundedMultiplier_memLp ha hB (c • f)).coeFn_toLp,
      (boundedMultiplier_memLp ha hB f).coeFn_toLp, Lp.coeFn_smul c f,
      Lp.coeFn_smul c ((boundedMultiplier_memLp ha hB f).toLp (fun x => a x*f x))] with x hcf hf hsm hsm'
    simp only [Pi.smul_apply, smul_eq_mul] at hsm hsm'
    simp only [RingHom.id_apply]
    rw [hcf, hsm', hf, hsm]
    ring

lemma boundedL2MultiplierLinear_ae {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {a : Ω → ℝ} (ha : AEStronglyMeasurable a μ) {B : ℝ}
    (hB : ∀ᵐ x ∂μ, ‖a x‖ ≤ B) (f : Lp ℝ 2 μ) :
    boundedL2MultiplierLinear ha hB f =ᵐ[μ] fun x => a x*f x :=
  (boundedMultiplier_memLp ha hB f).coeFn_toLp

/-- Bounded multiplication is continuous in the actual L² norm. -/
def boundedL2Multiplier {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {a : Ω → ℝ} (ha : AEStronglyMeasurable a μ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ᵐ x ∂μ, ‖a x‖ ≤ B) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (boundedL2MultiplierLinear ha hB).mkContinuous B fun f => by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [boundedL2MultiplierLinear_ae ha hB f, hB] with x hx hb
    rw [hx, norm_mul]
    exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)

lemma boundedL2Multiplier_ae {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {a : Ω → ℝ} (ha : AEStronglyMeasurable a μ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ᵐ x ∂μ, ‖a x‖ ≤ B) (f : Lp ℝ 2 μ) :
    boundedL2Multiplier ha hB0 hB f =ᵐ[μ] fun x => a x*f x :=
  boundedL2MultiplierLinear_ae ha hB f

/-- Multiplication of compact smooth core elements by any smooth function. -/
def smoothCompactMultiply {n : ℕ} {a : CoordinateSpace n → ℝ}
    (ha : ContDiff ℝ ∞ a) (f : smoothCompactCore n) : smoothCompactCore n :=
  ⟨fun x => a x*f.1 x, ha.mul f.2.1, f.2.2.mul_left⟩

/-- The actual product-rule jet map built from three genuine L² operators
(value multiplier and derivative multipliers). -/
def sobolevJetMultiply {n : ℕ} {μ ν : Measure (CoordinateSpace n)}
    (M : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 ν) (D : Fin n → Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 ν) :
    SobolevJet μ →L[ℝ] SobolevJet ν :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n+1) => Lp ℝ 2 ν)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (Fin.cases
      (M.comp (PiLp.proj 2 (fun _ : Fin (n+1) => Lp ℝ 2 μ) 0))
      (fun i => M.comp (PiLp.proj 2 (fun _ : Fin (n+1) => Lp ℝ 2 μ) i.succ) +
        (D i).comp (PiLp.proj 2 (fun _ : Fin (n+1) => Lp ℝ 2 μ) 0))))

@[simp] lemma sobolevJetMultiply_zero {n : ℕ} {μ ν : Measure (CoordinateSpace n)}
    (M : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 ν) (D : Fin n → Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 ν)
    (u : SobolevJet μ) : sobolevJetMultiply M D u 0 = M (u 0) := rfl

@[simp] lemma sobolevJetMultiply_succ {n : ℕ} {μ ν : Measure (CoordinateSpace n)}
    (M : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 ν) (D : Fin n → Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 ν)
    (u : SobolevJet μ) (i : Fin n) :
    sobolevJetMultiply M D u i.succ = M (u i.succ) + D i (u 0) := rfl

/-- On the actual compact smooth core, the jet construction equals ordinary
pointwise multiplication and its proved derivative product rule. -/
theorem sobolevJetMultiply_core {n : ℕ} {μ ν : Measure (CoordinateSpace n)}
    [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    {a : CoordinateSpace n → ℝ} (ha : ContDiff ℝ ∞ a) (hνμ : ν ≪ μ)
    (M : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 ν) (D : Fin n → Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 ν)
    (hM : ∀ f, M f =ᵐ[ν] fun x => a x*f x)
    (hD : ∀ i f, D i f =ᵐ[ν] fun x => coordinateDerivative i a x*f x)
    (f : smoothCompactCore n) :
    sobolevJetMultiply M D (smoothCompactJet μ f) = smoothCompactJet ν (smoothCompactMultiply ha f) := by
  apply PiLp.ext
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [sobolevJetMultiply_zero, smoothCompactJet_zero]
    apply Lp.ext
    filter_upwards [hM (smoothCompactToL2 μ f),
      hνμ.ae_eq (smoothCompactToL2_ae μ f), smoothCompactToL2_ae ν (smoothCompactMultiply ha f)] with x hx hf hg
    exact (hx.trans (congrArg (fun y => a x*y) hf)).trans hg.symm
  · simp only [sobolevJetMultiply_succ, smoothCompactJet_succ, smoothCompactJet_zero]
    apply Lp.ext
    filter_upwards [Lp.coeFn_add (M (smoothCompactToL2 μ (smoothCompactDerivative i f)))
        (D i (smoothCompactToL2 μ f)),
      hM (smoothCompactToL2 μ (smoothCompactDerivative i f)), hD i (smoothCompactToL2 μ f),
      hνμ.ae_eq (smoothCompactToL2_ae μ f), hνμ.ae_eq (smoothCompactToL2_ae μ (smoothCompactDerivative i f)),
      smoothCompactToL2_ae ν (smoothCompactDerivative i (smoothCompactMultiply ha f))] with x hs hm hd hf hdf hout
    simp only [Pi.add_apply] at hs
    rw [hs, hm, hd, hf, hdf, hout]
    change a x * coordinateDerivative i f.1 x + coordinateDerivative i a x * f.1 x =
      coordinateDerivative i (fun y => a y*f.1 y) x
    rw [coordinateDerivative_mul (ha.differentiable (by simp)) (f.2.1.differentiable (by simp))]
    ring

/-- Continuity passes actual core multiplication to its Sobolev closure. -/
theorem sobolevJetMultiply_mem {n : ℕ} {μ ν : Measure (CoordinateSpace n)}
    [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    {a : CoordinateSpace n → ℝ} (ha : ContDiff ℝ ∞ a) (hνμ : ν ≪ μ)
    (M : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 ν) (D : Fin n → Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 ν)
    (hM : ∀ f, M f =ᵐ[ν] fun x => a x*f x)
    (hD : ∀ i f, D i f =ᵐ[ν] fun x => coordinateDerivative i a x*f x)
    (u : weightedSobolev μ) : sobolevJetMultiply M D u.1 ∈ weightedSobolev ν := by
  have hclosed : IsClosed ((sobolevJetMultiply M D) ⁻¹' (weightedSobolev ν : Set (SobolevJet ν))) :=
    (LinearMap.range (smoothCompactJet ν)).isClosed_topologicalClosure.preimage
      (sobolevJetMultiply M D).continuous
  have hcore : (LinearMap.range (smoothCompactJet μ) : Set (SobolevJet μ)) ⊆
      (sobolevJetMultiply M D) ⁻¹' (weightedSobolev ν : Set (SobolevJet ν)) := by
    rintro _ ⟨f, rfl⟩
    change sobolevJetMultiply M D (smoothCompactJet μ f) ∈ weightedSobolev ν
    rw [sobolevJetMultiply_core ha hνμ M D hM hD]
    exact (LinearMap.range (smoothCompactJet ν)).le_topologicalClosure ⟨smoothCompactMultiply ha f, rfl⟩
  exact closure_minimal hcore hclosed u.2

/-- A general output wrapper for the proved product-rule map. -/
theorem exists_weightedSobolev_of_multipliers {n : ℕ} {μ ν : Measure (CoordinateSpace n)}
    [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    {a : CoordinateSpace n → ℝ} (ha : ContDiff ℝ ∞ a) (hνμ : ν ≪ μ)
    (M : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 ν) (D : Fin n → Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 ν)
    (hM : ∀ f, M f =ᵐ[ν] fun x => a x*f x)
    (hD : ∀ i f, D i f =ᵐ[ν] fun x => coordinateDerivative i a x*f x)
    (u : weightedSobolev μ) :
    ∃ v : weightedSobolev ν,
      (v.1 0 =ᵐ[ν] fun x => a x*u.1 0 x) ∧
      ∀ i, v.1 i.succ =ᵐ[ν] fun x => a x*u.1 i.succ x + coordinateDerivative i a x*u.1 0 x := by
  let v : weightedSobolev ν := ⟨sobolevJetMultiply M D u.1,
    sobolevJetMultiply_mem ha hνμ M D hM hD u⟩
  refine ⟨v, hM (u.1 0), ?_⟩
  intro i
  filter_upwards [Lp.coeFn_add (M (u.1 i.succ)) (D i (u.1 0)), hM (u.1 i.succ), hD i (u.1 0)] with x hx hm hd
  change (M (u.1 i.succ) + D i (u.1 0)) x = _
  simpa only [Pi.add_apply, hm, hd] using hx

/-- A bounded smooth function with bounded first derivatives genuinely
multiplies the constructed weighted H¹ space, with the actual product rule. -/
theorem exists_weightedSobolev_mul {n : ℕ} (μ : Measure (CoordinateSpace n))
    [IsFiniteMeasureOnCompacts μ] {a : CoordinateSpace n → ℝ}
    (ha : ContDiff ℝ ∞ a) (B : ℝ) (hB : ∀ x, ‖a x‖ ≤ B)
    (D : Fin n → ℝ) (hD : ∀ i x, ‖coordinateDerivative i a x‖ ≤ D i)
    (u : weightedSobolev μ) :
    ∃ v : weightedSobolev μ,
      (v.1 0 =ᵐ[μ] fun x => a x * u.1 0 x) ∧
      ∀ i, v.1 i.succ =ᵐ[μ] fun x =>
        a x*u.1 i.succ x + coordinateDerivative i a x*u.1 0 x := by
  let M := boundedL2Multiplier ha.continuous.aestronglyMeasurable
    ((norm_nonneg (a 0)).trans (hB 0)) (Filter.Eventually.of_forall hB) (μ := μ)
  let MD := fun i => boundedL2Multiplier (smooth_coordinateDerivative ha i).continuous.aestronglyMeasurable
    ((norm_nonneg (coordinateDerivative i a 0)).trans (hD i 0)) (Filter.Eventually.of_forall (hD i)) (μ := μ)
  have hM (f : Lp ℝ 2 μ) : M f =ᵐ[μ] fun x => a x*f x := boundedL2Multiplier_ae _ _ _ _
  have hMD (i : Fin n) (f : Lp ℝ 2 μ) : MD i f =ᵐ[μ] fun x => coordinateDerivative i a x*f x :=
    boundedL2Multiplier_ae _ _ _ _
  let v : weightedSobolev μ := ⟨sobolevJetMultiply M MD u.1,
    sobolevJetMultiply_mem ha (Measure.AbsolutelyContinuous.refl μ) M MD hM hMD u⟩
  refine ⟨v, hM (u.1 0), ?_⟩
  intro i
  filter_upwards [Lp.coeFn_add (M (u.1 i.succ)) (MD i (u.1 0)), hM (u.1 i.succ), hMD i (u.1 0)] with x hx hm hd
  change (M (u.1 i.succ) + MD i (u.1 0)) x = _
  simpa only [Pi.add_apply, hm, hd] using hx

/-- Compact smooth multiplication has no separate boundedness premises;
the required multiplier bounds are obtained from actual compact supports. -/
theorem exists_weightedSobolev_mul_compact {n : ℕ} (μ : Measure (CoordinateSpace n))
    [IsFiniteMeasureOnCompacts μ] {a : CoordinateSpace n → ℝ}
    (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a) (u : weightedSobolev μ) :
    ∃ v : weightedSobolev μ,
      (v.1 0 =ᵐ[μ] fun x => a x * u.1 0 x) ∧
      ∀ i, v.1 i.succ =ᵐ[μ] fun x =>
        a x*u.1 i.succ x + coordinateDerivative i a x*u.1 0 x := by
  obtain ⟨B, hB⟩ := hac.exists_bound_of_continuous ha.continuous
  have hd (i : Fin n) : ∃ D, ∀ x, ‖coordinateDerivative i a x‖ ≤ D :=
    (hac.fderiv_apply (𝕜 := ℝ) (Pi.single i 1)).exists_bound_of_continuous
      (smooth_coordinateDerivative ha i).continuous
  choose D hD using hd
  exact exists_weightedSobolev_mul μ ha B hB D hD u

end GaussianTilt.Letwin
