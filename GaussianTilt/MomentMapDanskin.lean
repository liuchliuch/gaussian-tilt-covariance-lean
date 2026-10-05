import Mathlib

/-! # Compact upper-semicontinuous maximizers and envelope differentiation

All maximizers and their stability are obtained from actual compactness.
These lemmas support the variational moment-measure Euler equation.
-/
noncomputable section
open Filter Set
open scoped Topology

namespace GaussianTilt.MomentMapCoercivity

theorem upperSemicontinuous_attains_max {α β : Type*} [TopologicalSpace α]
    [CompactSpace α] [Nonempty α] [LinearOrder β] {f : α → β}
    (hf : UpperSemicontinuous f) : ∃ x, ∀ y, f y ≤ f x := by
  let S : α → Set α := fun y ↦ f ⁻¹' Ici (f y)
  have hd : Directed (· ⊇ ·) S := by
    intro x y
    rcases le_total (f x) (f y) with h | h
    · exact ⟨y, fun z hz ↦ h.trans hz, subset_rfl⟩
    · exact ⟨x, subset_rfl, fun z hz ↦ h.trans hz⟩
  have hclosed (y : α) : IsClosed (S y) := hf.isClosed_preimage _
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed S hd
    (fun y ↦ ⟨y, le_rfl⟩) (fun y ↦ (hclosed y).isCompact) hclosed
  exact ⟨x, fun y ↦ mem_iInter.mp hx y⟩

lemma upperSemicontinuous_restrict {α β : Type*} [TopologicalSpace α] [Preorder β]
    {K : Set α} {f : α → β} (hf : UpperSemicontinuousOn f K) :
    UpperSemicontinuous (K.restrict f) := by
  intro x r hr
  have h := hf x x.property r hr
  rw [← map_nhds_subtype_val x] at h
  exact h

theorem upperSemicontinuousOn_attains_max {α β : Type*} [TopologicalSpace α]
    [LinearOrder β] {K : Set α} (hK : IsCompact K) (hne : K.Nonempty)
    {f : α → β} (hf : UpperSemicontinuousOn f K) :
    ∃ x ∈ K, ∀ y ∈ K, f y ≤ f x := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  letI : Nonempty K := hne.to_subtype
  obtain ⟨x, hx⟩ := upperSemicontinuous_attains_max (upperSemicontinuous_restrict hf)
  exact ⟨x, x.property, fun y hy ↦ hx ⟨y, hy⟩⟩

/-- Near-maximizers have nearly the same continuous observable as the unique
maximizer. This proves the needed compact argmax stability quantitatively. -/
theorem near_maximizer_observable {α : Type*} [TopologicalSpace α] [CompactSpace α]
    {a b : α → ℝ} (ha : UpperSemicontinuous a) (hb : Continuous b) {y₀ : α}
    (hmax : ∀ y, a y ≤ a y₀) (hunique : ∀ y, a y = a y₀ → y = y₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y, a y₀ - δ ≤ a y → |b y - b y₀| < ε := by
  let K : Set α := {y | ε ≤ |b y - b y₀|}
  have hK : IsCompact K := (isClosed_le continuous_const (hb.sub continuous_const).abs).isCompact
  by_cases hne : K.Nonempty
  · obtain ⟨z, hz, hzm⟩ := upperSemicontinuousOn_attains_max hK hne (ha.upperSemicontinuousOn K)
    have hneq : z ≠ y₀ := by
      intro heq
      have hz' : ε ≤ |b z - b y₀| := hz
      rw [heq, sub_self, abs_zero] at hz'
      linarith
    have hlt : a z < a y₀ := lt_of_le_of_ne (hmax z) (fun heq ↦ hneq (hunique z heq))
    refine ⟨(a y₀ - a z) / 2, by linarith, ?_⟩
    intro y hy
    by_contra hyb
    have hyK : y ∈ K := le_of_not_gt hyb
    have h := hzm y hyK
    linarith
  · refine ⟨1, by norm_num, fun y _ ↦ ?_⟩
    exact lt_of_not_ge (fun hy ↦ hne ⟨y, hy⟩)

def compactEnvelope {α : Type*} (a b : α → ℝ) (t : ℝ) : ℝ :=
  sSup (Set.range (fun y ↦ a y - t * b y))

lemma compactEnvelope_eq_at_max {α : Type*} {a b : α → ℝ} {t : ℝ} {y : α}
    (hy : ∀ z, a z - t * b z ≤ a y - t * b y) :
    compactEnvelope a b t = a y - t * b y := by
  apply le_antisymm
  · apply csSup_le ⟨_, mem_range_self y⟩
    rintro r ⟨z, rfl⟩
    exact hy z
  · have hbd : BddAbove (Set.range (fun z ↦ a z - t * b z)) := by
      refine ⟨a y - t * b y, ?_⟩
      rintro r ⟨z, rfl⟩
      exact hy z
    exact le_csSup hbd (mem_range_self y)

/-- Danskin's derivative for a real upper-semicontinuous compact envelope.
The maximizer is unique only at the differentiation parameter. -/
theorem hasDerivAt_compactEnvelope {α : Type*} [TopologicalSpace α] [CompactSpace α]
    {a b : α → ℝ} (ha : UpperSemicontinuous a) (hb : Continuous b) {y₀ : α}
    (hmax : ∀ y, a y ≤ a y₀) (hunique : ∀ y, a y = a y₀ → y = y₀) :
    HasDerivAt (compactEnvelope a b) (-b y₀) 0 := by
  letI : Nonempty α := ⟨y₀⟩
  have hpert (t : ℝ) : UpperSemicontinuous (fun y ↦ a y - t * b y) := by
    simpa only [sub_eq_add_neg, neg_mul] using ha.add ((continuous_const : Continuous (fun _ : α ↦ -t)).mul hb).upperSemicontinuous
  choose y hy using (fun t : ℝ ↦ upperSemicontinuous_attains_max (hpert t))
  have hvalue (t : ℝ) : compactEnvelope a b t = a (y t) - t * b (y t) :=
    compactEnvelope_eq_at_max (hy t)
  have hzero : compactEnvelope a b 0 = a y₀ := by
    have h := compactEnvelope_eq_at_max (a := a) (b := b) (t := 0) (y := y₀)
      (by simpa only [zero_mul, sub_zero] using hmax)
    simpa only [zero_mul, sub_zero] using h
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hb.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg (b y₀)).trans (hM y₀ (mem_univ _))
  have hbd (z : α) : |b z - b y₀| ≤ 2 * M := by
    have h := norm_sub_le (b z) (b y₀)
    rw [Real.norm_eq_abs] at h
    linarith [hM z (mem_univ _), hM y₀ (mem_univ _)]
  have hlimit : Tendsto (fun t : ℝ ↦ b (y t)) (𝓝 0) (𝓝 (b y₀)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨δ, hδ, hnear⟩ := near_maximizer_observable ha hb hmax hunique hε
    have hsmall : ∀ᶠ t : ℝ in 𝓝 0, |t| < δ / (2 * M + 1) :=
      continuous_abs.continuousAt.tendsto.eventually
        (eventually_lt_nhds (by simpa only [abs_zero] using
          (div_pos hδ (by linarith : 0 < 2 * M + 1))))
    filter_upwards [hsmall] with t ht
    rw [Real.dist_eq]
    apply hnear
    have hyt := hy t y₀
    have habs := le_abs_self (t * (b y₀ - b (y t)))
    rw [abs_mul, abs_sub_comm] at habs
    have hproduct := mul_le_mul_of_nonneg_left (hbd (y t)) (abs_nonneg t)
    have htδ := (lt_div_iff₀ (by linarith : 0 < 2 * M + 1)).mp ht
    nlinarith [abs_nonneg t]
  have herr (t : ℝ) :
      ‖t‖⁻¹ * ‖compactEnvelope a b t - compactEnvelope a b 0 - t * (-b y₀)‖ ≤
        |b (y t) - b y₀| := by
    rw [hvalue, hzero]
    have hlow := hy t y₀
    have hup := hmax (y t)
    have hnonneg : 0 ≤ a (y t) - t * b (y t) - a y₀ - t * (-b y₀) := by linarith
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg hnonneg]
    by_cases ht : t = 0
    · simp only [ht, abs_zero, inv_zero, zero_mul]
      exact abs_nonneg _
    · have htpos : 0 < |t| := abs_pos.mpr ht
      have habs := le_abs_self (t * (b y₀ - b (y t)))
      rw [abs_mul, abs_sub_comm] at habs
      have hh : a (y t) - t * b (y t) - a y₀ - t * (-b y₀) ≤
          |t| * |b (y t) - b y₀| := by nlinarith
      have h := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr htpos.le)
      simpa only [← mul_assoc, inv_mul_cancel₀ htpos.ne', one_mul] using h
  rw [hasDerivAt_iff_tendsto]
  simp only [sub_zero, smul_eq_mul]
  apply squeeze_zero (fun t ↦ mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _)) herr
  simpa only [sub_self, abs_zero] using (hlimit.sub_const (b y₀)).abs

/-- Set-based form with the literal supremum requested in the variational
argument, under upper semicontinuity on the compact domain. -/
theorem hasDerivAt_compactEnvelopeOn {α : Type*} [TopologicalSpace α]
    {K : Set α} (hK : IsCompact K) {a b : α → ℝ}
    (ha : UpperSemicontinuousOn a K) (hb : ContinuousOn b K) {y₀ : α} (hy₀ : y₀ ∈ K)
    (hmax : ∀ y ∈ K, a y ≤ a y₀) (hunique : ∀ y ∈ K, a y = a y₀ → y = y₀) :
    HasDerivAt (fun t : ℝ ↦ sSup ((fun y ↦ a y - t * b y) '' K)) (-b y₀) 0 := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have h := hasDerivAt_compactEnvelope (upperSemicontinuous_restrict ha)
    (continuousOn_iff_continuous_restrict.mp hb) (y₀ := ⟨y₀, hy₀⟩)
    (fun y ↦ hmax y y.property) (fun y heq ↦ Subtype.ext (hunique y y.property heq))
  convert h using 1
  funext t
  congr 1
  ext r
  simp only [mem_image, mem_range, Set.restrict_apply, Subtype.exists, exists_prop]

end GaussianTilt.MomentMapCoercivity
