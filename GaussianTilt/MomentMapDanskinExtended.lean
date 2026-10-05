import GaussianTilt.MomentMapDanskin

/-! # Envelope derivatives with genuine infinite boundary potentials

The payoff may take the value minus infinity. Truncating below the unique
finite maximum does not change the envelope near the differentiation point;
the finite compact-envelope theorem therefore applies without replacing
infinite boundary values by an unproved regularity assumption.
-/
noncomputable section
open Filter Set
open scoped Topology

namespace GaussianTilt.MomentMapCoercivity

def lowerTruncatePayoff {α : Type*} (a : α → EReal) (L : ℝ) (y : α) : ℝ :=
  (max (a y) (L : EReal)).toReal

lemma coe_lowerTruncatePayoff {α : Type*} {a : α → EReal} {U L : ℝ}
    (hU : ∀ y, a y ≤ (U : EReal)) (y : α) :
    (lowerTruncatePayoff a L y : EReal) = max (a y) (L : EReal) := by
  apply EReal.coe_toReal
  · exact ne_of_lt ((max_le_max (hU y) le_rfl).trans_lt (by
      exact max_lt (EReal.coe_lt_top U) (EReal.coe_lt_top L)))
  · exact ne_of_gt ((EReal.bot_lt_coe L).trans_le (le_max_right _ _))

lemma upperSemicontinuous_lowerTruncatePayoff {α : Type*} [TopologicalSpace α]
    {a : α → EReal} (ha : UpperSemicontinuous a) {U L : ℝ}
    (hU : ∀ y, a y ≤ (U : EReal)) : UpperSemicontinuous (lowerTruncatePayoff a L) := by
  apply upperSemicontinuous_iff_isOpen_preimage.mpr
  intro r
  have heq (y : α) : lowerTruncatePayoff a L y < r ↔ a y < (r : EReal) ∧ L < r := by
    rw [← EReal.coe_lt_coe_iff, coe_lowerTruncatePayoff hU, max_lt_iff, EReal.coe_lt_coe_iff]
  change IsOpen {y | lowerTruncatePayoff a L y < r}
  simp_rw [heq]
  by_cases hL : L < r
  · simpa only [hL, and_true] using ha.isOpen_preimage (r : EReal)
  · simp only [hL, and_false, setOf_false, isOpen_empty]

def extendedCompactEnvelope {α : Type*} (a : α → EReal) (b : α → ℝ) (t : ℝ) : EReal :=
  sSup (Set.range (fun y ↦ a y - (t * b y : ℝ)))

/-- The extended-real compact-envelope derivative; payoffs equal to minus
infinity are permitted anywhere except at the unique maximizing point. -/
theorem hasDerivAt_extendedCompactEnvelope {α : Type*} [TopologicalSpace α] [CompactSpace α]
    {a : α → EReal} {b : α → ℝ} (ha : UpperSemicontinuous a) (hb : Continuous b)
    {y₀ : α} {A : ℝ} (hy₀ : a y₀ = (A : EReal))
    (hmax : ∀ y, a y ≤ (A : EReal)) (hunique : ∀ y, a y = (A : EReal) → y = y₀) :
    HasDerivAt (fun t : ℝ ↦ (extendedCompactEnvelope a b t).toReal) (-b y₀) 0 := by
  letI : Nonempty α := ⟨y₀⟩
  let a' : α → ℝ := lowerTruncatePayoff a (A - 1)
  have ha' : UpperSemicontinuous a' := upperSemicontinuous_lowerTruncatePayoff ha hmax
  have ha₀ : a' y₀ = A := by
    dsimp [a', lowerTruncatePayoff]
    rw [hy₀]
    have hL : ((A - 1 : ℝ) : EReal) ≤ (A : EReal) := EReal.coe_le_coe_iff.mpr (by linarith)
    change (max (A : EReal) ((A - 1 : ℝ) : EReal)).toReal = A
    rw [max_eq_left hL, EReal.toReal_coe]
  have hmax' (y : α) : a' y ≤ A := by
    apply EReal.coe_le_coe_iff.mp
    rw [coe_lowerTruncatePayoff hmax]
    exact max_le (hmax y) (EReal.coe_le_coe_iff.mpr (by linarith))
  have huniq' (y : α) (hy : a' y = a' y₀) : y = y₀ := by
    apply hunique
    rw [ha₀] at hy
    have he := congrArg (fun r : ℝ ↦ (r : EReal)) hy
    change (lowerTruncatePayoff a (A - 1) y : EReal) = (A : EReal) at he
    rw [coe_lowerTruncatePayoff hmax] at he
    apply le_antisymm (hmax y)
    by_contra hn
    have hlt : max (a y) (A - 1 : ℝ) < (A : EReal) :=
      max_lt (lt_of_not_ge hn) (EReal.coe_lt_coe_iff.mpr (by linarith))
    exact (ne_of_lt hlt) he
  have hd := hasDerivAt_compactEnvelope ha' hb (fun y ↦ by simpa only [ha₀] using hmax' y) huniq'
  apply hd.congr_of_eventuallyEq
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hb.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg (b y₀)).trans (hM y₀ (mem_univ _))
  have hbd (z : α) : |b z - b y₀| ≤ 2 * M := by
    have h := norm_sub_le (b z) (b y₀)
    rw [Real.norm_eq_abs] at h
    linarith [hM z (mem_univ _), hM y₀ (mem_univ _)]
  have hsmall : ∀ᶠ t : ℝ in 𝓝 0, |t| < 1 / (2 * M + 1) :=
    continuous_abs.continuousAt.tendsto.eventually
      (eventually_lt_nhds (by simpa only [abs_zero] using
        (div_pos (by norm_num : (0 : ℝ) < 1) (by linarith : 0 < 2 * M + 1))))
  filter_upwards [hsmall] with t ht
  have hp : UpperSemicontinuous (fun y ↦ a' y - t * b y) := by
    simpa only [sub_eq_add_neg, neg_mul] using
      ha'.add ((continuous_const : Continuous (fun _ : α ↦ -t)).mul hb).upperSemicontinuous
  obtain ⟨z, hz⟩ := upperSemicontinuous_attains_max hp
  have hzvalue := compactEnvelope_eq_at_max hz
  have hza : A - 1 < a' z := by
    have h := hz y₀
    rw [ha₀] at h
    have hneg := neg_abs_le (t * (b z - b y₀))
    rw [abs_mul] at hneg
    have hprod := mul_le_mul_of_nonneg_left (hbd z) (abs_nonneg t)
    have ht' := (lt_div_iff₀ (by linarith : 0 < 2 * M + 1)).mp ht
    nlinarith [abs_nonneg t]
  have hza' : (A - 1 : ℝ) < a z := by
    have h := EReal.coe_lt_coe_iff.mpr hza
    rw [coe_lowerTruncatePayoff hmax] at h
    simpa only [lt_max_iff, lt_self_iff_false, or_false] using h
  have haz : a z = (a' z : EReal) := by
    rw [coe_lowerTruncatePayoff hmax, max_eq_left hza'.le]
  have henv : extendedCompactEnvelope a b t = (compactEnvelope a' b t : EReal) := by
    rw [hzvalue]
    apply le_antisymm
    · apply sSup_le
      rintro r ⟨y, rfl⟩
      have hay : a y ≤ (a' y : EReal) := by
        rw [coe_lowerTruncatePayoff hmax]
        exact le_max_left _ _
      calc
        a y - (t * b y : ℝ) ≤ (a' y : EReal) - (t * b y : ℝ) := EReal.sub_le_sub hay le_rfl
        _ = ((a' y - t * b y : ℝ) : EReal) := (EReal.coe_sub _ _).symm
        _ ≤ _ := EReal.coe_le_coe_iff.mpr (hz y)
    · have h : a z - (t * b z : ℝ) ≤ extendedCompactEnvelope a b t := le_sSup (mem_range_self z)
      simpa only [haz, ← EReal.coe_sub] using h
  rw [henv, EReal.toReal_coe]

/-- The literal set-supremum form, allowing minus-infinite boundary payoffs. -/
theorem hasDerivAt_extendedCompactEnvelopeOn {α : Type*} [TopologicalSpace α]
    {K : Set α} (hK : IsCompact K) {a : α → EReal} {b : α → ℝ}
    (ha : UpperSemicontinuousOn a K) (hb : ContinuousOn b K) {y₀ : α} (hy₀ : y₀ ∈ K)
    {A : ℝ} (hA : a y₀ = (A : EReal)) (hmax : ∀ y ∈ K, a y ≤ (A : EReal))
    (hunique : ∀ y ∈ K, a y = (A : EReal) → y = y₀) :
    HasDerivAt (fun t : ℝ ↦ (sSup ((fun y ↦ a y - (t * b y : ℝ)) '' K)).toReal)
      (-b y₀) 0 := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have h := hasDerivAt_extendedCompactEnvelope (upperSemicontinuous_restrict ha)
    (continuousOn_iff_continuous_restrict.mp hb) (y₀ := ⟨y₀, hy₀⟩) hA
    (fun y ↦ hmax y y.property) (fun y heq ↦ Subtype.ext (hunique y y.property heq))
  convert h using 1
  funext t
  congr 1
  congr 1
  ext r
  simp only [mem_image, mem_range, Set.restrict_apply, Subtype.exists, exists_prop]

end GaussianTilt.MomentMapCoercivity
