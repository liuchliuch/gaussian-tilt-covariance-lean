import GaussianTilt.MomentMapPointwiseRecovery
import GaussianTilt.MomentMapDanskinExtended

/-! # Attained Fenchel duality and the actual gradient

Compact target maximizers are constructed by nested compact level sets of
the recovered duals. At a differentiable source point the unique maximizing
target point is its actual Euclidean gradient.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators InnerProductSpace
namespace GaussianTilt.MomentMapCoercivity
variable {n : ℕ}

def momentPayoff (ψ : E n → ℝ) (x y : E n) : EReal :=
  (⟪x, y⟫_ℝ : ℝ) - (extendedDual ψ y : EReal)

theorem extendedDual_young {ψ : E n → ℝ} (hψ : ∀ x, 0 ≤ ψ x) (x y : E n) :
    ((⟪x, y⟫_ℝ - ψ x : ℝ) : EReal) ≤ (extendedDual ψ y : EReal) := by
  have hx : x ∈ ⋃ k : ℕ, sourceBall (n := n) k := by rw [iUnion_sourceBall]; trivial
  obtain ⟨k, hk⟩ := mem_iUnion.mp hx
  have h := fenchel_young (sourceBall_norm_bound k) (fun x _ => hψ x) y hk
  rw [real_inner_comm] at h
  have hE : ((⟪x, y⟫_ℝ - ψ x : ℝ) : EReal) ≤
      (ENNReal.ofReal (recoveredDual ψ k y) : EReal) := by
    rw [EReal.coe_ennreal_ofReal]
    exact EReal.coe_le_coe_iff.mpr (h.trans (le_max_left _ _))
  exact hE.trans (EReal.coe_ennreal_le_coe_ennreal_iff.mpr
    (le_iSup (fun k => ENNReal.ofReal (recoveredDual ψ k y)) k))

theorem momentPayoff_le {ψ : E n → ℝ} (hψ : ∀ x, 0 ≤ ψ x) (x y : E n) :
    momentPayoff ψ x y ≤ (ψ x : EReal) := by
  have h := extendedDual_young hψ x y
  rw [EReal.coe_sub] at h
  have h' := (EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot (ψ x)))
    (.inl (EReal.coe_ne_top (ψ x)))).mp h
  exact EReal.sub_le_of_le_add (by simpa only [add_comm] using h')

theorem extendedDual_lowerSemicontinuous {ψ : E n → ℝ} (hψ : ∀ x, 0 ≤ ψ x) :
    LowerSemicontinuous (fun y => (extendedDual ψ y : EReal)) := by
  have h : LowerSemicontinuous (extendedDual ψ) := lowerSemicontinuous_iSup
    (fun k => (ENNReal.continuous_ofReal.comp (recoveredDual_continuous hψ k)).lowerSemicontinuous)
  exact continuous_coe_ennreal_ereal.comp_lowerSemicontinuous h EReal.coe_ennreal_strictMono.monotone

theorem momentPayoff_upperSemicontinuous {ψ : E n → ℝ} (hψ : ∀ x, 0 ≤ ψ x) (x : E n) :
    UpperSemicontinuous (momentPayoff ψ x) := by
  have hl := extendedDual_lowerSemicontinuous hψ
  have hn : UpperSemicontinuous (fun y => -(extendedDual ψ y : EReal)) :=
    continuous_neg.comp_lowerSemicontinuous_antitone hl (fun _ _ h => EReal.neg_le_neg_iff.mpr h)
  have hc : Continuous (fun y : E n => (⟪x, y⟫_ℝ : EReal)) :=
    continuous_coe_real_ereal.comp (continuous_const.inner continuous_id)
  simpa only [momentPayoff, sub_eq_add_neg] using hc.upperSemicontinuous.add' hn
    (fun y => EReal.continuousAt_add (.inl (EReal.coe_ne_top _)) (.inl (EReal.coe_ne_bot _)))

theorem exists_attaining_extendedDual {K : Set (E n)} {ψ : E n → ℝ} {R : ℝ}
    (hKc : IsCompact K) (hKn : K.Nonempty) (hK : ∀ y ∈ K, ‖y‖ ≤ R)
    (hψ0 : ψ 0 = 0) (hψ : ∀ x, 0 ≤ ψ x)
    (hrecover : ∀ k x, ψ x ≤ fenchel K (recoveredDual ψ k) x) (x : E n) :
    ∃ y ∈ K, (extendedDual ψ y : EReal) = ((⟪x, y⟫_ℝ - ψ x : ℝ) : EReal) := by
  let T : ℕ → Set (E n) := fun k => K ∩ {y | ψ x ≤ ⟪x, y⟫_ℝ - recoveredDual ψ k y}
  have hTc (k : ℕ) : IsClosed (T k) := hKc.isClosed.inter
    (isClosed_le continuous_const ((continuous_const.inner continuous_id).sub (recoveredDual_continuous hψ k)))
  have hTn (k : ℕ) : (T k).Nonempty := by
    obtain ⟨y, hy, hmax⟩ := hKc.exists_isMaxOn hKn
      (((continuous_const.inner continuous_id).sub (recoveredDual_continuous hψ k)).continuousOn)
    have heq : fenchel K (recoveredDual ψ k) x = ⟪x, y⟫_ℝ - recoveredDual ψ k y := by
      apply le_antisymm
      · apply csSup_le (fenchelValues_nonempty hKn _ _)
        rintro a ⟨z, hz, rfl⟩
        exact hmax hz
      · exact fenchel_young hK (fun y _ => recoveredDual_nonneg hψ0 hψ k y) x hy
    refine ⟨y, hy, ?_⟩
    change ψ x ≤ ⟪x, y⟫_ℝ - recoveredDual ψ k y
    rw [← heq]
    exact hrecover k x
  have hTmono (k : ℕ) : T (k + 1) ⊆ T k := by
    intro y hy
    refine ⟨hy.1, ?_⟩
    have h := recoveredDual_monotone hψ y (Nat.le_succ k)
    have hh : ψ x ≤ ⟪x, y⟫_ℝ - recoveredDual ψ (k + 1) y := hy.2
    change recoveredDual ψ k y ≤ recoveredDual ψ (k + 1) y at h
    change ψ x ≤ ⟪x, y⟫_ℝ - recoveredDual ψ k y
    linarith
  obtain ⟨y, hy⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    T hTmono hTn (hKc.inter_right
      (isClosed_le continuous_const ((continuous_const.inner continuous_id).sub (recoveredDual_continuous hψ 0)))) hTc
  have hyt (k : ℕ) : y ∈ T k := mem_iInter.mp hy k
  refine ⟨y, (hyt 0).1, le_antisymm ?_ (extendedDual_young hψ x y)⟩
  have hB : 0 ≤ ⟪x, y⟫_ℝ - ψ x := by
    have hn := recoveredDual_nonneg hψ0 hψ 0 y
    have h : ψ x ≤ ⟪x, y⟫_ℝ - recoveredDual ψ 0 y := (hyt 0).2
    linarith
  have hb : extendedDual ψ y ≤ ENNReal.ofReal (⟪x, y⟫_ℝ - ψ x) := by
    apply iSup_le
    intro k
    apply ENNReal.ofReal_mono
    have h : ψ x ≤ ⟪x, y⟫_ℝ - recoveredDual ψ k y := (hyt k).2
    linarith
  have h := EReal.coe_ennreal_le_coe_ennreal_iff.mpr hb
  simpa only [EReal.coe_ennreal_ofReal, max_eq_left hB] using h

theorem exists_attaining_momentPayoff {K : Set (E n)} {ψ : E n → ℝ} {R : ℝ}
    (hKc : IsCompact K) (hKn : K.Nonempty) (hK : ∀ y ∈ K, ‖y‖ ≤ R)
    (hψ0 : ψ 0 = 0) (hψ : ∀ x, 0 ≤ ψ x)
    (hrecover : ∀ k x, ψ x ≤ fenchel K (recoveredDual ψ k) x) (x : E n) :
    ∃ y ∈ K, momentPayoff ψ x y = (ψ x : EReal) := by
  obtain ⟨y, hy, hd⟩ := exists_attaining_extendedDual hKc hKn hK hψ0 hψ hrecover x
  refine ⟨y, hy, ?_⟩
  rw [momentPayoff, hd, ← EReal.coe_sub]
  congr 1
  ring

lemma extendedDual_eq_of_momentPayoff_eq {ψ : E n → ℝ} {x y : E n}
    (h : momentPayoff ψ x y = (ψ x : EReal)) :
    (extendedDual ψ y : EReal) = ((⟪x, y⟫_ℝ - ψ x : ℝ) : EReal) := by
  have hfin : extendedDual ψ y ≠ ⊤ := by
    intro ht
    have hh := h
    simp only [momentPayoff, ht, EReal.coe_ennreal_top, EReal.sub_top] at hh
    exact (EReal.coe_ne_bot (ψ x)) hh.symm
  have he : (extendedDual ψ y : EReal) = ((extendedDual ψ y).toReal : EReal) :=
    (EReal.coe_ennreal_toReal hfin).symm
  rw [momentPayoff, he, ← EReal.coe_sub] at h
  have hr := EReal.coe_injective h
  rw [he]
  apply EReal.coe_injective.eq_iff.mpr
  linarith

/-- Equality in actual Fenchel duality identifies the target maximizer with
the actual gradient at every differentiable source point. -/
theorem gradient_eq_of_momentPayoff_eq {ψ : E n → ℝ} (hψ : ∀ x, 0 ≤ ψ x)
    {x y : E n} (hd : DifferentiableAt ℝ ψ x)
    (heq : momentPayoff ψ x y = (ψ x : EReal)) : gradient ψ x = y := by
  have hdual := extendedDual_eq_of_momentPayoff_eq heq
  let f : E n → ℝ := fun z => ψ z - ⟪y, z⟫_ℝ
  have hmin : IsLocalMin f x := by
    apply Filter.Eventually.of_forall
    intro z
    have h := extendedDual_young hψ z y
    rw [hdual] at h
    have hr := EReal.coe_le_coe_iff.mp h
    dsimp [f]
    rw [real_inner_comm y z, real_inner_comm y x] at hr
    linarith
  have hder : HasFDerivAt f (fderiv ℝ ψ x - innerSL ℝ y) x :=
    hd.hasFDerivAt.sub (innerSL ℝ y).hasFDerivAt
  have hzero := hmin.hasFDerivAt_eq_zero hder
  have he : fderiv ℝ ψ x = innerSL ℝ y := sub_eq_zero.mp hzero
  have hgrad : HasGradientAt ψ y x := by
    apply hasGradientAt_iff_hasFDerivAt.mpr
    convert hd.hasFDerivAt using 1
    exact he.symm
  exact hgrad.gradient

/-- The constructed compact dual has a unique maximizer at almost every
source point, precisely the actual Euclidean gradient needed by Danskin. -/
theorem ae_gradient_is_unique_momentPayoff_maximizer
    {K : Set (E n)} {ψ : E n → ℝ} {R : ℝ}
    (hKc : IsCompact K) (hKn : K.Nonempty) (hK : ∀ y ∈ K, ‖y‖ ≤ R)
    (hψ0 : ψ 0 = 0) (hψ : ∀ x, 0 ≤ ψ x) (hψc : ConvexOn ℝ univ ψ)
    (hrecover : ∀ k x, ψ x ≤ fenchel K (recoveredDual ψ k) x) :
    ∀ᵐ x ∂volume, gradient ψ x ∈ K ∧ momentPayoff ψ x (gradient ψ x) = (ψ x : EReal) ∧
      ∀ y ∈ K, momentPayoff ψ x y = (ψ x : EReal) → y = gradient ψ x := by
  filter_upwards [convex_ae_differentiable hψc] with x hd
  obtain ⟨y, hy, heq⟩ := exists_attaining_momentPayoff hKc hKn hK hψ0 hψ hrecover x
  have hg := gradient_eq_of_momentPayoff_eq hψ hd heq
  refine ⟨hg ▸ hy, hg ▸ heq, ?_⟩
  intro z hz hzeq
  exact (gradient_eq_of_momentPayoff_eq hψ hd hzeq).symm

end GaussianTilt.MomentMapCoercivity
