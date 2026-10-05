import GaussianTilt.CompactPrekopa

/-!
# Compact measurable logconcave densities and one-coordinate marginals

These lemmas extract the open positive-support interval and its continuity
from the multiplicative logconcavity inequality. In particular, the hard-
cutoff Prékopa theorem can be applied without assuming density continuity.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace GaussianTilt.LogConcaveMarginal

/-- Multiplicative logconcavity without a hidden regularity assumption. -/
def IsLogConcave {E : Type*} [AddCommMonoid E] [Module ℝ E] (f : E → ℝ) : Prop :=
  (∀ x, 0 ≤ f x) ∧ ∀ x y : E, ∀ α β : ℝ, 0 ≤ α → 0 ≤ β → α + β = 1 →
    f x ^ α * f y ^ β ≤ f (α • x + β • y)

lemma convex_support {E : Type*} [AddCommMonoid E] [Module ℝ E] {f : E → ℝ}
    (hf : IsLogConcave f) : Convex ℝ (Function.support f) := by
  intro x hx y hy α β hα hβ hαβ
  have hxpos : 0 < f x := lt_of_le_of_ne (hf.1 x) (Ne.symm hx)
  have hypos : 0 < f y := lt_of_le_of_ne (hf.1 y) (Ne.symm hy)
  exact (lt_of_lt_of_le (mul_pos (Real.rpow_pos_of_pos hxpos _) (Real.rpow_pos_of_pos hypos _))
    (hf.2 x y α β hα hβ hαβ)).ne'

lemma convexOn_neg_log {E : Type*} [AddCommMonoid E] [Module ℝ E] {f : E → ℝ}
    (hf : IsLogConcave f) {S : Set E} (hS : Convex ℝ S) (hp : ∀ x ∈ S, 0 < f x) :
    ConvexOn ℝ S (fun x ↦ -Real.log (f x)) := by
  refine ⟨hS, ?_⟩
  intro x hx y hy α β hα hβ hαβ
  have h := Real.log_le_log (mul_pos (Real.rpow_pos_of_pos (hp x hx) α)
    (Real.rpow_pos_of_pos (hp y hy) β)) (hf.2 x y α β hα hβ hαβ)
  rw [Real.log_mul (Real.rpow_pos_of_pos (hp x hx) α).ne' (Real.rpow_pos_of_pos (hp y hy) β).ne',
    Real.log_rpow (hp x hx), Real.log_rpow (hp y hy)] at h
  simp only [smul_eq_mul]
  linarith

lemma continuousOn_positive_convex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → ℝ} (hf : IsLogConcave f) {S : Set E}
    (hS : Convex ℝ S) (hSo : IsOpen S) (hp : ∀ x ∈ S, 0 < f x) : ContinuousOn f S := by
  have h := Real.continuous_exp.comp_continuousOn (ConvexOn.continuousOn hSo (convexOn_neg_log hf hS hp)).neg
  apply h.congr
  intro x hx
  simp only [Function.comp_apply, neg_neg, Real.exp_log (hp x hx)]

/-- A positive-mass compactly supported logconcave function has one open
positive-support interval, and is continuous throughout its interior. -/
theorem interval_support_of_integral_pos {f : ℝ → ℝ} (hf : IsLogConcave f)
    (hi : Integrable f) (hm : 0 < ∫ x, f x)
    (hs : ∃ A B : ℝ, ∀ x ∉ Icc A B, f x = 0) :
    ∃ a b : ℝ, a < b ∧ (∀ x ∈ Ioo a b, 0 < f x) ∧
      (∀ x ∉ Icc a b, f x = 0) ∧ ContinuousOn f (Ioo a b) := by
  let S := Function.support f
  have hvol : 0 < volume S := (integral_pos_iff_support_of_nonneg hf.1 hi).mp hm
  have hne : S.Nonempty := by
    by_contra h
    have he : S = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    simpa only [he, measure_empty, lt_self_iff_false] using hvol
  obtain ⟨A, B, hAB⟩ := hs
  have hSB : S ⊆ Icc A B := by
    intro x hx
    by_contra hn
    exact hx (hAB x hn)
  have hbelow : BddBelow S := ⟨A, fun x hx ↦ (hSB hx).1⟩
  have habove : BddAbove S := ⟨B, fun x hx ↦ (hSB hx).2⟩
  let a := sInf S
  let b := sSup S
  have hSsub : S ⊆ Icc a b := fun x hx ↦ ⟨csInf_le hbelow hx, le_csSup habove hx⟩
  have hab : a < b := by
    by_contra h
    have hba : b ≤ a := not_lt.mp h
    have hsub : S ⊆ {a} := by
      intro x hx
      exact le_antisymm ((hSsub hx).2.trans hba) (hSsub hx).1
    have hz : volume S = 0 := measure_mono_null hsub (measure_singleton a)
    rw [hz] at hvol
    exact (lt_irrefl _) hvol
  have hpos : ∀ x ∈ Ioo a b, 0 < f x := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := exists_lt_of_csInf_lt hne hx.1
    obtain ⟨z, hz, hxz⟩ := exists_lt_of_lt_csSup hne hx.2
    have hmem := (convex_support hf).ordConnected.out hy hz ⟨hyx.le, hxz.le⟩
    exact lt_of_le_of_ne (hf.1 x) (Ne.symm hmem)
  refine ⟨a, b, hab, hpos, ?_, continuousOn_positive_convex hf (convex_Ioo _ _) isOpen_Ioo hpos⟩
  intro x hx
  by_contra hne
  exact hx (hSsub hne)


lemma positive_interpolated_interval {f g h : ℝ → ℝ} {a b c d α β : ℝ}
    (hab : a < b) (hcd : c < d) (hα : 0 < α) (hβ : 0 < β)
    (hfp : ∀ x ∈ Ioo a b, 0 < f x) (hgp : ∀ y ∈ Ioo c d, 0 < g y)
    (hmajor : ∀ x y, f x ^ α * g y ^ β ≤ h (α * x + β * y)) :
    ∀ z ∈ Ioo (α * a + β * c) (α * b + β * d), 0 < h z := by
  intro z hz
  let L := α * a + β * c
  let R := α * b + β * d
  have hLR : L < R := add_lt_add (mul_lt_mul_of_pos_left hab hα) (mul_lt_mul_of_pos_left hcd hβ)
  let r := (z - L) / (R - L)
  have hr : r ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact div_pos (sub_pos.mpr hz.1) (sub_pos.mpr hLR)
    · exact (div_lt_one (sub_pos.mpr hLR)).mpr (by linarith [hz.2])
  let x := a + r * (b - a)
  let y := c + r * (d - c)
  have hx : x ∈ Ioo a b := by
    dsimp [x]
    have h₁ := mul_pos hr.1 (sub_pos.mpr hab)
    have h₂ := mul_lt_mul_of_pos_right hr.2 (sub_pos.mpr hab)
    constructor <;> linarith
  have hy : y ∈ Ioo c d := by
    dsimp [y]
    have h₁ := mul_pos hr.1 (sub_pos.mpr hcd)
    have h₂ := mul_lt_mul_of_pos_right hr.2 (sub_pos.mpr hcd)
    constructor <;> linarith
  have he : α * x + β * y = z := by
    have hrD : r * (R - L) = z - L := div_mul_cancel₀ _ (sub_pos.mpr hLR).ne'
    dsimp [x, y, L, R] at *
    nlinarith
  rw [← he]
  exact lt_of_lt_of_le (mul_pos (Real.rpow_pos_of_pos (hfp x hx) _) (Real.rpow_pos_of_pos (hgp y hy) _))
    (hmajor x y)

/-- Prékopa–Leindler for compactly supported measurable logconcave input
slices. No density continuity, positive full support, or endpoint assumptions
remain; regularity and support intervals are extracted from logconcavity. -/
theorem integral_rpow_mul_le_of_logconcave {f g h : ℝ → ℝ}
    (hf : IsLogConcave f) (hg : IsLogConcave g) (hh : IsLogConcave h)
    (hfi : Integrable f) (hgi : Integrable g) (hhi : Integrable h)
    (hfs : ∃ A B : ℝ, ∀ x ∉ Icc A B, f x = 0)
    (hgs : ∃ A B : ℝ, ∀ y ∉ Icc A B, g y = 0)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + β = 1)
    (hmajor : ∀ x y, f x ^ α * g y ^ β ≤ h (α * x + β * y)) :
    (∫ x, f x) ^ α * (∫ y, g y) ^ β ≤ ∫ z, h z := by
  by_cases hα0 : α = 0
  · have hβ1 : β = 1 := by linarith
    simp only [hα0, hβ1, Real.rpow_zero, Real.rpow_one, zero_mul, one_mul, zero_add] at *
    exact integral_mono hgi hhi (fun y ↦ hmajor 0 y)
  by_cases hβ0 : β = 0
  · have hα1 : α = 1 := by linarith
    simp only [hβ0, hα1, Real.rpow_zero, Real.rpow_one, zero_mul, one_mul, mul_one, add_zero] at *
    exact integral_mono hfi hhi (fun x ↦ hmajor x 0)
  by_cases hfm : (∫ x, f x) = 0
  · rw [hfm, Real.zero_rpow hα0, zero_mul]
    exact integral_nonneg hh.1
  by_cases hgm : (∫ y, g y) = 0
  · rw [hgm, Real.zero_rpow hβ0, mul_zero]
    exact integral_nonneg hh.1
  have hαp : 0 < α := lt_of_le_of_ne hα (Ne.symm hα0)
  have hβp : 0 < β := lt_of_le_of_ne hβ (Ne.symm hβ0)
  obtain ⟨a, b, hab, hfp, hfs', hfc⟩ := interval_support_of_integral_pos hf hfi
    (lt_of_le_of_ne (integral_nonneg hf.1) (Ne.symm hfm)) hfs
  obtain ⟨c, d, hcd, hgp, hgs', hgc⟩ := interval_support_of_integral_pos hg hgi
    (lt_of_le_of_ne (integral_nonneg hg.1) (Ne.symm hgm)) hgs
  have hhp := positive_interpolated_interval hab hcd hαp hβp hfp hgp hmajor
  exact Prekopa.integral_rpow_mul_le_of_interval_support hab hcd hαp hβp hαβ hfc hgc
    (continuousOn_positive_convex hh (convex_Ioo _ _) isOpen_Ioo hhp) hfp hgp hfi hgi hhi hh.1
    hfs' hgs' (fun x _ y _ ↦ hmajor x y)

lemma logconcave_slice {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {f : E × ℝ → ℝ} (hf : IsLogConcave f) (x : E) : IsLogConcave (fun u ↦ f (x, u)) := by
  refine ⟨fun u ↦ hf.1 (x, u), ?_⟩
  intro u v α β hα hβ hαβ
  have hx : α • x + β • x = x := by rw [← add_smul, hαβ, one_smul]
  simpa only [Prod.smul_mk, Prod.mk_add_mk, hx] using hf.2 (x, u) (x, v) α β hα hβ hαβ

/-- One-coordinate Prékopa marginalization for measurable logconcave
compact-support densities. Integrability and boundedness are only required
of the actual slices; differentiability and global continuity are absent. -/
theorem marginal_logconcave_of_compact_slices {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {f : E × ℝ → ℝ} (hf : IsLogConcave f)
    (hi : ∀ x, Integrable (fun u : ℝ ↦ f (x, u)))
    (hs : ∀ x, ∃ A B : ℝ, ∀ u ∉ Icc A B, f (x, u) = 0) :
    IsLogConcave (fun x ↦ ∫ u : ℝ, f (x, u)) := by
  refine ⟨fun x ↦ integral_nonneg (fun u ↦ hf.1 (x, u)), ?_⟩
  intro x y α β hα hβ hαβ
  apply integral_rpow_mul_le_of_logconcave (logconcave_slice hf x) (logconcave_slice hf y)
    (logconcave_slice hf (α • x + β • y)) (hi x) (hi y) (hi _) (hs x) (hs y) hα hβ hαβ
  intro u v
  simpa only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] using hf.2 (x, u) (y, v) α β hα hβ hαβ


/-- A finite convex function has a supporting affine function at every
interior point of its convex domain, without differentiability. -/
lemma affine_lower_on {V : ℝ → ℝ} {S : Set ℝ} (hc : ConvexOn ℝ S V) {m : ℝ}
    (hm : m ∈ interior S) : ∃ c : ℝ, ∀ x ∈ S, V m + c * (x - m) ≤ V x := by
  let c := derivWithin V (Iio m) m
  refine ⟨c, ?_⟩
  intro x hx
  rcases lt_trichotomy x m with hxm | rfl | hmx
  · have h := hc.slope_le_leftDeriv_of_mem_interior hx hm hxm
    rw [slope_def_field] at h
    have h' := (div_le_iff₀ (sub_pos.mpr hxm)).mp h
    dsimp [c]
    nlinarith
  · simp
  · have h := (hc.leftDeriv_le_rightDeriv_of_mem_interior hm).trans
      (hc.rightDeriv_le_slope_of_mem_interior hm hx hmx)
    rw [slope_def_field] at h
    have h' := (le_div_iff₀ (sub_pos.mpr hmx)).mp h
    dsimp [c]
    nlinarith

/-- Compactly supported finite-valued logconcave functions are bounded.
The supporting-affine argument includes hard boundaries of the support. -/
theorem bounded_of_compact_support {f : ℝ → ℝ} (hf : IsLogConcave f)
    (hs : ∃ A B : ℝ, ∀ x ∉ Icc A B, f x = 0) : ∃ C : ℝ, ∀ x, f x ≤ C := by
  classical
  let S := Function.support f
  obtain ⟨A, B, hAB⟩ := hs
  have hSB : S ⊆ Icc A B := by
    intro x hx
    by_contra hn
    exact hx (hAB x hn)
  have hpos : ∀ x ∈ S, 0 < f x := fun x hx ↦ lt_of_le_of_ne (hf.1 x) (Ne.symm hx)
  by_cases hne : S.Nonempty
  · obtain ⟨x₀, hx₀⟩ := hne
    by_cases hsingle : ∀ x ∈ S, ∀ y ∈ S, x = y
    · refine ⟨f x₀, ?_⟩
      intro x
      by_cases hx : x ∈ S
      · rw [hsingle x hx x₀ hx₀]
      · have hz : f x = 0 := by simpa only [S, Function.mem_support, not_not] using hx
        rw [hz]
        exact hf.1 x₀
    push_neg at hsingle
    obtain ⟨y, hy, z, hz, hyz⟩ := hsingle
    have hmain : ∀ y ∈ S, ∀ z ∈ S, y < z → ∃ C : ℝ, ∀ x, f x ≤ C := by
      intro y hy z hz hyz
      let m := (y + z) / 2
      have hsub : Ioo y z ⊆ S := fun x hx ↦ (convex_support hf).ordConnected.out hy hz ⟨hx.1.le, hx.2.le⟩
      have hm : m ∈ interior S := by
        apply interior_mono hsub
        rw [isOpen_Ioo.interior_eq]
        dsimp [m]
        constructor <;> linarith
      obtain ⟨c, hc⟩ := affine_lower_on (convexOn_neg_log hf (convex_support hf) hpos) hm
      let L := min (-Real.log (f m) + c * (A - m)) (-Real.log (f m) + c * (B - m))
      have hL : ∀ x ∈ S, L ≤ -Real.log (f x) := by
        intro x hx
        have hv := hc x hx
        rcases le_total 0 c with hc0 | hc0
        · have hh := mul_le_mul_of_nonneg_left (sub_le_sub_right (hSB hx).1 m) hc0
          exact (min_le_left _ _).trans (by linarith)
        · have hh := mul_le_mul_of_nonpos_left (sub_le_sub_right (hSB hx).2 m) hc0
          exact (min_le_right _ _).trans (by linarith)
      refine ⟨Real.exp (-L), ?_⟩
      intro x
      by_cases hx : x ∈ S
      · rw [← Real.exp_log (hpos x hx)]
        exact Real.exp_le_exp.mpr (by linarith [hL x hx])
      · have hz : f x = 0 := by simpa only [S, Function.mem_support, not_not] using hx
        rw [hz]
        exact (Real.exp_pos _).le
    rcases lt_or_gt_of_ne hyz with hyz | hzy
    · exact hmain y hy z hz hyz
    · exact hmain z hz y hy hzy
  · refine ⟨0, ?_⟩
    intro x
    have hx : x ∉ S := fun hx ↦ hne ⟨x, hx⟩
    have hz : f x = 0 := by simpa only [S, Function.mem_support, not_not] using hx
    exact hz.le

/-- Actual integrability of a compactly supported measurable logconcave
slice follows from its pointwise shape and measurability. -/
theorem integrable_of_compact_support {f : ℝ → ℝ} (hf : IsLogConcave f) (hm : Measurable f)
    (hs : ∃ A B : ℝ, ∀ x ∉ Icc A B, f x = 0) : Integrable f := by
  obtain ⟨C, hC⟩ := bounded_of_compact_support hf hs
  obtain ⟨A, B, hAB⟩ := hs
  have hconst : IntegrableOn (fun _ : ℝ ↦ C) (Icc A B) := integrableOn_const isCompact_Icc.measure_ne_top
  have hi : IntegrableOn f (Icc A B) := hconst.mono' hm.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x ↦ by simpa only [Real.norm_eq_abs, abs_of_nonneg (hf.1 x)] using hC x))
  exact hi.integrable_of_forall_notMem_eq_zero hAB

/-- Full compact-slice marginal preservation: the slice-integrability
requirement is discharged from measurable logconcavity and bounded support. -/
theorem marginal_logconcave_of_measurable_compact_slices {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {f : E × ℝ → ℝ} (hf : IsLogConcave f)
    (hm : ∀ x, Measurable (fun u : ℝ ↦ f (x, u)))
    (hs : ∀ x, ∃ A B : ℝ, ∀ u ∉ Icc A B, f (x, u) = 0) :
    IsLogConcave (fun x ↦ ∫ u : ℝ, f (x, u)) :=
  marginal_logconcave_of_compact_slices hf
    (fun x ↦ integrable_of_compact_support (logconcave_slice hf x) (hm x) (hs x)) hs

end GaussianTilt.LogConcaveMarginal
