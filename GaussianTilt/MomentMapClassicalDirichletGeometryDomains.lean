import GaussianTilt.MomentMapClassicalDirichletGeometry

/-! # Actual inner smooth domains approximating a convex body -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal Gradient ContDiff
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

lemma closure_strict_sublevel_of_convex {f : E n → ℝ} (hf : Continuous f)
    (hc : ConvexOn ℝ univ f) {t : ℝ} (hne : ∃ a, f a < t) :
    closure {x | f x < t} = {x | f x ≤ t} := by
  apply Subset.antisymm
  · exact closure_minimal (fun x h => show f x ≤ t from le_of_lt h) (isClosed_le hf continuous_const)
  · obtain ⟨a, ha⟩ := hne
    intro x hx
    have hseg : openSegment ℝ a x ⊆ {y | f y < t} := by
      rintro y ⟨b, c, hb, hcc, hbc, rfl⟩
      have h := hc.2 (mem_univ a) (mem_univ x) hb.le hcc.le hbc
      have hlt := mul_lt_mul_of_pos_left ha hb
      have hle := mul_le_mul_of_nonneg_left hx hcc.le
      simp only [smul_eq_mul] at h
      change f (b • a + c • x) < t
      have ht : b*t+c*t = t := by rw [← add_mul, hbc, one_mul]
      linarith
    exact closure_mono hseg (segment_subset_closure_openSegment (right_mem_segment ℝ a x))

lemma gradient_ne_zero_on_convex_level {f : E n → ℝ}
    (hf : Differentiable ℝ f) (hc : ConvexOn ℝ univ f) {t : ℝ}
    (hne : ∃ a, f a < t) {x : E n} (hx : f x = t) : gradient f x ≠ 0 := by
  obtain ⟨a, ha⟩ := hne
  intro hz
  have hh := convex_gradient_support hc (hf x) a
  rw [hz, inner_zero_left, add_zero, hx] at hh
  exact (not_lt_of_ge hh) ha

lemma interior_weak_sublevel_of_regular {f : E n → ℝ}
    (hf : Continuous f) {t : ℝ} (hreg : ∀ x, f x = t → gradient f x ≠ 0) :
    interior {x | f x ≤ t} = {x | f x < t} := by
  apply Subset.antisymm
  · intro x hx
    have hle := interior_subset hx
    change f x ≤ t at hle
    by_contra hlt
    have he : f x = t := le_antisymm hle (not_lt.mp hlt)
    have hm : IsLocalMax f x := by
      filter_upwards [mem_interior_iff_mem_nhds.mp hx] with y hy
      change f y ≤ f x
      rwa [he]
    apply hreg x he
    simp [gradient, hm.fderiv_eq_zero]
  · exact interior_maximal (fun x h => show f x ≤ t from le_of_lt h) (isOpen_lt hf continuous_const)

/-- The output is literal smooth defining data for a relatively compact
inner domain, including quantitative strong convexity and regular boundary. -/
structure SmoothInnerDomain (S A : Set (E n)) where
  defining : E n → ℝ
  modulus : ℝ
  modulus_pos : 0 < modulus
  smooth : ContDiff ℝ ∞ defining
  strongly_convex : StrongConvexOn univ modulus defining
  negative_nonempty : ∃ a, defining a < 0
  contains : A ⊆ {x | defining x < 0}
  compact_sublevel : IsCompact {x | defining x ≤ 0}
  sublevel_inside : {x | defining x ≤ 0} ⊆ interior S
  regular_level : ∀ x, defining x = 0 → gradient defining x ≠ 0

namespace SmoothInnerDomain
variable {S A : Set (E n)} (d : SmoothInnerDomain S A)

def domain : Set (E n) := {x | d.defining x < 0}
def body : Set (E n) := {x | d.defining x ≤ 0}

lemma convex_defining : ConvexOn ℝ univ d.defining :=
  (d.strongly_convex.strictConvexOn d.modulus_pos).convexOn

lemma isOpen_domain : IsOpen d.domain := isOpen_lt d.smooth.continuous continuous_const
lemma convex_domain : Convex ℝ d.domain := by
  simpa only [domain, mem_univ, true_and] using d.convex_defining.convex_lt 0
lemma convex_body : Convex ℝ d.body := by
  simpa only [body, mem_univ, true_and] using d.convex_defining.convex_le 0
lemma closure_domain : closure d.domain = d.body :=
  closure_strict_sublevel_of_convex d.smooth.continuous d.convex_defining d.negative_nonempty
lemma interior_body : interior d.body = d.domain :=
  interior_weak_sublevel_of_regular d.smooth.continuous d.regular_level
lemma frontier_domain : frontier d.domain = {x | d.defining x = 0} := by
  rw [frontier, d.closure_domain, d.isOpen_domain.interior_eq]
  ext x
  simp only [body, domain, mem_diff, mem_setOf_eq, not_lt]
  exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩
lemma bounded_domain : Bornology.IsBounded d.domain :=
  d.compact_sublevel.isBounded.subset (fun x h => show d.defining x ≤ 0 from le_of_lt h)
lemma compact_closure : IsCompact (closure d.domain) := by
  rw [d.closure_domain]
  exact d.compact_sublevel

end SmoothInnerDomain

/-- Every compact interior subset of a convex body containing the origin has
an actual smooth strongly convex relatively compact neighborhood. -/
theorem exists_smoothInnerDomain_centered {S A : Set (E n)}
    (hS : IsCompact S) (hc : Convex ℝ S) (h0 : S ∈ 𝓝 0)
    (hA : IsCompact A) (hAS : A ⊆ interior S) : Nonempty (SmoothInnerDomain S A) := by
  let B := insert (0 : E n) A
  have hB : IsCompact B := hA.insert 0
  have hBne : B.Nonempty := ⟨0, mem_insert _ _⟩
  have hBS : B ⊆ interior S := by
    intro x hx
    rcases hx with rfl | hx
    · exact mem_interior_iff_mem_nhds.mpr h0
    · exact hAS hx
  obtain ⟨L, hL⟩ := hc.lipschitz_gauge h0
  obtain ⟨a, ha, hmax⟩ := hB.exists_isMaxOn hBne (continuous_gauge hc h0).continuousOn
  have ham : gauge S a < 1 := (gauge_lt_one_iff_mem_interior hc h0).mpr (hBS ha)
  obtain ⟨R, hR⟩ := hB.exists_bound_of_continuousOn continuous_id.continuousOn
  have hR0 : 0 ≤ R := by simpa using hR 0 (mem_insert _ _)
  obtain ⟨ε, hε, hsmall⟩ := exists_pos_mul_lt (sub_pos.mpr ham) (2 * (L : ℝ) + 1 + R^2)
  let t := 1 - ((L : ℝ) + 1) * ε
  let f := smoothGaugeDefining S ε hε
  have hfc : ContDiff ℝ ∞ f := contDiff_smoothGaugeDefining hc h0 hε
  have hstrong : StrongConvexOn univ (2*ε) f := stronglyConvex_smoothGaugeDefining hc h0 hε
  have hneg (x : E n) (hx : x ∈ B) : f x < t := by
    have he := (abs_le.mp (smoothGaugeDefining_error hL hε x)).2
    have hnorm : ‖x‖^2 ≤ R^2 := sq_le_sq₀ (norm_nonneg _) hR0 |>.mpr (hR x hx)
    have hg := hmax hx
    change gauge S x ≤ gauge S a at hg
    have he' := mul_le_mul_of_nonneg_left hnorm hε.le
    dsimp [f, t] at *
    nlinarith
  have hsub : {x | f x ≤ t} ⊆ interior S := by
    intro x hx
    apply (gauge_lt_one_iff_mem_interior hc h0).mp
    have hl := smoothGaugeDefining_lower hL hε x
    change f x ≤ t at hx
    dsimp [f, t] at *
    linarith
  have hcompact : IsCompact {x | f x ≤ t} :=
    hS.of_isClosed_subset (isClosed_le hfc.continuous continuous_const) (hsub.trans interior_subset)
  let ρ := fun x => f x - t
  have hρ : ContDiff ℝ ∞ ρ := hfc.sub contDiff_const
  have hρstrong : StrongConvexOn univ (2*ε) ρ := by
    rw [strongConvexOn_iff_convex] at hstrong ⊢
    convert hstrong.add_const (-t) using 1
    ext x
    dsimp [ρ]
    ring
  have hρc := (hρstrong.strictConvexOn (mul_pos (by norm_num) hε)).convexOn
  have hρneg : ∃ x, ρ x < 0 := ⟨0, sub_neg.mpr (hneg 0 (mem_insert _ _))⟩
  refine ⟨{ defining := ρ, modulus := 2*ε, modulus_pos := by positivity
            smooth := hρ, strongly_convex := hρstrong, negative_nonempty := hρneg
            contains := ?_, compact_sublevel := ?_, sublevel_inside := ?_, regular_level := ?_ }⟩
  · intro x hx
    exact sub_neg.mpr (hneg x (mem_insert_of_mem _ hx))
  · simpa only [ρ, sub_nonpos] using hcompact
  · simpa only [ρ, sub_nonpos] using hsub
  · exact fun x hx => gradient_ne_zero_on_convex_level
      (hρ.differentiable (by norm_num)) hρc hρneg hx

/-- Translation removes the normalization that the convex body contain zero. -/
theorem exists_smoothInnerDomain {S A : Set (E n)}
    (hS : IsCompact S) (hc : Convex ℝ S) (hSi : (interior S).Nonempty)
    (hA : IsCompact A) (hAS : A ⊆ interior S) : Nonempty (SmoothInnerDomain S A) := by
  obtain ⟨a, ha⟩ := hSi
  let e := Homeomorph.addRight a
  let S' := e ⁻¹' S
  let A' := e ⁻¹' A
  have hS' : IsCompact S' := e.isCompact_preimage.mpr hS
  have hA' : IsCompact A' := e.isCompact_preimage.mpr hA
  have hci : interior S' = e ⁻¹' interior S := (e.preimage_interior S).symm
  have hc' : Convex ℝ S' := by
    intro x hx y hy b c hb hcc hbc
    have hh := hc hx hy hb hcc hbc
    change b • (x+a) + c • (y+a) ∈ S at hh
    change (b • x+c • y)+a ∈ S
    have hec : c = 1-b := by linarith
    rw [hec] at hh ⊢
    convert hh using 1 <;> module
  have h0' : S' ∈ 𝓝 0 := by
    apply mem_interior_iff_mem_nhds.mp
    rw [hci]
    simpa [e] using ha
  have hAS' : A' ⊆ interior S' := by
    rw [hci]
    exact preimage_mono hAS
  obtain ⟨d⟩ := exists_smoothInnerDomain_centered hS' hc' h0' hA' hAS'
  let f := fun x => d.defining (x-a)
  have hf : ContDiff ℝ ∞ f := d.smooth.comp (contDiff_id.sub contDiff_const)
  have hstrong : StrongConvexOn univ d.modulus f := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ b c hb hcc hbc
    have hh := d.strongly_convex.2 (mem_univ (x-a)) (mem_univ (y-a)) hb hcc hbc
    have he : b • (x-a)+c • (y-a) = (b • x+c • y)-a := by
      have hec : c = 1-b := by linarith
      rw [hec]
      module
    simpa only [f, he, sub_sub_sub_cancel_right] using hh
  have hne : ∃ x, f x < 0 := by
    obtain ⟨x, hx⟩ := d.negative_nonempty
    exact ⟨x+a, by simpa [f] using hx⟩
  have hbody : {x | f x ≤ 0} = e '' {x | d.defining x ≤ 0} := by
    ext x
    constructor
    · intro hx
      exact ⟨x-a, hx, by simp [e]⟩
    · rintro ⟨y, hy, rfl⟩
      simpa [f, e] using hy
  refine ⟨{ defining := f, modulus := d.modulus, modulus_pos := d.modulus_pos
            smooth := hf, strongly_convex := hstrong, negative_nonempty := hne
            contains := ?_, compact_sublevel := ?_, sublevel_inside := ?_, regular_level := ?_ }⟩
  · intro x hx
    apply d.contains
    simpa [A', e] using hx
  · rw [hbody]
    exact d.compact_sublevel.image e.continuous
  · intro x hx
    have hh := d.sublevel_inside hx
    rw [hci] at hh
    simpa [e] using hh
  · exact fun x hx => gradient_ne_zero_on_convex_level
      (hf.differentiable (by norm_num))
      ((hstrong.strictConvexOn d.modulus_pos).convexOn) hne hx

end GaussianTilt.MomentMapRegularity
