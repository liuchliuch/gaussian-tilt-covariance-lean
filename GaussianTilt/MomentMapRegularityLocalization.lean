import GaussianTilt.MomentMapRegularityDualDifferentiability

/-!
# Actual subgradient images and contact sets

These are geometric and measure-theoretic prerequisites for Alexandrov
localization. The subgradient relation is the literal global supporting-plane
inequality; it is not an assumed Monge--Ampère operator.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators Gradient NNReal ENNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

/-- The literal global supporting-plane relation. -/
def SupportsAt (φ : E n → ℝ) (p x : E n) : Prop :=
  ∀ y, φ x + inner ℝ p (y - x) ≤ φ y

/-- All slopes of supporting planes touching a set. -/
def subgradientImage (φ : E n → ℝ) (A : Set (E n)) : Set (E n) :=
  {p | ∃ x ∈ A, SupportsAt φ p x}

/-- The contact set of a fixed supporting slope. -/
def contactSet (φ : E n → ℝ) (p : E n) : Set (E n) :=
  {x | SupportsAt φ p x}

lemma supportsAt_gradient {φ : E n → ℝ} (hc : ConvexOn ℝ univ φ)
    {x : E n} (hx : DifferentiableAt ℝ φ x) : SupportsAt φ (gradient φ x) x :=
  convex_gradient_support hc hx

lemma supportsAt_mono {φ : E n → ℝ} {p q x y : E n}
    (hx : SupportsAt φ p x) (hy : SupportsAt φ q y) :
    0 ≤ inner ℝ (q - p) (y - x) := by
  have hx' := hx y
  have hy' := hy x
  rw [inner_sub_left]
  have he : inner ℝ q (x - y) = -inner ℝ q (y - x) := by
    rw [← inner_neg_right, neg_sub]
  rw [he] at hy'
  linarith

/-- A global Lipschitz bound bounds every supporting slope, including slopes
at points where the source is not differentiable. -/
lemma supportsAt_norm_le {φ : E n → ℝ} {L : ℝ≥0} (hL : LipschitzWith L φ)
    {p x : E n} (hx : SupportsAt φ p x) : ‖p‖ ≤ L := by
  have hs := hx (x + p)
  simp only [add_sub_cancel_left, real_inner_self_eq_norm_sq] at hs
  have hb := hL.norm_sub_le (x + p) x
  simp only [add_sub_cancel_left, Real.norm_eq_abs] at hb
  have hu := (le_abs_self (φ (x + p) - φ x)).trans hb
  nlinarith [norm_nonneg p, L.coe_nonneg]

lemma isClosed_supportsAt_graph {φ : E n → ℝ} (hφ : Continuous φ) :
    IsClosed {z : E n × E n | SupportsAt φ z.2 z.1} := by
  simp only [SupportsAt, setOf_forall]
  apply isClosed_iInter
  intro y
  exact isClosed_le ((hφ.comp continuous_fst).add
    (continuous_snd.inner (continuous_const.sub continuous_fst))) continuous_const

/-- Compact source sets have compact literal subgradient images. -/
theorem isCompact_subgradientImage {φ : E n → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L φ) {A : Set (E n)} (hA : IsCompact A) :
    IsCompact (subgradientImage φ A) := by
  let G := (A ×ˢ Metric.closedBall (0 : E n) (L : ℝ)) ∩
    {z : E n × E n | SupportsAt φ z.2 z.1}
  have hG : IsCompact G := (hA.prod (isCompact_closedBall 0 (L : ℝ))).inter_right
    (isClosed_supportsAt_graph hL.continuous)
  have he : subgradientImage φ A = Prod.snd '' G := by
    ext p
    constructor
    · rintro ⟨x, hx, hs⟩
      refine ⟨(x, p), ⟨⟨hx, ?_⟩, hs⟩, rfl⟩
      simpa only [Metric.mem_closedBall, dist_zero_right] using supportsAt_norm_le hL hs
    · rintro ⟨⟨x, p⟩, ⟨⟨hx, _⟩, hs⟩, rfl⟩
      exact ⟨x, hx, hs⟩
  rw [he]
  exact hG.image continuous_snd

lemma contactSet_eq_level {φ : E n → ℝ} {p x : E n}
    (hx : SupportsAt φ p x) :
    contactSet φ p = {y | φ y - inner ℝ p y = φ x - inner ℝ p x} := by
  ext y
  constructor
  · intro hy
    have hxy := hx y
    have hyx := hy x
    simp only [inner_sub_right] at hxy hyx
    dsimp
    linarith
  · intro he z
    have hxz := hx z
    dsimp at he
    simp only [inner_sub_right] at hxz ⊢
    linarith

lemma isClosed_contactSet {φ : E n → ℝ} (hφ : Continuous φ) (p : E n) :
    IsClosed (contactSet φ p) := by
  exact (isClosed_supportsAt_graph hφ).preimage (continuous_id.prodMk continuous_const)

lemma convex_contactSet {φ : E n → ℝ} (hc : ConvexOn ℝ univ φ) (p : E n) :
    Convex ℝ (contactSet φ p) := by
  intro x hx y hy a b ha hb hab
  intro z
  have hcxy := hc.2 (mem_univ x) (mem_univ y) ha hb hab
  have hxz := mul_le_mul_of_nonneg_left (hx z) ha
  have hyz := mul_le_mul_of_nonneg_left (hy z) hb
  simp only [smul_eq_mul] at hcxy
  simp only [inner_sub_right, inner_add_right, inner_smul_right]
  simp only [inner_sub_right] at hxz hyz
  nlinarith [congrArg (fun t : ℝ => t * φ z) hab,
    congrArg (fun t : ℝ => t * inner ℝ p z) hab]

/-- Interior contact sets are compact as a consequence of the actual
transport equation, even before any strict-convexity theorem. -/
theorem isCompact_contactSet_of_target_density {φ V : E n → ℝ}
    (hφ : Continuous φ) (hc : ConvexOn ℝ univ φ) {K : Set (E n)}
    (hK : IsOpen K) (hV : ContinuousOn V K)
    (hmap : (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x)))).map
      (gradient φ) = volume.withDensity (fun x => ENNReal.ofReal
        (K.indicator (fun y => Real.exp (-V y)) x)))
    {p : E n} (hp : p ∈ K) : IsCompact (contactSet φ p) := by
  by_cases hn : (contactSet φ p).Nonempty
  · obtain ⟨x, hx⟩ := hn
    apply (compact_tilted_section_of_target_density hφ hc hK hV hmap hp
      (φ x - inner ℝ p x)).of_isClosed_subset (isClosed_contactSet hφ p)
    rw [contactSet_eq_level hx]
    intro y hy
    exact hy.le
  · simpa [Set.not_nonempty_iff_eq_empty.mp hn] using (isCompact_empty : IsCompact (∅ : Set (E n)))

/-- A full-measure gradient constraint controls *all* subgradients. The proof
uses monotonicity, density of differentiability points, and geometric
Hahn--Banach separation; it assumes no source smoothness. -/
theorem supportsAt_mem_closure_of_ae_gradient {φ : E n → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L φ) (hc : ConvexOn ℝ univ φ) {K : Set (E n)}
    (hKc : Convex ℝ K) (hg : ∀ᵐ y ∂volume, gradient φ y ∈ K)
    {p x : E n} (hx : SupportsAt φ p x) : p ∈ closure K := by
  by_contra hp
  obtain ⟨f, u, hfu, hup⟩ := geometric_hahn_banach_closed_point hKc.closure isClosed_closure hp
  let v : E n := (InnerProductSpace.toDual ℝ (E n)).symm f
  have hfv (q : E n) : inner ℝ v q = f q := by
    change (InnerProductSpace.toDual ℝ (E n)) v q = f q
    simp [v]
  let C : ℝ := (L : ℝ) + ‖p‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hδ : 0 < (f p - u) / C := div_pos (sub_pos.mpr hup) hC
  have hdense := volume.dense_of_ae ((MomentMapCoercivity.convex_ae_differentiable hc).and hg)
  obtain ⟨y, ⟨hyd, hyK⟩, hyδ⟩ := (Metric.mem_closure_iff.mp (hdense (x + v)))
    ((f p - u) / C) hδ
  let q := gradient φ y
  have hq := supportsAt_gradient hc hyd
  have hmono := supportsAt_mono hx hq
  have hqnorm : ‖q‖ ≤ L := supportsAt_norm_le hL hq
  have hqp : ‖q - p‖ < C := by
    exact lt_of_le_of_lt (norm_sub_le q p) (by dsimp [C]; linarith)
  have hnear : ‖y - (x + v)‖ < (f p - u) / C := by
    simpa only [dist_comm, dist_eq_norm] using hyδ
  have herr : inner ℝ (q - p) (y - (x + v)) < f p - u := by
    calc
      _ ≤ |inner ℝ (q - p) (y - (x + v))| := le_abs_self _
      _ ≤ ‖q - p‖ * ‖y - (x + v)‖ := abs_real_inner_le_norm _ _
      _ ≤ C * ‖y - (x + v)‖ := mul_le_mul_of_nonneg_right hqp.le (norm_nonneg _)
      _ < C * ((f p - u) / C) := mul_lt_mul_of_pos_left hnear hC
      _ = f p - u := by field_simp
  have hqf : f q < u := hfu q (subset_closure hyK)
  have he : inner ℝ (q - p) (y - x) =
      f q - f p + inner ℝ (q - p) (y - (x + v)) := by
    rw [show y - x = v + (y - (x + v)) by module, inner_add_right,
      show inner ℝ (q - p) v = f (q - p) from
        (real_inner_comm _ _).trans (hfv _), map_sub]
  change 0 ≤ inner ℝ (q - p) (y - x) at hmono
  rw [he] at hmono
  linarith

/-- The literal transport identity forces the gradient to lie in K at
Lebesgue-almost every source point, since exp(-φ) is everywhere positive. -/
theorem ae_gradient_mem_of_target_density {φ V : E n → ℝ}
    (hφ : Continuous φ) {K : Set (E n)} (hK : IsOpen K)
    (hV : ContinuousOn V K)
    (hmap : (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x)))).map
      (gradient φ) = volume.withDensity (fun x => ENNReal.ofReal
        (K.indicator (fun y => Real.exp (-V y)) x))) :
    ∀ᵐ x ∂volume, gradient φ x ∈ K := by
  have hg : Measurable (gradient φ) :=
    (InnerProductSpace.toDual ℝ (E n)).symm.continuous.measurable.comp (measurable_fderiv ℝ φ)
  have ht := target_ae_mem hK hV
  rw [← hmap] at ht
  have hs := (ae_map_iff hg.aemeasurable hK.measurableSet).mp ht
  have hden : Measurable (fun x => ENNReal.ofReal (Real.exp (-φ x))) :=
    ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp hφ.neg).measurable
  have hs' := (ae_withDensity_iff hden).mp hs
  filter_upwards [hs'] with x hx
  exact hx (by simp [Real.exp_pos])

/-- All actual supporting slopes are confined to the closed convex target. -/
theorem subgradientImage_subset_closure_of_target_density {φ V : E n → ℝ}
    {L : ℝ≥0} (hL : LipschitzWith L φ) (hc : ConvexOn ℝ univ φ)
    {K : Set (E n)} (hK : IsOpen K) (hKc : Convex ℝ K) (hV : ContinuousOn V K)
    (hmap : (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x)))).map
      (gradient φ) = volume.withDensity (fun x => ENNReal.ofReal
        (K.indicator (fun y => Real.exp (-V y)) x))) (A : Set (E n)) :
    subgradientImage φ A ⊆ closure K := by
  rintro p ⟨x, _, hx⟩
  exact supportsAt_mem_closure_of_ae_gradient hL hc hKc
    (ae_gradient_mem_of_target_density hL.continuous hK hV hmap) hx

/-- The fundamental Alexandrov identification on compact source sets: the
target measure of the literal subgradient image equals source mass. Every
uniqueness premise is discharged by the actual interior Legendre potential. -/
theorem measure_subgradientImage_of_target_density {φ V : E n → ℝ}
    {L : ℝ≥0} (hL : LipschitzWith L φ) (hc : ConvexOn ℝ univ φ)
    {K : Set (E n)} (hK : IsOpen K) (hKc : Convex ℝ K) (hV : ContinuousOn V K)
    (hmap : (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x)))).map
      (gradient φ) = volume.withDensity (fun x => ENNReal.ofReal
        (K.indicator (fun y => Real.exp (-V y)) x)))
    {A : Set (E n)} (hA : IsCompact A) :
    (volume.withDensity (fun x => ENNReal.ofReal
      (K.indicator (fun y => Real.exp (-V y)) x))) (subgradientImage φ A) =
    (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x)))) A := by
  let ν := volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x)))
  have hg : Measurable (gradient φ) :=
    (InnerProductSpace.toDual ℝ (E n)).symm.continuous.measurable.comp (measurable_fderiv ℝ φ)
  have huniq := ae_unique_source_support hL.continuous hc hK hKc hV hmap
  rw [← hmap] at huniq
  have huniq' := ae_of_ae_map hg.aemeasurable huniq
  have hd : ∀ᵐ x ∂ν, DifferentiableAt ℝ φ x :=
    (withDensity_absolutelyContinuous volume _).ae_le
      (MomentMapCoercivity.convex_ae_differentiable hc)
  rw [← hmap, Measure.map_apply hg (isCompact_subgradientImage hL hA).measurableSet]
  apply measure_congr
  filter_upwards [hd, huniq'] with x hdx hux
  apply propext
  constructor
  · rintro ⟨y, hy, hsy⟩
    have he : x = y := hux x y (supportsAt_gradient hc hdx) hsy
    simpa [he] using hy
  · intro hx
    exact ⟨x, hx, supportsAt_gradient hc hdx⟩

end GaussianTilt.MomentMapRegularity
