import GaussianTilt.MomentMapRegularityLocalizationWidth
import GaussianTilt.MomentMapRegularityLocalizationExposed
import GaussianTilt.MomentMapRegularityLocalizationAffine
import GaussianTilt.MomentMapRegularityLocalizationStrictness
import GaussianTilt.MomentMapAffineNormalization

/-! # Contact localization and strict convexity of genuine moment sources -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators Gradient NNReal ENNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

lemma convexOn_comp_affineSource {u : E n → ℝ} (hu : ConvexOn ℝ univ u)
    (T : E n ≃L[ℝ] E n) (a : E n) :
    ConvexOn ℝ univ (fun y => u (affineSource T a y)) := by
  simpa only [Set.preimage_univ, Function.comp_def, affineSource, add_comm] using
    (hu.translate_right a).comp_linearMap T.symm.toLinearEquiv.toLinearMap

lemma forward_image_eq_affineSource_preimage (T : E n ≃L[ℝ] E n)
    (a : E n) (S : Set (E n)) :
    (fun y => T (y - a)) '' S = affineSource T a ⁻¹' S := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa [affineSource] using hz
  · intro hy
    exact ⟨affineSource T a y, hy, by simp [affineSource]⟩

lemma inner_affineSource_difference (T : E n ≃L[ℝ] E n)
    (a v y z : E n) :
    inner ℝ (affineSlope T 0 v) (y - z) =
      inner ℝ v (affineSource T a y - affineSource T a z) := by
  rw [affineSlope, sub_zero, LinearMap.adjoint_inner_left]
  change inner ℝ v (T.symm (y - z)) = _
  simp [affineSource, map_sub]

/-- Fixed finite dimension constant used after actual affine normalization. -/
def localizationWidthConstant (n : ℕ) : ℝ :=
  4 ^ n * 2 ^ n * (2 * ((n : ℝ) + 1) ^ (n - 1) *
    (2 * (3 * ((n : ℝ) + 1) ^ 2)) ^ n) *
      volume.real (Metric.closedBall (0 : E n) (3 * ((n : ℝ) + 1) ^ 2))

/-- The normalized obstruction, transferred back to a genuine unnormalized
tilted section. Every affine normalization and Jacobian factor is proved. -/
theorem tilted_section_width_obstruction [NeZero n] {φ : E n → ℝ}
    (hc : ConvexOn ℝ univ φ) {p x v z : E n} (hx : SupportsAt φ p x)
    {a b ε lam Lam : ℝ} (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) (hε : 0 < ε)
    (hlam : 0 ≤ lam) (hLam : 0 ≤ Lam)
    (hS : IsCompact (tiltedContactSection φ p x v a ε))
    (hz : z ∈ tiltedContactSection φ p x v a ε) (hzv : inner ℝ v (z - x) = -a)
    (hslab : ∀ y ∈ tiltedContactSection φ p x v a ε, inner ℝ v (y - x) < b)
    (hmass : ∀ A : Set (E n), IsCompact A → A ⊆ tiltedContactSection φ p x v a ε →
      ENNReal.ofReal lam * volume A ≤ volume (subgradientImage φ A) ∧
      volume (subgradientImage φ A) ≤ ENNReal.ofReal Lam * volume A) :
    lam ≤ localizationWidthConstant n * (b / a) * Lam := by
  let S := tiltedContactSection φ p x v a ε
  let w := tiltedContactPotential φ p x v a ε
  have hφ : Continuous φ := continuousOn_univ.mp (hc.continuousOn isOpen_univ)
  have hxi : x ∈ interior S := center_mem_interior_tiltedContactSection hφ p x v ha hε
  obtain ⟨c, T, hball, houter⟩ := exists_affine_normalization_explicit hS
    (convex_tiltedContactSection hc p x v a ε) ⟨x, hxi⟩
  let N := (fun y => T (y - c)) '' S
  let u := fun y => w (affineSource T c y)
  let x' := T (x - c)
  let z' := T (z - c)
  let v' := affineSlope T 0 v
  let R : ℝ := 3 * ((n : ℝ) + 1) ^ 2
  have hR : 0 < R := by dsimp [R]; positivity
  have hNc : IsCompact N := hS.image (T.continuous.comp (continuous_id.sub continuous_const))
  have huc : ConvexOn ℝ univ u := convexOn_comp_affineSource (convexOn_tiltedContactPotential hc p x v a ε) T c
  have hcontu : Continuous u := continuousOn_univ.mp (huc.continuousOn isOpen_univ)
  have hforward (y : E n) : affineSource T c (T (y - c)) = y := by simp [affineSource]
  have hpre : N = affineSource T c ⁻¹' S := forward_image_eq_affineSource_preimage T c S
  have hNx : x' ∈ N := ⟨x, interior_subset hxi, rfl⟩
  have hNz : z' ∈ N := ⟨z, hz, rfl⟩
  have hNsublevel : N = {y | u y ≤ 0} := by
    rw [hpre]
    ext y
    simp only [S, u, w, tiltedContactSection, tiltedContactPotential,
      mem_preimage, mem_setOf_eq, sub_nonpos]
  have hvalue : u x' = -ε * a := by
    dsimp [u, x', w]
    rw [hforward, tiltedContactPotential_center]
  have hbound : ∀ y ∈ N, -(2 * ε * a) ≤ u y ∧ u y ≤ 0 := by
    intro y hy
    have hyS : affineSource T c y ∈ S := by rw [hpre] at hy; exact hy
    have hsy := hx (affineSource T c y)
    have hsb := hslab (affineSource T c y) hyS
    have hym := hyS
    change φ (affineSource T c y) - φ x - inner ℝ p (affineSource T c y - x) ≤
      ε * (inner ℝ v (affineSource T c y - x) + a) at hym
    dsimp [u, w, tiltedContactPotential]
    constructor <;> nlinarith
  have hboundary : ∀ y ∈ frontier N, 0 ≤ u y := by
    rw [hNsublevel]
    intro y hy
    exact (frontier_le_subset_eq hcontu continuous_const hy).ge
  have hupper : ∀ y ∈ N, inner ℝ v' (y - x') ≤ b := by
    intro y hy
    have hyS : affineSource T c y ∈ S := by rw [hpre] at hy; exact hy
    dsimp [v']
    rw [inner_affineSource_difference, show affineSource T c x' = x by simp [x', affineSource]]
    exact (hslab _ hyS).le
  have hlower : inner ℝ v' (z' - x') ≤ -a := by
    dsimp [v']
    rw [inner_affineSource_difference, show affineSource T c x' = x by simp [x', affineSource],
      show affineSource T c z' = z by simp [z', affineSource], hzv]
  let d := |LinearMap.det T.symm.toLinearEquiv.toLinearMap|
  let q := d ^ 2
  have hd : 0 < d := abs_pos.mpr T.symm.toLinearEquiv.isUnit_det'.ne_zero
  have hq : 0 < q := sq_pos_of_pos hd
  let P := p + ε • v
  let k := φ x - inner ℝ p x + ε * (a - inner ℝ v x)
  have hueq : u = affinePotential φ T c P k := by
    funext y
    exact tiltedContactPotential_eq φ p x v a ε (affineSource T c y)
  have hden (A : Set (E n)) (hA : IsCompact A) (hAN : A ⊆ N) :
      ENNReal.ofReal (q * lam) * volume A ≤ volume (subgradientImage u A) ∧
      volume (subgradientImage u A) ≤ ENNReal.ofReal (q * Lam) * volume A := by
    have hIA : IsCompact (affineSource T c '' A) := hA.image (T.symm.continuous.add continuous_const)
    have hIAS : affineSource T c '' A ⊆ S := by
      rintro _ ⟨y, hy, rfl⟩
      have hh := hAN hy
      rwa [hpre] at hh
    have h := subgradientImage_affine_density_bounds φ T c P k A
      (hmass _ hIA hIAS).1 (hmass _ hIA hIAS).2
    have he (r : ℝ) : ENNReal.ofReal (q * r) = affineJacobian T ^ 2 * ENNReal.ofReal r := by
      rw [ENNReal.ofReal_mul hq.le, ENNReal.ofReal_pow hd.le]
      rfl
    rw [hueq, he lam, he Lam]
    exact h
  have hmassL := (hden (Metric.closedBall (0 : E n) (1 / 2)) (isCompact_closedBall _ _)
    ((Metric.closedBall_subset_closedBall (by norm_num)).trans hball)).1
  have hmassU := (hden N hNc Subset.rfl).2
  have h := normalized_relative_width_obstruction huc hNc hball hR houter hNx hNz hb ha
    (by norm_num : (0 : ℝ) ≤ 2) hq hlam hLam hbound
    (by rw [hvalue]; nlinarith : u x' < 0)
    (by rw [hvalue]; ring_nf; exact le_rfl : 2 * ε * a ≤ 2 * (-u x'))
    hboundary hupper hlower hmassL hmassU
  dsimp [localizationWidthConstant, R] at *
  convert h using 1 <;> ring

/-- Caffarelli contact localization for the genuine global moment source.
The actual Alexandrov equation, affine normalization, cone maximum
principle, exposed contact construction, and thin-section contradiction are
all discharged. No strict-convexity or named regularity premise is used. -/
theorem strictConvexOn_of_target_density {φ V : E n → ℝ}
    {L : ℝ≥0} (hL : LipschitzWith L φ) (hc : ConvexOn ℝ univ φ)
    {K : Set (E n)} (hK : IsOpen K) (hKc : Convex ℝ K)
    (hKb : Bornology.IsBounded K) (hV : ContinuousOn V (closure K))
    (hmap : (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x)))).map
      (gradient φ) = volume.withDensity (fun x => ENNReal.ofReal
        (K.indicator (fun y => Real.exp (-V y)) x))) :
    StrictConvexOn ℝ univ φ := by
  by_cases hn : n = 0
  · subst n
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy hxy a b ha hb hab
    exact (hxy (Subsingleton.elim x y)).elim
  haveI : NeZero n := ⟨hn⟩
  have hφ := hL.continuous
  have hVK := hV.mono subset_closure
  obtain ⟨w, hw⟩ := (ae_gradient_mem_of_target_density hφ hK hVK hmap).exists
  apply strictConvexOn_of_subsingleton_contactSet hL hc
  intro p x hx y hy
  by_contra hxy
  obtain ⟨e, he, v, δ, hδ, hpδ, hexpose⟩ :=
    contactSet_has_exposed_inward_tilt hφ hc hK hVK hmap hw ⟨x, hx⟩
  obtain ⟨y₀, hy₀, hne⟩ : ∃ y₀ ∈ contactSet φ p, y₀ ≠ e := by
    by_cases hxe : x = e
    · exact ⟨y, hy, fun hye => hxy (hxe.trans hye.symm)⟩
    · exact ⟨x, hx, hxe⟩
  have hyv := hexpose y₀ hy₀ hne
  let a := -inner ℝ v (y₀ - e) / 2
  have ha : 0 < a := by dsimp [a]; linarith
  have hyva : inner ℝ v (y₀ - e) < -a := by dsimp [a]; linarith
  obtain ⟨z, hzC, hzv, hzSections⟩ := exists_contact_at_linear_height hc he hy₀ ha hyva
  let B := tiltedContactSection φ p e v a δ
  have hB : IsCompact B := by
    dsimp [B]
    rw [tiltedContactSection_eq_tilted_sublevel]
    exact compact_tilted_section_of_target_density hφ hc hK hVK hmap hpδ _
  obtain ⟨lam, Lam, hlam, hLam, hmass⟩ :=
    local_subgradientImage_volume_bounds hL hc hK hKc hKb hV hmap hB
  have hv : ∀ t ∈ contactSet φ p, inner ℝ v (t - e) ≤ 0 := by
    intro t ht
    by_cases hte : t = e
    · subst t; simp
    · exact (hexpose t ht hte).le
  let D := localizationWidthConstant n * Lam / a
  have hsmall : ∀ b : ℝ, 0 < b → b < a → lam ≤ D * b := by
    intro b hb hba
    obtain ⟨η, hη, hηslab⟩ := tilted_sections_eventually_in_thin_slab
      hφ hc hK hVK hmap he hv hδ hpδ hb (a := a)
    let ε := min δ η / 2
    have hε : 0 < ε := by dsimp [ε]; positivity
    have hεδ : ε ≤ δ := by dsimp [ε]; have := min_le_left δ η; linarith
    have hεη : ε < η := by dsimp [ε]; have := min_le_right δ η; linarith
    have hSB : tiltedContactSection φ p e v a ε ⊆ B :=
      tiltedContactSection_mono he a hε hεδ
    have hSc : IsCompact (tiltedContactSection φ p e v a ε) := by
      apply hB.of_isClosed_subset ?_ hSB
      rw [tiltedContactSection_eq_potential_sublevel]
      exact isClosed_le (continuous_tiltedContactPotential hφ p e v a ε) continuous_const
    have hobs := tilted_section_width_obstruction hc he ha hb hba.le hε hlam.le hLam.le
      hSc (hzSections ε).1 hzv (fun t ht => (hηslab ε hε hεη t ht).2.1)
      (fun A hA hAS => hmass A hA (hAS.trans hSB))
    convert hobs using 1 <;> dsimp [D] <;> ring
  have htend : Tendsto (fun b : ℝ => D * b) (𝓝[>] 0) (𝓝 0) := by
    simpa using ((continuous_const.mul continuous_id).tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hevent : ∀ᶠ b : ℝ in 𝓝[>] 0, lam ≤ D * b := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds ha)] with b hb hba
    exact hsmall b hb hba
  have hzero : lam ≤ 0 := ge_of_tendsto htend hevent
  exact (not_le_of_gt hlam) hzero

end GaussianTilt.MomentMapRegularity
