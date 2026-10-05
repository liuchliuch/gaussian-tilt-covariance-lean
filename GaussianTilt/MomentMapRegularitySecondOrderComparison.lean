import GaussianTilt.MomentMapAlexandrovMaximum
import GaussianTilt.MomentMapRegularitySecondOrderDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Alexandrov comparison using literal supporting slopes

Boundary ordering gives inclusion of subgradient images of the strict
sublevel region, by compact minimization.  Compact-set Alexandrov identities
extend to bounded open sets by a proved exhaustion argument.  Strict density
ordering then yields the comparison principle, without classical Hessians.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators Gradient NNReal ENNReal Pointwise
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

/-- If `u ≥ v` on the boundary, any slope supporting `v` where `u < v`
supports `u` somewhere in the same strict sublevel region. -/
theorem subgradientImage_strict_sublevel_subset {u v : E n → ℝ}
    (hu : ConvexOn ℝ univ u) (huc : Continuous u)
    {S : Set (E n)} (hS : IsCompact S)
    (hb : ∀ y ∈ frontier S, v y ≤ u y) :
    subgradientImage v (interior S ∩ {y | u y < v y}) ⊆
      subgradientImage u (interior S ∩ {y | u y < v y}) := by
  rintro p ⟨x, ⟨hxi, hxuv⟩, hpx⟩
  change u x < v x at hxuv
  let F := fun y => u y - inner ℝ p y
  have hF : Continuous F := huc.sub (continuous_const.inner continuous_id)
  obtain ⟨z, hz, hmin⟩ := hS.exists_isMinOn ⟨x, interior_subset hxi⟩ hF.continuousOn
  have hzi : z ∈ interior S := by
    by_contra hzi
    have hzb : z ∈ frontier S := ⟨subset_closure hz, hzi⟩
    have hbound := hb z hzb
    have hsupport := hpx z
    have hm := hmin (interior_subset hxi)
    dsimp [F] at hm
    rw [inner_sub_right] at hsupport
    linarith
  have hzuv : u z < v z := by
    have hm := hmin (interior_subset hxi)
    have hs := hpx z
    dsimp [F] at hm
    rw [inner_sub_right] at hs
    linarith
  refine ⟨z, ⟨hzi, hzuv⟩, ?_⟩
  have hm := IsMinOn.of_isLocalMin_of_convex_univ
    (hmin.isLocalMin (mem_interior_iff_mem_nhds.mp hzi)) (alexandrov_convex_tilt hu p)
  intro y
  have h := hm y
  change u z - inner ℝ p z ≤ u y - inner ℝ p y at h
  rw [inner_sub_right]
  linarith

lemma subgradientImage_iUnion (u : E n → ℝ) {ι : Type*} (A : ι → Set (E n)) :
    subgradientImage u (⋃ i, A i) = ⋃ i, subgradientImage u (A i) := by
  ext p
  constructor
  · rintro ⟨x, hx, hs⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨i, x, hi, hs⟩
  · intro hp
    obtain ⟨i, x, hx, hs⟩ := mem_iUnion.mp hp
    exact ⟨x, mem_iUnion.mpr ⟨i, hx⟩, hs⟩

/-- An open subset of a compact set has an increasing compact exhaustion
in the ambient Euclidean space. -/
lemma exists_monotone_compact_exhaustion {S A : Set (E n)} (hS : IsCompact S)
    (hA : IsOpen A) (hAS : A ⊆ S) :
    ∃ K : ℕ → Set (E n), (∀ j, IsCompact (K j)) ∧ Monotone K ∧
      (∀ j, K j ⊆ A) ∧ ⋃ j, K j = A := by
  obtain ⟨F, hFc, hFA, hFU, hFm⟩ := hA.exists_iUnion_isClosed
  refine ⟨fun j => F j ∩ S, (fun j => hS.inter_left (hFc j)),
    (fun i j hij => inter_subset_inter_left S (hFm hij)),
    (fun j => inter_subset_left.trans (hFA j)), ?_⟩
  rw [← iUnion_inter, hFU, inter_eq_left.mpr hAS]

/-- A compact-set Alexandrov identity extends to every open subset of a
compact set, by continuity from below of both literal images and measures. -/
theorem alexandrov_identity_on_open_of_on_compact {u : E n → ℝ}
    {μ : Measure (E n)} {S A : Set (E n)} (hS : IsCompact S)
    (hid : ∀ K : Set (E n), IsCompact K → K ⊆ S → volume (subgradientImage u K) = μ K)
    (hA : IsOpen A) (hAS : A ⊆ S) :
    volume (subgradientImage u A) = μ A := by
  obtain ⟨K, hKc, hKm, hKA, hKU⟩ := exists_monotone_compact_exhaustion hS hA hAS
  have him : Monotone (fun j => subgradientImage u (K j)) :=
    fun i j hij => alexandrov_subgradientImage_mono u (hKm hij)
  rw [← hKU, subgradientImage_iUnion, him.measure_iUnion, hKm.measure_iUnion]
  exact iSup_congr fun j => hid (K j) (hKc j) ((hKA j).trans hAS)

/-- Strict Alexandrov density ordering implies comparison under boundary
ordering.  The densities enter through literal compact-set image identities,
not through a pre-existing classical Monge--Ampère equation. -/
theorem alexandrov_comparison_of_strict_density {u v f g : E n → ℝ}
    (hu : ConvexOn ℝ univ u) (huc : Continuous u) (hvc : Continuous v)
    {S : Set (E n)} (hS : IsCompact S)
    (hb : ∀ y ∈ frontier S, v y ≤ u y)
    (hgm : Measurable g) (hfn : ∀ y ∈ interior S, 0 ≤ f y)
    (hfg : ∀ y ∈ interior S, f y < g y)
    (huid : ∀ A : Set (E n), IsCompact A → A ⊆ S →
      volume (subgradientImage u A) = (volume.withDensity (fun y => ENNReal.ofReal (f y))) A)
    (hvid : ∀ A : Set (E n), IsCompact A → A ⊆ S →
      volume (subgradientImage v A) = (volume.withDensity (fun y => ENNReal.ofReal (g y))) A) :
    ∀ x ∈ S, v x ≤ u x := by
  intro x hx
  by_contra hxuv
  have hxuv : u x < v x := lt_of_not_ge hxuv
  have hxi : x ∈ interior S := by
    by_contra hxi
    exact hxuv.not_ge (hb x ⟨subset_closure hx, hxi⟩)
  let A : Set (E n) := interior S ∩ {y | u y < v y}
  have hA : IsOpen A := isOpen_interior.inter (isOpen_lt huc hvc)
  have hAS : A ⊆ S := inter_subset_left.trans interior_subset
  have hApos : 0 < volume A := hA.measure_pos volume ⟨x, hxi, hxuv⟩
  have hAu := alexandrov_identity_on_open_of_on_compact hS huid hA hAS
  have hAv := alexandrov_identity_on_open_of_on_compact hS hvid hA hAS
  have hAu_fin : volume (subgradientImage u A) ≠ ⊤ :=
    ne_top_of_le_ne_top (alexandrov_isCompact_subgradientImage huc hS).measure_ne_top
      (measure_mono (alexandrov_subgradientImage_mono u hAS))
  have hfi : ∫⁻ y in A, ENNReal.ofReal (f y) ∂volume ≠ ⊤ := by
    rwa [← withDensity_apply _ hA.measurableSet, ← hAu]
  have hlt : (volume.withDensity (fun y => ENNReal.ofReal (f y))) A <
      (volume.withDensity (fun y => ENNReal.ofReal (g y))) A := by
    rw [withDensity_apply _ hA.measurableSet, withDensity_apply _ hA.measurableSet]
    apply setLIntegral_strict_mono hA.measurableSet hApos.ne' hgm.ennreal_ofReal hfi
    filter_upwards [] with y
    intro hy
    exact ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt (hfn y hy.1) (hfg y hy.1)) |>.mpr (hfg y hy.1)
  have hle := measure_mono (μ := volume) (subgradientImage_strict_sublevel_subset hu huc hS hb)
  change volume (subgradientImage v A) ≤ volume (subgradientImage u A) at hle
  rw [hAu, hAv] at hle
  exact hlt.not_ge hle

lemma supportsAt_pos_mul_add_const_iff {u : E n → ℝ} {t : ℝ} (ht : 0 < t)
    (b : ℝ) (p x : E n) :
    SupportsAt (fun y => t * u y + b) (t • p) x ↔ SupportsAt u p x := by
  constructor
  · intro h y
    have hh := h y
    simp only [real_inner_smul_left] at hh
    change t * u x + b + t * inner ℝ p (y - x) ≤ t * u y + b at hh
    have he : t * (u x + inner ℝ p (y - x)) ≤ t * u y := by linarith
    exact (mul_le_mul_left ht).mp he
  · intro h y
    have hh := mul_le_mul_of_nonneg_left (h y) ht.le
    change t * u x + b + inner ℝ (t • p) (y - x) ≤ t * u y + b
    rw [real_inner_smul_left]
    linarith

/-- Scaling a convex potential scales its literal supporting slopes. -/
theorem subgradientImage_pos_mul_add_const (u : E n → ℝ) {t : ℝ} (ht : 0 < t)
    (b : ℝ) (A : Set (E n)) :
    subgradientImage (fun y => t * u y + b) A = (fun p => t • p) '' subgradientImage u A := by
  ext p
  constructor
  · rintro ⟨x, hx, hs⟩
    have hp : t • (t⁻¹ • p) = p := by rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
    refine ⟨t⁻¹ • p, ⟨x, hx, ?_⟩, hp⟩
    apply (supportsAt_pos_mul_add_const_iff ht b _ _).mp
    simpa only [hp] using hs
  · rintro ⟨q, ⟨x, hx, hs⟩, rfl⟩
    exact ⟨x, hx, (supportsAt_pos_mul_add_const_iff ht b q x).mpr hs⟩

/-- Exact homogeneity of Alexandrov mass for a positive vertical scaling. -/
theorem volume_subgradientImage_pos_mul_add_const (u : E n → ℝ) {t : ℝ}
    (ht : 0 < t) (b : ℝ) (A : Set (E n)) :
    volume (subgradientImage (fun y => t * u y + b) A) =
      ENNReal.ofReal (t ^ n) * volume (subgradientImage u A) := by
  rw [subgradientImage_pos_mul_add_const u ht b A]
  change volume (t • subgradientImage u A) = _
  simpa [E, Reference.Space] using volume.addHaar_smul_of_nonneg ht.le (subgradientImage u A)

/-- Equality or non-strict ordering of positive Alexandrov densities still
implies comparison. A small vertical scaling makes the density inequality
strict while preserving a putative violation and the boundary ordering. -/
theorem alexandrov_comparison_of_density_le [NeZero n] {u v f g : E n → ℝ}
    (hu : ConvexOn ℝ univ u) (huc : Continuous u) (hvc : Continuous v)
    {S : Set (E n)} (hS : IsCompact S)
    (hb : ∀ y ∈ frontier S, v y ≤ u y)
    (hgm : Measurable g) (hfn : ∀ y ∈ interior S, 0 ≤ f y)
    (hgp : ∀ y ∈ interior S, 0 < g y) (hfg : ∀ y ∈ interior S, f y ≤ g y)
    (huid : ∀ A : Set (E n), IsCompact A → A ⊆ S →
      volume (subgradientImage u A) = (volume.withDensity (fun y => ENNReal.ofReal (f y))) A)
    (hvid : ∀ A : Set (E n), IsCompact A → A ⊆ S →
      volume (subgradientImage v A) = (volume.withDensity (fun y => ENNReal.ofReal (g y))) A) :
    ∀ x ∈ S, v x ≤ u x := by
  intro x hx
  by_contra hxuv
  have hxuv : u x < v x := lt_of_not_ge hxuv
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn huc.continuousOn
  have hMu : ∀ y ∈ S, u y ≤ M := fun y hy =>
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hM y hy)
  have hcont : Continuous (fun t : ℝ => t * u x + (1 - t) * M) := by fun_prop
  have hnear : ∀ᶠ t : ℝ in 𝓝 1, t * u x + (1 - t) * M < v x :=
    hcont.continuousAt.eventually (eventually_lt_nhds (by simpa using hxuv))
  have hex : ∃ t : ℝ, 0 < t ∧ t < 1 ∧ t * u x + (1 - t) * M < v x := by
    have hnear' : ∀ᶠ t : ℝ in 𝓝[<] 1, t * u x + (1 - t) * M < v x :=
      nhdsWithin_le_nhds hnear
    have hpos : ∀ᶠ t : ℝ in 𝓝[<] 1, 0 < t :=
      nhdsWithin_le_nhds (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))
    have hlt : ∀ᶠ t : ℝ in 𝓝[<] 1, t < 1 := self_mem_nhdsWithin
    exact (hpos.and (hlt.and hnear')).exists
  obtain ⟨t, ht, ht1, htx⟩ := hex
  let w : E n → ℝ := fun y => t * u y + (1 - t) * M
  have hwc : Continuous w := (continuous_const.mul huc).add continuous_const
  have hwconv : ConvexOn ℝ univ w := (hu.smul ht.le).add (convexOn_const _ convex_univ)
  have hwb : ∀ y ∈ frontier S, v y ≤ w y := by
    intro y hy
    have hyS : y ∈ S := hS.isClosed.closure_subset hy.1
    have hbound := hMu y hyS
    have hvu := hb y hy
    dsimp [w]
    nlinarith
  have htpow0 : 0 ≤ t ^ n := pow_nonneg ht.le _
  have htpow1 : t ^ n < 1 := pow_lt_one₀ ht.le ht1 (NeZero.ne n)
  have hwid : ∀ A : Set (E n), IsCompact A → A ⊆ S →
      volume (subgradientImage w A) =
        (volume.withDensity (fun y => ENNReal.ofReal (t ^ n * f y))) A := by
    intro A hA hAS
    rw [show w = (fun y => t * u y + (1 - t) * M) from rfl,
      volume_subgradientImage_pos_mul_add_const u ht _ A, huid A hA hAS]
    simp_rw [ENNReal.ofReal_mul htpow0]
    have hm := withDensity_smul' (μ := (volume : Measure (E n)))
      (ENNReal.ofReal (t ^ n)) (fun y => ENNReal.ofReal (f y)) ENNReal.ofReal_ne_top
    have ha := congrArg (fun μ : Measure (E n) => μ A) hm
    simpa only [Pi.smul_apply, smul_eq_mul, Measure.smul_apply] using ha.symm
  have hcmp := alexandrov_comparison_of_strict_density hwconv hwc hvc hS hwb hgm
    (fun y hy => mul_nonneg htpow0 (hfn y hy))
    (fun y hy => lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hfg y hy) htpow0)
      (by nlinarith [hgp y hy])) hwid hvid x hx
  exact htx.not_ge hcmp

end GaussianTilt.MomentMapRegularity
