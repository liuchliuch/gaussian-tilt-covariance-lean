import GaussianTilt.MomentMapRegularityDirichlet
import GaussianTilt.MomentMapRegularitySecondOrderComparison

/-! # Alexandrov comparison on the actual bounded domain -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators Gradient NNReal ENNReal Pointwise
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

lemma subgradientImageOn_mono (S : Set (E n)) (u : E n → ℝ) {A B : Set (E n)}
    (h : A ⊆ B) : subgradientImageOn S u A ⊆ subgradientImageOn S u B := by
  rintro p ⟨x, hx, hp⟩
  exact ⟨x, h hx, hp⟩

theorem alexandrovOn_identity_on_open_of_on_compact {u : E n → ℝ}
    {μ : Measure (E n)} {S A : Set (E n)} (hS : IsCompact S)
    (hid : ∀ K : Set (E n), IsCompact K → K ⊆ interior S → volume (subgradientImageOn S u K) = μ K)
    (hA : IsOpen A) (hAS : A ⊆ interior S) :
    volume (subgradientImageOn S u A) = μ A := by
  obtain ⟨K, hKc, hKm, hKA, hKU⟩ := exists_monotone_compact_exhaustion hS hA (hAS.trans interior_subset)
  have him : Monotone (fun j => subgradientImageOn S u (K j)) :=
    fun i j hij => subgradientImageOn_mono S u (hKm hij)
  rw [← hKU, subgradientImageOn_iUnion, him.measure_iUnion, hKm.measure_iUnion]
  exact iSup_congr fun j => hid (K j) (hKc j) ((hKA j).trans hAS)

/-- Local-domain comparison needs finite density mass, not a globally
bounded slope set or a fictitious convex extension through the boundary. -/
theorem alexandrovOn_comparison_of_strict_density {u v f g : E n → ℝ}
    (huc : Continuous u) (hvc : Continuous v) {S : Set (E n)} (hS : IsCompact S)
    (hb : ∀ y ∈ frontier S, v y ≤ u y)
    (hgm : Measurable g) (hfn : ∀ y ∈ interior S, 0 ≤ f y)
    (hfg : ∀ y ∈ interior S, f y < g y)
    (hfin : (volume.withDensity (fun y => ENNReal.ofReal (f y))) S ≠ ⊤)
    (huid : ∀ A : Set (E n), IsCompact A → A ⊆ interior S →
      volume (subgradientImageOn S u A) = (volume.withDensity (fun y => ENNReal.ofReal (f y))) A)
    (hvid : ∀ A : Set (E n), IsCompact A → A ⊆ interior S →
      volume (subgradientImageOn S v A) = (volume.withDensity (fun y => ENNReal.ofReal (g y))) A) :
    ∀ x ∈ S, v x ≤ u x := by
  intro x hx
  by_contra hxuv
  have hxuv : u x < v x := lt_of_not_ge hxuv
  have hxi : x ∈ interior S := by
    by_contra hxi
    exact hxuv.not_ge (hb x ⟨subset_closure hx, hxi⟩)
  let A : Set (E n) := interior S ∩ {y | u y < v y}
  have hA : IsOpen A := isOpen_interior.inter (isOpen_lt huc hvc)
  have hAS : A ⊆ interior S := inter_subset_left
  have hApos : 0 < volume A := hA.measure_pos volume ⟨x, hxi, hxuv⟩
  have hAu := alexandrovOn_identity_on_open_of_on_compact hS huid hA hAS
  have hAv := alexandrovOn_identity_on_open_of_on_compact hS hvid hA hAS
  have hfi : ∫⁻ y in A, ENNReal.ofReal (f y) ∂volume ≠ ⊤ := by
    rw [← withDensity_apply _ hA.measurableSet]
    exact ne_top_of_le_ne_top hfin (measure_mono (hAS.trans interior_subset))
  have hlt : (volume.withDensity (fun y => ENNReal.ofReal (f y))) A <
      (volume.withDensity (fun y => ENNReal.ofReal (g y))) A := by
    rw [withDensity_apply _ hA.measurableSet, withDensity_apply _ hA.measurableSet]
    apply setLIntegral_strict_mono hA.measurableSet hApos.ne' hgm.ennreal_ofReal hfi
    filter_upwards [] with y
    intro hy
    exact ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt (hfn y hy.1) (hfg y hy.1)) |>.mpr (hfg y hy.1)
  have hle := measure_mono (μ := volume) (subgradientImageOn_strict_sublevel_subset hS huc.continuousOn hb)
  change volume (subgradientImageOn S v A) ≤ volume (subgradientImageOn S u A) at hle
  rw [hAu, hAv] at hle
  exact hlt.not_ge hle

lemma supportsOn_pos_mul_add_const_iff (S : Set (E n)) {u : E n → ℝ} {t : ℝ} (ht : 0 < t)
    (b : ℝ) (p x : E n) :
    SupportsOn S (fun y => t * u y + b) (t • p) x ↔ SupportsOn S u p x := by
  constructor
  · intro h y hy
    have hh := h y hy
    simp only [real_inner_smul_left] at hh
    have he : t * (u x + inner ℝ p (y - x)) ≤ t * u y := by linarith
    exact (mul_le_mul_left ht).mp he
  · intro h y hy
    have hh := mul_le_mul_of_nonneg_left (h y hy) ht.le
    change t * u x + b + inner ℝ (t • p) (y - x) ≤ t * u y + b
    rw [real_inner_smul_left]
    linarith

theorem subgradientImageOn_pos_mul_add_const (S : Set (E n)) (u : E n → ℝ) {t : ℝ}
    (ht : 0 < t) (b : ℝ) (A : Set (E n)) :
    subgradientImageOn S (fun y => t * u y + b) A = (fun p => t • p) '' subgradientImageOn S u A := by
  ext p
  constructor
  · rintro ⟨x, hx, hs⟩
    have hp : t • (t⁻¹ • p) = p := by rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
    refine ⟨t⁻¹ • p, ⟨x, hx, ?_⟩, hp⟩
    apply (supportsOn_pos_mul_add_const_iff S ht b _ _).mp
    simpa only [hp] using hs
  · rintro ⟨q, ⟨x, hx, hs⟩, rfl⟩
    exact ⟨x, hx, (supportsOn_pos_mul_add_const_iff S ht b q x).mpr hs⟩

theorem volume_subgradientImageOn_pos_mul_add_const (S : Set (E n)) (u : E n → ℝ) {t : ℝ}
    (ht : 0 < t) (b : ℝ) (A : Set (E n)) :
    volume (subgradientImageOn S (fun y => t * u y + b) A) =
      ENNReal.ofReal (t ^ n) * volume (subgradientImageOn S u A) := by
  rw [subgradientImageOn_pos_mul_add_const S u ht b A]
  change volume (t • subgradientImageOn S u A) = _
  simpa [E, Reference.Space] using volume.addHaar_smul_of_nonneg ht.le (subgradientImageOn S u A)

/-- Non-strict positive-density comparison on a bounded domain. -/
theorem alexandrovOn_comparison_of_density_le [NeZero n] {u v f g : E n → ℝ}
    (huc : Continuous u) (hvc : Continuous v)
    {S : Set (E n)} (hS : IsCompact S)
    (hb : ∀ y ∈ frontier S, v y ≤ u y)
    (hgm : Measurable g) (hfn : ∀ y ∈ interior S, 0 ≤ f y)
    (hgp : ∀ y ∈ interior S, 0 < g y) (hfg : ∀ y ∈ interior S, f y ≤ g y)
    (hfin : (volume.withDensity (fun y => ENNReal.ofReal (f y))) S ≠ ⊤)
    (huid : ∀ A : Set (E n), IsCompact A → A ⊆ interior S →
      volume (subgradientImageOn S u A) = (volume.withDensity (fun y => ENNReal.ofReal (f y))) A)
    (hvid : ∀ A : Set (E n), IsCompact A → A ⊆ interior S →
      volume (subgradientImageOn S v A) = (volume.withDensity (fun y => ENNReal.ofReal (g y))) A) :
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
  have hwb : ∀ y ∈ frontier S, v y ≤ w y := by
    intro y hy
    have hyS : y ∈ S := hS.isClosed.closure_subset hy.1
    have hbound := hMu y hyS
    have hvu := hb y hy
    dsimp [w]
    nlinarith
  have htpow0 : 0 ≤ t ^ n := pow_nonneg ht.le _
  have htpow1 : t ^ n < 1 := pow_lt_one₀ ht.le ht1 (NeZero.ne n)
  have hwid : ∀ A : Set (E n), IsCompact A → A ⊆ interior S →
      volume (subgradientImageOn S w A) =
        (volume.withDensity (fun y => ENNReal.ofReal (t ^ n * f y))) A := by
    intro A hA hAS
    rw [show w = (fun y => t * u y + (1 - t) * M) from rfl,
      volume_subgradientImageOn_pos_mul_add_const S u ht _ A, huid A hA hAS]
    simp_rw [ENNReal.ofReal_mul htpow0]
    have hm := withDensity_smul' (μ := (volume : Measure (E n)))
      (ENNReal.ofReal (t ^ n)) (fun y => ENNReal.ofReal (f y)) ENNReal.ofReal_ne_top
    have ha := congrArg (fun μ : Measure (E n) => μ A) hm
    simpa only [Pi.smul_apply, smul_eq_mul, Measure.smul_apply] using ha.symm
  have hscaled : volume.withDensity (fun y => ENNReal.ofReal (t^n * f y)) =
      ENNReal.ofReal (t^n) • volume.withDensity (fun y => ENNReal.ofReal (f y)) := by
    simp_rw [ENNReal.ofReal_mul htpow0]
    exact withDensity_smul' _ _ ENNReal.ofReal_ne_top
  have hwfin : (volume.withDensity (fun y => ENNReal.ofReal (t^n * f y))) S ≠ ⊤ := by
    rw [hscaled, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  have hcmp := alexandrovOn_comparison_of_strict_density hwc hvc hS hwb hgm
    (fun y hy => mul_nonneg htpow0 (hfn y hy))
    (fun y hy => lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hfg y hy) htpow0)
      (by nlinarith [hgp y hy])) hwfin hwid hvid x hx
  exact htx.not_ge hcmp

end GaussianTilt.MomentMapRegularity
