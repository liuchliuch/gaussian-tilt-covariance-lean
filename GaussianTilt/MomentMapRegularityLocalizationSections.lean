import GaussianTilt.MomentMapRegularityLocalizationDensity

/-!
# Tilted contact sections and exposed-point localization geometry

The positive-height sections obtained by tilting a supporting plane are
constructed explicitly. Compactness gives their convergence to the clipped
contact set, including quantitative confinement near an exposed contact
point. These lemmas precede the Alexandrov maximum-principle contradiction.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators Gradient NNReal ENNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

/-- A Euclidean farthest point of a compact set is exposed by its own
position vector. Convexity is not required for this existence statement. -/
theorem exists_exposed_point_of_isCompact {C : Set (E n)}
    (hC : IsCompact C) (hCn : C.Nonempty) :
    ∃ x ∈ C, ∀ y ∈ C, y ≠ x → inner ℝ x (y - x) < 0 := by
  obtain ⟨x, hx, hmax⟩ := hC.exists_isMaxOn hCn continuous_norm.continuousOn
  refine ⟨x, hx, ?_⟩
  intro y hy hne
  have hn : ‖y‖ ≤ ‖x‖ := hmax hy
  have hd : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hs := norm_sub_sq_real y x
  have hi : inner ℝ y x = inner ℝ x y := real_inner_comm _ _
  rw [inner_sub_right, real_inner_self_eq_norm_sq]
  rw [hi] at hs
  nlinarith [norm_nonneg y, norm_nonneg x, sq_pos_of_pos hd]

/-- Clipping by a linear functional exposing a compact set localizes the
remaining cap in any prescribed neighborhood of its exposed point. -/
theorem exists_exposed_cap_subset {C : Set (E n)} (hC : IsCompact C)
    {x v : E n} (_hx : x ∈ C)
    (hv : ∀ y ∈ C, y ≠ x → inner ℝ v (y - x) < 0)
    {U : Set (E n)} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ a : ℝ, 0 < a ∧ {y | y ∈ C ∧ -a ≤ inner ℝ v (y - x)} ⊆ U := by
  let D := C \ U
  have hD : IsCompact D := hC.inter_right hU.isClosed_compl
  by_cases hn : D.Nonempty
  · have hh : Continuous (fun y : E n => inner ℝ v (y - x)) :=
      continuous_const.inner (continuous_id.sub continuous_const)
    obtain ⟨y, hy, hmax⟩ := hD.exists_isMaxOn hn hh.continuousOn
    have hne : y ≠ x := by intro he; subst y; exact hy.2 hxU
    have hneg := hv y hy.1 hne
    refine ⟨-inner ℝ v (y - x) / 2, by linarith, ?_⟩
    intro z hz
    by_contra hzU
    have hle := hmax (show z ∈ D from ⟨hz.1, hzU⟩)
    dsimp at hle
    linarith [hz.2]
  · refine ⟨1, by norm_num, ?_⟩
    intro z hz
    by_contra hzU
    exact hn ⟨z, hz.1, hzU⟩

/-- Pure compactness localization for tilted sublevels. No PDE estimate is
hidden here: outside the limiting clipped zero set, the continuous residual
has a strictly positive minimum on a fixed compact section. -/
theorem small_tilt_sublevel_subset {F G : E n → ℝ}
    (hF : Continuous F) (hG : Continuous G) (hFnonneg : ∀ x, 0 ≤ F x)
    {δ : ℝ} (hδ : 0 < δ) (hS : IsCompact {x | F x ≤ δ * G x})
    {U : Set (E n)} (hU : IsOpen U)
    (hzero : {x | F x = 0 ∧ 0 ≤ G x} ⊆ U) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      {x | F x ≤ ε * G x} ⊆ U := by
  have hsubset {ε : ℝ} (hε : 0 < ε) (hεδ : ε ≤ δ) :
      {x | F x ≤ ε * G x} ⊆ {x | F x ≤ δ * G x} := by
    intro x hx
    have hg : 0 ≤ G x := by
      change F x ≤ ε * G x at hx
      nlinarith [hFnonneg x]
    exact hx.trans (mul_le_mul_of_nonneg_right hεδ hg)
  let D := {x | F x ≤ δ * G x} \ U
  have hD : IsCompact D := hS.inter_right hU.isClosed_compl
  by_cases hn : D.Nonempty
  · obtain ⟨z, hz, hmin⟩ := hD.exists_isMinOn hn hF.continuousOn
    have hzpos : 0 < F z := by
      by_contra hnz
      have he : F z = 0 := le_antisymm (le_of_not_gt hnz) (hFnonneg z)
      have hgz : 0 ≤ G z := by
        have hs := hz.1
        change F z ≤ δ * G z at hs
        nlinarith
      exact hz.2 (hzero ⟨he, hgz⟩)
    obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn hG.continuousOn
    let H := |M| + 1
    have hH : 0 < H := by dsimp [H]; positivity
    refine ⟨min δ (F z / H), lt_min hδ (div_pos hzpos hH), ?_⟩
    intro ε hε hε₀ x hx
    have hxS := hsubset hε (lt_of_lt_of_le hε₀ (min_le_left _ _)).le hx
    by_contra hxU
    have hminx : F z ≤ F x := hmin ⟨hxS, hxU⟩
    have hgH : G x ≤ H := by
      have hb := hM x hxS
      rw [Real.norm_eq_abs] at hb
      dsimp [H]
      linarith [le_abs_self (G x), le_abs_self M]
    have hεH : ε * H < F z := (lt_div_iff₀ hH).mp
      (lt_of_lt_of_le hε₀ (min_le_right _ _))
    have hle := mul_le_mul_of_nonneg_left hgH hε.le
    change F x ≤ ε * G x at hx
    linarith
  · refine ⟨δ, hδ, ?_⟩
    intro ε hε hεδ x hx
    by_contra hxU
    exact hn ⟨x, hsubset hε hεδ.le hx, hxU⟩

/-- A positive-height section obtained by tilting a literal supporting
plane by ε v and raising it by ε a. -/
def tiltedContactSection (φ : E n → ℝ) (p x v : E n) (a ε : ℝ) : Set (E n) :=
  {y | φ y - φ x - inner ℝ p (y - x) ≤ ε * (inner ℝ v (y - x) + a)}

lemma tiltedContactSection_eq_tilted_sublevel (φ : E n → ℝ)
    (p x v : E n) (a ε : ℝ) :
    tiltedContactSection φ p x v a ε =
      {y | φ y - inner ℝ (p + ε • v) y ≤
        φ x - inner ℝ p x + ε * (a - inner ℝ v x)} := by
  ext y
  simp only [tiltedContactSection, mem_setOf_eq, inner_sub_right,
    inner_add_left, real_inner_smul_left]
  constructor <;> intro h <;> nlinarith

lemma center_mem_interior_tiltedContactSection {φ : E n → ℝ}
    (hφ : Continuous φ) (p x v : E n) {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) :
    x ∈ interior (tiltedContactSection φ p x v a ε) := by
  apply mem_interior.mpr
  refine ⟨{y | φ y - φ x - inner ℝ p (y - x) < ε * (inner ℝ v (y - x) + a)}, ?_, ?_, ?_⟩
  · intro y hy
    change φ y - φ x - inner ℝ p (y - x) ≤ ε * (inner ℝ v (y - x) + a)
    exact le_of_lt hy
  · exact isOpen_lt ((hφ.sub continuous_const).sub
      (continuous_const.inner (continuous_id.sub continuous_const)))
      (continuous_const.mul ((continuous_const.inner
        (continuous_id.sub continuous_const)).add continuous_const))
  · simp only [mem_setOf_eq, sub_self, inner_zero_right, zero_add]
    positivity

/-- Genuine moment sections at sufficiently small tilts converge into every
open neighborhood of their clipped contact set. Compactness is derived from
the actual transport law at one nearby interior slope. -/
theorem small_tiltedContactSection_subset_of_target_density {φ V : E n → ℝ}
    (hφ : Continuous φ) (hc : ConvexOn ℝ univ φ)
    {K : Set (E n)} (hK : IsOpen K) (hV : ContinuousOn V K)
    (hmap : (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x)))).map
      (gradient φ) = volume.withDensity (fun x => ENNReal.ofReal
        (K.indicator (fun y => Real.exp (-V y)) x)))
    {p x v : E n} (hx : SupportsAt φ p x) {a δ : ℝ}
    (hδ : 0 < δ) (hpδ : p + δ • v ∈ K)
    {U : Set (E n)} (hU : IsOpen U)
    (hcap : {y | y ∈ contactSet φ p ∧ -a ≤ inner ℝ v (y - x)} ⊆ U) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      tiltedContactSection φ p x v a ε ⊆ U := by
  apply small_tilt_sublevel_subset
    ((hφ.sub continuous_const).sub (continuous_const.inner (continuous_id.sub continuous_const)))
    ((continuous_const.inner (continuous_id.sub continuous_const)).add continuous_const)
    (fun y => by
      change 0 ≤ φ y - φ x - inner ℝ p (y - x)
      have h := hx y
      linarith) hδ
  · change IsCompact (tiltedContactSection φ p x v a δ)
    rw [tiltedContactSection_eq_tilted_sublevel]
    exact compact_tilted_section_of_target_density hφ hc hK hV hmap hpδ _
  · exact hU
  · intro y hy
    change φ y - φ x - inner ℝ p (y - x) = 0 ∧ 0 ≤ inner ℝ v (y - x) + a at hy
    apply hcap
    constructor
    · rw [contactSet_eq_level hx]
      change φ y - inner ℝ p y = φ x - inner ℝ p x
      have he := hy.1
      simp only [inner_sub_right] at he
      linarith
    · linarith [hy.2]

lemma exists_small_tilt_mem_open {K : Set (E n)} (hK : IsOpen K)
    {p : E n} (hp : p ∈ K) (v : E n) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ δ → p + ε • v ∈ K := by
  have hc : Continuous (fun ε : ℝ => p + ε • v) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have h0 : (0 : ℝ) ∈ (fun ε : ℝ => p + ε • v) ⁻¹' K := by simpa using hp
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp ((hK.preimage hc).mem_nhds h0)
  refine ⟨R / 2, by positivity, ?_⟩
  intro ε hε hεδ
  apply hball
  simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hε]
  linarith

/-- Arbitrarily small sections can be cut around an exposed interior-slope
contact point. All compactness and interior assertions are genuine
consequences of the original moment transport. -/
theorem localized_tilted_sections_of_exposed_contact {φ V : E n → ℝ}
    (hφ : Continuous φ) (hc : ConvexOn ℝ univ φ)
    {K : Set (E n)} (hK : IsOpen K) (hV : ContinuousOn V K)
    (hmap : (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x)))).map
      (gradient φ) = volume.withDensity (fun x => ENNReal.ofReal
        (K.indicator (fun y => Real.exp (-V y)) x)))
    {p x v : E n} (hp : p ∈ K) (hx : SupportsAt φ p x)
    (hv : ∀ y ∈ contactSet φ p, y ≠ x → inner ℝ v (y - x) < 0)
    {U : Set (E n)} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ a ε₀ : ℝ, 0 < a ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      IsCompact (tiltedContactSection φ p x v a ε) ∧
      x ∈ interior (tiltedContactSection φ p x v a ε) ∧
      tiltedContactSection φ p x v a ε ⊆ U := by
  obtain ⟨a, ha, hcap⟩ := exists_exposed_cap_subset
    (isCompact_contactSet_of_target_density hφ hc hK hV hmap hp) hx hv hU hxU
  obtain ⟨δ, hδ, hδK⟩ := exists_small_tilt_mem_open hK hp v
  obtain ⟨η, hη, hηU⟩ := small_tiltedContactSection_subset_of_target_density
    hφ hc hK hV hmap hx hδ (hδK δ hδ.le le_rfl) hU hcap
  refine ⟨a, min δ η, ha, lt_min hδ hη, ?_⟩
  intro ε hε hε₀
  refine ⟨?_, center_mem_interior_tiltedContactSection hφ p x v ha hε,
    hηU ε hε (lt_of_lt_of_le hε₀ (min_le_right _ _))⟩
  rw [tiltedContactSection_eq_tilted_sublevel]
  exact compact_tilted_section_of_target_density hφ hc hK hV hmap
    (hδK ε hε.le (lt_of_lt_of_le hε₀ (min_le_left _ _)).le) _

/-- The tilted sections approach the supporting hyperplane of their contact
set from above, while remaining on the prescribed lower side. This is the
slab-collapse geometry used in the localization contradiction. -/
theorem tilted_sections_eventually_in_thin_slab {φ V : E n → ℝ}
    (hφ : Continuous φ) (hc : ConvexOn ℝ univ φ)
    {K : Set (E n)} (hK : IsOpen K) (hV : ContinuousOn V K)
    (hmap : (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x)))).map
      (gradient φ) = volume.withDensity (fun x => ENNReal.ofReal
        (K.indicator (fun y => Real.exp (-V y)) x)))
    {p x v : E n} (hx : SupportsAt φ p x)
    (hv : ∀ y ∈ contactSet φ p, inner ℝ v (y - x) ≤ 0)
    {a δ b : ℝ} (hδ : 0 < δ) (hpδ : p + δ • v ∈ K) (hb : 0 < b) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ y ∈ tiltedContactSection φ p x v a ε,
        -a ≤ inner ℝ v (y - x) ∧ inner ℝ v (y - x) < b ∧
        -ε * (a + b) < φ y - φ x - inner ℝ p (y - x) -
          ε * (inner ℝ v (y - x) + a) := by
  have hU : IsOpen {y : E n | inner ℝ v (y - x) < b} :=
    isOpen_lt (continuous_const.inner (continuous_id.sub continuous_const)) continuous_const
  obtain ⟨ε₀, hε₀, hsub⟩ := small_tiltedContactSection_subset_of_target_density
    hφ hc hK hV hmap hx hδ hpδ hU
    (fun y hy => (hv y hy.1).trans_lt hb)
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε hεsmall y hy
  have hyb : inner ℝ v (y - x) < b := hsub ε hε hεsmall hy
  have hsupport := hx y
  change φ y - φ x - inner ℝ p (y - x) ≤ ε * (inner ℝ v (y - x) + a) at hy
  refine ⟨?_, hyb, ?_⟩ <;> nlinarith

/-- The explicit convex function cut off by a tilted contact section. -/
def tiltedContactPotential (φ : E n → ℝ) (p x v : E n) (a ε : ℝ) (y : E n) : ℝ :=
  φ y - φ x - inner ℝ p (y - x) - ε * (inner ℝ v (y - x) + a)

lemma tiltedContactPotential_eq (φ : E n → ℝ) (p x v : E n) (a ε : ℝ) (y : E n) :
    tiltedContactPotential φ p x v a ε y =
      (φ y - inner ℝ (p + ε • v) y) -
        (φ x - inner ℝ p x + ε * (a - inner ℝ v x)) := by
  simp only [tiltedContactPotential, inner_sub_right, inner_add_left, real_inner_smul_left]
  ring

lemma convexOn_tiltedContactPotential {φ : E n → ℝ} (hc : ConvexOn ℝ univ φ)
    (p x v : E n) (a ε : ℝ) :
    ConvexOn ℝ univ (tiltedContactPotential φ p x v a ε) := by
  have he : tiltedContactPotential φ p x v a ε = fun y =>
      (φ y - inner ℝ (p + ε • v) y) -
        (φ x - inner ℝ p x + ε * (a - inner ℝ v x)) := by
    funext y
    exact tiltedContactPotential_eq φ p x v a ε y
  rw [he]
  exact (hc.sub ((innerSL ℝ (p + ε • v)).toLinearMap.concaveOn convex_univ)).sub (concaveOn_const _ convex_univ)

lemma continuous_tiltedContactPotential {φ : E n → ℝ} (hφ : Continuous φ)
    (p x v : E n) (a ε : ℝ) : Continuous (tiltedContactPotential φ p x v a ε) := by
  unfold tiltedContactPotential
  exact ((hφ.sub continuous_const).sub
    (continuous_const.inner (continuous_id.sub continuous_const))).sub
    (continuous_const.mul ((continuous_const.inner
      (continuous_id.sub continuous_const)).add continuous_const))

lemma tiltedContactSection_eq_potential_sublevel (φ : E n → ℝ)
    (p x v : E n) (a ε : ℝ) :
    tiltedContactSection φ p x v a ε = {y | tiltedContactPotential φ p x v a ε y ≤ 0} := by
  ext y
  simp only [tiltedContactSection, tiltedContactPotential, mem_setOf_eq, sub_nonpos]

lemma convex_tiltedContactSection {φ : E n → ℝ} (hc : ConvexOn ℝ univ φ)
    (p x v : E n) (a ε : ℝ) : Convex ℝ (tiltedContactSection φ p x v a ε) := by
  rw [tiltedContactSection_eq_potential_sublevel]
  simpa only [mem_univ, true_and] using (convexOn_tiltedContactPotential hc p x v a ε).convex_le 0

lemma tiltedContactPotential_eq_zero_on_frontier {φ : E n → ℝ}
    (hφ : Continuous φ) (p x v : E n) (a ε : ℝ) :
    ∀ y ∈ frontier (tiltedContactSection φ p x v a ε),
      tiltedContactPotential φ p x v a ε y = 0 := by
  rw [tiltedContactSection_eq_potential_sublevel]
  exact frontier_le_subset_eq (continuous_tiltedContactPotential hφ p x v a ε) continuous_const

lemma tiltedContactPotential_center (φ : E n → ℝ) (p x v : E n) (a ε : ℝ) :
    tiltedContactPotential φ p x v a ε x = -ε * a := by
  simp [tiltedContactPotential, neg_mul]

lemma tiltedContactSection_mono {φ : E n → ℝ} {p x v : E n}
    (hx : SupportsAt φ p x) (a : ℝ) {ε δ : ℝ} (hε : 0 < ε) (hεδ : ε ≤ δ) :
    tiltedContactSection φ p x v a ε ⊆ tiltedContactSection φ p x v a δ := by
  intro y hy
  have hs := hx y
  change φ y - φ x - inner ℝ p (y - x) ≤ ε * (inner ℝ v (y - x) + a) at hy
  have hg : 0 ≤ inner ℝ v (y - x) + a := by nlinarith
  exact hy.trans (mul_le_mul_of_nonneg_right hεδ hg)

/-- A nontrivial contact segment provides a fixed lower-side point in all
the tilted sections, at exactly the chosen negative functional height. -/
theorem exists_contact_at_linear_height {φ : E n → ℝ}
    (hc : ConvexOn ℝ univ φ) {p x y v : E n}
    (hx : SupportsAt φ p x) (hy : SupportsAt φ p y)
    {a : ℝ} (ha : 0 < a) (hyv : inner ℝ v (y - x) < -a) :
    ∃ z ∈ contactSet φ p, inner ℝ v (z - x) = -a ∧
      ∀ ε : ℝ, z ∈ tiltedContactSection φ p x v a ε ∧
        tiltedContactPotential φ p x v a ε z = 0 := by
  let s := a / (-inner ℝ v (y - x))
  have hden : 0 < -inner ℝ v (y - x) := by linarith
  have hs : 0 < s := div_pos ha hden
  have hs1 : s < 1 := by apply (div_lt_one hden).mpr; linarith
  let z := (1 - s) • x + s • y
  have hz : z ∈ contactSet φ p := (convex_contactSet hc p) hx hy
    (sub_nonneg.mpr hs1.le) hs.le (by ring)
  have hdiff : z - x = s • (y - x) := by dsimp [z]; module
  have hvz : inner ℝ v (z - x) = -a := by
    rw [hdiff, inner_smul_right]
    dsimp [s]
    field_simp [(neg_pos.mp hden).ne]
    <;> ring
  have hFz : φ z - φ x - inner ℝ p (z - x) = 0 := by
    have hl : φ z - inner ℝ p z = φ x - inner ℝ p x := by
      simpa only [contactSet_eq_level hx, mem_setOf_eq] using hz
    rw [inner_sub_right]
    linarith
  refine ⟨z, hz, hvz, ?_⟩
  intro ε
  constructor
  · change φ z - φ x - inner ℝ p (z - x) ≤ ε * (inner ℝ v (z - x) + a)
    rw [hFz, hvz]
    simp
  · dsimp [tiltedContactPotential]
    rw [hFz, hvz]
    ring

end GaussianTilt.MomentMapRegularity
