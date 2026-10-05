import GaussianTilt.MomentMapRegularityDirichlet

/-! # Genuine convex Lipschitz extensions from bounded domains

The extension is a finite infimal convolution over the original compact
convex domain. Its local agreement is derived from boundedness and an
interior ball, rather than from an assumed extension or supporting plane.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

def convexLipschitzExtension (S : Set (E n)) (u : E n → ℝ) (L : ℝ≥0) (x : E n) : ℝ :=
  sInf ((fun y => u y + (L : ℝ) * ‖x-y‖) '' S)

lemma convexLipschitzExtension_attained {S : Set (E n)} (hS : IsCompact S)
    (hSn : S.Nonempty) {u : E n → ℝ} (hu : ContinuousOn u S) (L : ℝ≥0) (x : E n) :
    ∃ y ∈ S, convexLipschitzExtension S u L x = u y + (L : ℝ) * ‖x-y‖ ∧
      ∀ z ∈ S, u y + (L : ℝ) * ‖x-y‖ ≤ u z + (L : ℝ) * ‖x-z‖ := by
  have hcont : ContinuousOn (fun y => u y+(L : ℝ)*‖x-y‖) S :=
    hu.add (continuous_const.mul (continuous_const.sub continuous_id).norm).continuousOn
  obtain ⟨y, hy, hm⟩ := hS.exists_isMinOn hSn hcont
  refine ⟨y, hy, ?_, hm⟩
  apply le_antisymm
  · apply csInf_le
    · exact ⟨_, by rintro _ ⟨z,hz,rfl⟩; exact hm hz⟩
    · exact ⟨y,hy,rfl⟩
  · apply le_csInf (hSn.image _)
    rintro _ ⟨z,hz,rfl⟩
    exact hm hz

lemma convexLipschitzExtension_le {S : Set (E n)} (hS : IsCompact S)
    {u : E n → ℝ} (hu : ContinuousOn u S) (L : ℝ≥0) (x : E n)
    {y : E n} (hy : y ∈ S) :
    convexLipschitzExtension S u L x ≤ u y+(L : ℝ)*‖x-y‖ := by
  obtain ⟨z,hz,he,hm⟩ := convexLipschitzExtension_attained hS ⟨y,hy⟩ hu L x
  rw [he]
  exact hm y hy

lemma convexLipschitzExtension_le_on {S : Set (E n)} (hS : IsCompact S)
    {u : E n → ℝ} (hu : ContinuousOn u S) (L : ℝ≥0) {x : E n} (hx : x ∈ S) :
    convexLipschitzExtension S u L x ≤ u x := by
  simpa using convexLipschitzExtension_le hS hu L x hx

lemma convexLipschitzExtension_lipschitz {S : Set (E n)} (hS : IsCompact S)
    (hSn : S.Nonempty) {u : E n → ℝ} (hu : ContinuousOn u S) (L : ℝ≥0) :
    LipschitzWith L (convexLipschitzExtension S u L) := by
  apply LipschitzWith.of_le_add_mul
  intro x z
  obtain ⟨y,hy,he,hm⟩ := convexLipschitzExtension_attained hS hSn hu L z
  have hh := convexLipschitzExtension_le hS hu L x hy
  rw [he, dist_eq_norm]
  have ht : ‖x-y‖ ≤ ‖x-z‖+‖z-y‖ := by simpa only [dist_eq_norm] using dist_triangle x z y
  have ht' := mul_le_mul_of_nonneg_left ht L.coe_nonneg
  linarith

lemma convexLipschitzExtension_convex {S : Set (E n)} (hS : IsCompact S)
    (hSn : S.Nonempty) {u : E n → ℝ} (hu : ContinuousOn u S)
    (hc : ConvexOn ℝ S u) (L : ℝ≥0) :
    ConvexOn ℝ univ (convexLipschitzExtension S u L) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  obtain ⟨p,hp,hep,_⟩ := convexLipschitzExtension_attained hS hSn hu L x
  obtain ⟨q,hq,heq,_⟩ := convexLipschitzExtension_attained hS hSn hu L y
  have hh := convexLipschitzExtension_le hS hu L (a • x+b • y) (hc.1 hp hq ha hb hab)
  have hcu := hc.2 hp hq ha hb hab
  have hnorm : ‖a • x+b • y-(a • p+b • q)‖ ≤ a*‖x-p‖+b*‖y-q‖ := by
    rw [show a • x+b • y-(a • p+b • q) = a • (x-p)+b • (y-q) by module]
    exact (norm_add_le _ _).trans_eq (by rw [norm_smul, norm_smul,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb])
  have hnorm' := mul_le_mul_of_nonneg_left hnorm L.coe_nonneg
  rw [hep, heq]
  simp only [smul_eq_mul] at hcu ⊢
  nlinarith

/-- An interior ball and a bound on the function control the descending
slope from the interior point to every point of the convex domain. -/
lemma convexOn_descending_slope_bound {S : Set (E n)} {u : E n → ℝ}
    (hc : ConvexOn ℝ S u) {x : E n} {r M : ℝ} (hr : 0 < r)
    (hM : 0 ≤ M) (hb : Metric.closedBall x r ⊆ S)
    (hu : ∀ y ∈ S, |u y| ≤ M) (y : E n) (hy : y ∈ S) :
    u x ≤ u y + (2*M/r)*‖x-y‖ := by
  by_cases hxy : x = y
  · simp [hxy]
  have hd : 0 < ‖x-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  let d := ‖x-y‖
  let z := x+(r/d) • (x-y)
  have hz : z ∈ S := by
    apply hb
    rw [Metric.mem_closedBall, dist_eq_norm]
    dsimp [z]
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hr hd)]
    exact le_of_eq (div_mul_cancel₀ r hd.ne')
  have hx : x ∈ S := hb (Metric.mem_closedBall_self hr.le)
  have hden : 0 < r+d := add_pos hr hd
  have ha : 0 ≤ r/(r+d) := (div_pos hr hden).le
  have hb' : 0 ≤ d/(r+d) := (div_pos hd hden).le
  have hab : r/(r+d)+d/(r+d) = 1 := by rw [← add_div, div_self hden.ne']
  have hd0 : d ≠ 0 := hd.ne'
  have he : (r/(r+d)) • y+(d/(r+d)) • z = x := by
    have h1 : d/(r+d)+(d/(r+d))*(r/d) = 1 := by field_simp [hd0, hden.ne']; ring
    have h2 : r/(r+d)-(d/(r+d))*(r/d) = 0 := by field_simp [hd0, hden.ne']; ring
    calc
      _ = (d/(r+d)+(d/(r+d))*(r/d)) • x +
          (r/(r+d)-(d/(r+d))*(r/d)) • y := by dsimp [z]; module
      _ = x := by rw [h1, h2]; simp
  have hh := hc.2 hy hz ha hb' hab
  rw [he] at hh
  simp only [smul_eq_mul] at hh
  have hh' : (r+d)*u x ≤ r*u y+d*u z := by
    rw [mul_comm]
    apply (le_div_iff₀ hden).mp
    convert hh using 1 <;> ring
  have hxbound := (abs_le.mp (hu x hx)).1
  have hzbound := (abs_le.mp (hu z hz)).2
  have hmain : r*(u x-u y) ≤ 2*M*d := by nlinarith
  have hquot : u x-u y ≤ (2*M*d)/r := (le_div_iff₀ hr).mpr (by nlinarith)
  change u x ≤ u y+(2*M/r)*d
  have heq : (2*M*d)/r = (2*M/r)*d := by ring
  rw [heq] at hquot
  linarith

lemma convexLipschitzExtension_eq_of_interior_ball {S : Set (E n)}
    (hS : IsCompact S) {u : E n → ℝ} (hu : ContinuousOn u S)
    (hc : ConvexOn ℝ S u) {x : E n} {r M : ℝ} (hr : 0 < r)
    (hM : 0 ≤ M) (hb : Metric.closedBall x r ⊆ S)
    (hub : ∀ y ∈ S, |u y| ≤ M) :
    convexLipschitzExtension S u (2*M/r).toNNReal x = u x := by
  have hx := hb (Metric.mem_closedBall_self hr.le)
  apply le_antisymm (convexLipschitzExtension_le_on hS hu _ hx)
  obtain ⟨y,hy,he,_⟩ := convexLipschitzExtension_attained hS ⟨x,hx⟩ hu (2*M/r).toNNReal x
  rw [he, Real.toNNReal_of_nonneg (show 0 ≤ 2*M/r from by positivity)]
  exact convexOn_descending_slope_bound hc hr hM hb hub y hy

lemma supportsOn_iff_supportsAt_of_local_extension {S : Set (E n)}
    {u V : E n → ℝ} (hc : ConvexOn ℝ univ V) {x p : E n}
    (hx : x ∈ interior S) (heq : V =ᶠ[𝓝 x] u)
    (hle : ∀ y ∈ S, V y ≤ u y) :
    SupportsOn S u p x ↔ SupportsAt V p x := by
  have hex : V x = u x := heq.self_of_nhds
  constructor
  · intro hp
    have hm : IsLocalMin (fun y => V y-inner ℝ p y) x := by
      filter_upwards [mem_interior_iff_mem_nhds.mp hx, heq] with y hy hey
      have hh := hp y hy
      rw [inner_sub_right] at hh
      change V x-inner ℝ p x ≤ V y-inner ℝ p y
      rw [hex, hey]
      linarith
    have hg := IsMinOn.of_isLocalMin_of_convex_univ hm (alexandrov_convex_tilt hc p)
    intro y
    have hh := hg y
    rw [inner_sub_right]
    linarith
  · intro hp y hy
    have hh := hp y
    rw [hex] at hh
    exact hh.trans (hle y hy)

/-- A bounded-domain convex potential has a genuine globally finite convex
Lipschitz extension agreeing on a neighborhood of any compact interior set.
Its literal global subgradient image is the original local-domain image. -/
theorem exists_local_convex_lipschitz_extension {S A : Set (E n)}
    (hS : IsCompact S) (hSn : S.Nonempty) {u : E n → ℝ}
    (hu : ContinuousOn u S) (hc : ConvexOn ℝ S u)
    (hA : IsCompact A) (hAS : A ⊆ interior S) :
    ∃ (V : E n → ℝ) (L : ℝ≥0), LipschitzWith L V ∧ ConvexOn ℝ univ V ∧
      (∀ x ∈ A, V =ᶠ[𝓝 x] u) ∧ (∀ x ∈ S, V x ≤ u x) ∧
      (∀ B ⊆ A, subgradientImage V B = subgradientImageOn S u B) := by
  obtain ⟨δ,hδ,hδS⟩ := hA.exists_cthickening_subset_open isOpen_interior hAS
  let K := Metric.cthickening δ A
  have hK : IsCompact K := hA.cthickening
  have hKS : K ⊆ interior S := hδS
  obtain ⟨r,hr,hrS⟩ := hK.exists_cthickening_subset_open isOpen_interior hKS
  obtain ⟨M,hM⟩ := hS.exists_bound_of_continuousOn hu
  let M' := max M 0
  have hMb : ∀ y ∈ S, |u y| ≤ M' := fun y hy =>
    (hM y hy).trans (le_max_left _ _)
  let L := (2*M'/r).toNNReal
  let V := convexLipschitzExtension S u L
  have hVL : LipschitzWith L V := convexLipschitzExtension_lipschitz hS hSn hu L
  have hVc : ConvexOn ℝ univ V := convexLipschitzExtension_convex hS hSn hu hc L
  have heq (x : E n) (hx : x ∈ K) : V x = u x :=
    convexLipschitzExtension_eq_of_interior_ball hS hu hc hr (le_max_right _ _)
      (((Metric.closedBall_subset_cthickening hx r).trans hrS).trans interior_subset) hMb
  have hlocal (x : E n) (hx : x ∈ A) : V =ᶠ[𝓝 x] u := by
    have hn : K ∈ 𝓝 x := mem_of_superset
      (Metric.isOpen_thickening.mem_nhds (Metric.self_subset_thickening hδ A hx))
      (Metric.thickening_subset_cthickening δ A)
    filter_upwards [hn] with y hy
    exact heq y hy
  have hle : ∀ x ∈ S, V x ≤ u x := fun x hx => convexLipschitzExtension_le_on hS hu L hx
  refine ⟨V,L,hVL,hVc,hlocal,hle,?_⟩
  intro B hBA
  ext p
  constructor
  · rintro ⟨x,hx,hp⟩
    exact ⟨x,hx,(supportsOn_iff_supportsAt_of_local_extension hVc
      (hAS (hBA hx)) (hlocal x (hBA hx)) hle).mpr hp⟩
  · rintro ⟨x,hx,hp⟩
    exact ⟨x,hx,(supportsOn_iff_supportsAt_of_local_extension hVc
      (hAS (hBA hx)) (hlocal x (hBA hx)) hle).mp hp⟩

end GaussianTilt.MomentMapRegularity
