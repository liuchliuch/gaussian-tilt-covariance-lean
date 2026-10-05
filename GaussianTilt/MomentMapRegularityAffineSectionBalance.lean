import GaussianTilt.MomentMapRegularityInteriorDifferentiability
import GaussianTilt.MomentMapRegularityLocalizationConclusion

/-!
# Actual affine section balance and continuous differentiability

The affine normalization and literal Monge--Ampère volume covariance are
combined with the normalized Aleksandrov centering estimate. The resulting
reflection constant is uniform for all sections with the same density
bounds. Shrinking strict-convex sections then give actual C¹ regularity.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators Gradient NNReal ENNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

/-- The explicit outer radius supplied by the maximal determinant normalization. -/
def sectionNormalizationRadius (n : ℕ) : ℝ := 3 * ((n : ℝ) + 1) ^ 2

lemma sectionNormalizationRadius_pos (n : ℕ) : 0 < sectionNormalizationRadius n := by
  unfold sectionNormalizationRadius
  positivity

/-- An affine-invariant reflection factor depending only on dimension and
upper and lower local Alexandrov density bounds. -/
def sectionBalanceFactor (n : ℕ) (lam Lam : ℝ) : ℝ :=
  min (1 / 2) (lam / sectionCenterCoefficient n (sectionNormalizationRadius n) Lam /
    (2 * sectionNormalizationRadius n))

lemma sectionBalanceFactor_pos {lam Lam : ℝ} (hlam : 0 < lam) (hLam : 0 < Lam) :
    0 < sectionBalanceFactor n lam Lam := by
  unfold sectionBalanceFactor
  have hR := sectionNormalizationRadius_pos n
  have hC := sectionCenterCoefficient_pos (n := n) hR hLam
  exact lt_min (by norm_num) (div_pos (div_pos hlam hC) (by positivity))

lemma sectionBalanceFactor_le_half (n : ℕ) (lam Lam : ℝ) :
    sectionBalanceFactor n lam Lam ≤ 1 / 2 := min_le_left _ _

/-- Convexity survives the actual affine coordinate and supporting-plane change. -/
lemma convexOn_affinePotential {φ : E n → ℝ} (hc : ConvexOn ℝ univ φ)
    (T : E n ≃L[ℝ] E n) (a p : E n) (b : ℝ) :
    ConvexOn ℝ univ (affinePotential φ T a p b) := by
  exact convexOn_comp_affineSource
    ((alexandrov_convex_tilt hc p).sub (concaveOn_const b convex_univ)) T a

/-- Every actual compact section with two-sided local density bounds is
uniformly balanced around its supporting point. No smoothness or strict
convexity is assumed in this geometric statement. -/
theorem supportSection_reflection_balance [NeZero n] {φ : E n → ℝ}
    (hc : ConvexOn ℝ univ φ) {p x : E n} (hp : SupportsAt φ p x)
    {h lam Lam : ℝ} (hh : 0 < h) (hlam : 0 < lam) (hLam : 0 < Lam)
    (hS : IsCompact (supportSection φ p x h))
    (hmass : ∀ A : Set (E n), IsCompact A → A ⊆ supportSection φ p x h →
      ENNReal.ofReal lam * volume A ≤ volume (subgradientImage φ A) ∧
      volume (subgradientImage φ A) ≤ ENNReal.ofReal Lam * volume A) :
    ∀ y ∈ supportSection φ p x h,
      x - sectionBalanceFactor n lam Lam • (y - x) ∈ supportSection φ p x h := by
  let S := supportSection φ p x h
  have hφ : Continuous φ := continuousOn_univ.mp (hc.continuousOn isOpen_univ)
  have hSc : Convex ℝ S := convex_supportSection hc p x h
  have hxi : x ∈ interior S := center_mem_interior_supportSection hφ p x hh
  obtain ⟨a, T, hball, houter⟩ := exists_affine_normalization_explicit hS hSc ⟨x, hxi⟩
  let N := (fun y => T (y - a)) '' S
  let b := φ x - inner ℝ p x + h
  let u := affinePotential φ T a p b
  let x' := T (x - a)
  let R := sectionNormalizationRadius n
  have hR : 0 < R := sectionNormalizationRadius_pos n
  have hNc : IsCompact N := hS.image (T.continuous.comp (continuous_id.sub continuous_const))
  have hNcv : Convex ℝ N := by
    have ht := (hSc.translate (-a)).linear_image T.toLinearMap
    simpa only [image_image, Function.comp_def, neg_add_eq_sub] using ht
  have huc : ConvexOn ℝ univ u := convexOn_affinePotential hc T a p b
  have hcontu : Continuous u := continuousOn_univ.mp (huc.continuousOn isOpen_univ)
  have hpre : N = affineSource T a ⁻¹' S := forward_image_eq_affineSource_preimage T a S
  have huval (y : E n) : u y = supportResidual φ p x (affineSource T a y) - h := by
    dsimp [u, affinePotential, b, supportResidual]
    rw [inner_sub_right]
    ring
  have hvalue : u x' = -h := by
    rw [huval]
    simp [x', affineSource, supportResidual_self]
  have hNsublevel : N = {y | u y ≤ 0} := by
    rw [hpre]
    ext y
    rw [mem_preimage, mem_setOf_eq, huval]
    change supportResidual φ p x (affineSource T a y) ≤ h ↔
      supportResidual φ p x (affineSource T a y) - h ≤ 0
    constructor <;> intro hh <;> linarith
  have hNx : x' ∈ interior N := by
    have hop : IsOpenMap (fun y : E n => T (y - a)) := T.isOpenMap.comp (isOpenMap_sub_right a)
    exact hop.image_interior_subset S ⟨x, hxi, rfl⟩
  have hbound : ∀ y ∈ N, -h ≤ u y ∧ u y ≤ 0 := by
    intro y hy
    have hyS : affineSource T a y ∈ S := by rwa [hpre] at hy
    have hlo := supportResidual_nonneg hp (affineSource T a y)
    change supportResidual φ p x (affineSource T a y) ≤ h at hyS
    rw [huval]
    constructor <;> linarith
  have hboundary : ∀ y ∈ frontier N, 0 ≤ u y := by
    rw [hNsublevel]
    intro y hy
    exact (frontier_le_subset_eq hcontu continuous_const hy).ge
  let d := |LinearMap.det T.symm.toLinearEquiv.toLinearMap|
  let q := d ^ 2
  have hd : 0 < d := abs_pos.mpr T.symm.toLinearEquiv.isUnit_det'.ne_zero
  have hq : 0 < q := sq_pos_of_pos hd
  have hden (A : Set (E n)) (hA : IsCompact A) (hAN : A ⊆ N) :
      ENNReal.ofReal (q * lam) * volume A ≤ volume (subgradientImage u A) ∧
      volume (subgradientImage u A) ≤ ENNReal.ofReal (q * Lam) * volume A := by
    have hIA : IsCompact (affineSource T a '' A) := hA.image (T.symm.continuous.add continuous_const)
    have hIAS : affineSource T a '' A ⊆ S := by
      rintro _ ⟨y, hy, rfl⟩
      have hh := hAN hy
      rwa [hpre] at hh
    have h := subgradientImage_affine_density_bounds φ T a p b A
      (hmass _ hIA hIAS).1 (hmass _ hIA hIAS).2
    have he (r : ℝ) : ENNReal.ofReal (q * r) = affineJacobian T ^ 2 * ENNReal.ofReal r := by
      rw [ENNReal.ofReal_mul hq.le, ENNReal.ofReal_pow hd.le]
      rfl
    rw [he lam, he Lam]
    exact h
  have hmassL := (hden (Metric.closedBall (0 : E n) (1 / 2)) (isCompact_closedBall _ _)
    ((Metric.closedBall_subset_closedBall (by norm_num)).trans hball)).1
  have hmassU := (hden N hNc Subset.rfl).2
  have hcenter := normalized_section_contains_center_ball huc hNc hNcv hball hR houter hNx
    hh hq hlam hLam hvalue hbound hboundary hmassL hmassU
  have hθ : 0 ≤ sectionBalanceFactor n lam Lam := (sectionBalanceFactor_pos hlam hLam).le
  have hθρ : sectionBalanceFactor n lam Lam * (2 * R) ≤
      lam / sectionCenterCoefficient n R Lam := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * R)).mp
    exact min_le_right _ _
  intro y hy
  have hmem := reflected_contraction_mem_of_center_ball hR hθ hθρ houter hcenter
    (interior_subset hNx) (show T (y - a) ∈ N from ⟨y, hy, rfl⟩)
  change x' - sectionBalanceFactor n lam Lam • (T (y - a) - x') ∈ N at hmem
  rw [hpre] at hmem
  change affineSource T a (x' - sectionBalanceFactor n lam Lam • (T (y - a) - x')) ∈ S at hmem
  have heq : affineSource T a (x' - sectionBalanceFactor n lam Lam • (T (y - a) - x')) =
      x - sectionBalanceFactor n lam Lam • (y - x) := by
    dsimp [affineSource, x']
    simp only [map_sub, map_smul, T.symm_apply_apply]
    module
  rwa [heq] at hmem

/-- A single pair of density bounds on an ambient set controls every compact
section inside it, with exactly the same reflection factor. -/
theorem supportSection_reflection_balance_of_subset [NeZero n] {φ : E n → ℝ}
    (hc : ConvexOn ℝ univ φ) {p x : E n} (hp : SupportsAt φ p x)
    {h lam Lam : ℝ} (hh : 0 < h) (hlam : 0 < lam) (hLam : 0 < Lam)
    (hS : IsCompact (supportSection φ p x h)) {B : Set (E n)}
    (hSB : supportSection φ p x h ⊆ B)
    (hmass : ∀ A : Set (E n), IsCompact A → A ⊆ B →
      ENNReal.ofReal lam * volume A ≤ volume (subgradientImage φ A) ∧
      volume (subgradientImage φ A) ≤ ENNReal.ofReal Lam * volume A) :
    ∀ y ∈ supportSection φ p x h,
      x - sectionBalanceFactor n lam Lam • (y - x) ∈ supportSection φ p x h :=
  supportSection_reflection_balance hc hp hh hlam hLam hS
    (fun A hA hAS => hmass A hA (hAS.trans hSB))

/-- Small sections around a fixed support enjoy a positive, height-independent
reflection factor supplied by local density bounds on one fixed ball. -/
theorem small_supportSection_reflection_balance [NeZero n] {φ : E n → ℝ}
    (hc : StrictConvexOn ℝ univ φ) {p x : E n} (hp : SupportsAt φ p x)
    {r lam Lam : ℝ} (hr : 0 < r) (hlam : 0 < lam) (hLam : 0 < Lam)
    (hmass : ∀ A : Set (E n), IsCompact A → A ⊆ Metric.closedBall x r →
      ENNReal.ofReal lam * volume A ≤ volume (subgradientImage φ A) ∧
      volume (subgradientImage φ A) ≤ ENNReal.ofReal Lam * volume A) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h < h₀ →
      ∀ y ∈ supportSection φ p x h,
        x - sectionBalanceFactor n lam Lam • (y - x) ∈ supportSection φ p x h := by
  obtain ⟨h₀, hh₀, hsmall⟩ := small_supportSection_subset_ball hc hp hr
  refine ⟨h₀, hh₀, ?_⟩
  intro h hh hhh₀
  exact supportSection_reflection_balance_of_subset hc.convexOn hp hh hlam hLam
    (isCompact_supportSection_of_strictConvexOn hc hp h)
    ((hsmall h hhh₀).trans Metric.ball_subset_closedBall) hmass

/-- Local compact-set Alexandrov density bounds imply actual C¹ regularity
for a globally Lipschitz strictly convex potential. The proof goes through
real section normalization and singleton supporting fibers. -/
theorem contDiff_one_of_local_subgradientImage_bounds {φ : E n → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L φ) (hc : StrictConvexOn ℝ univ φ)
    (hmass : ∀ B : Set (E n), IsCompact B →
      ∃ lam Lam : ℝ, 0 < lam ∧ 0 < Lam ∧
        ∀ A : Set (E n), IsCompact A → A ⊆ B →
          ENNReal.ofReal lam * volume A ≤ volume (subgradientImage φ A) ∧
          volume (subgradientImage φ A) ≤ ENNReal.ofReal Lam * volume A) :
    ContDiff ℝ 1 φ := by
  by_cases hn : n = 0
  · subst n
    have he : φ = fun _ => φ 0 := funext (fun x => congrArg φ (Subsingleton.elim x 0))
    rw [he]
    exact contDiff_const
  haveI : NeZero n := ⟨hn⟩
  apply contDiff_one_of_lipschitz_convex_differentiable hL hc.convexOn
  intro x
  apply differentiableAt_of_local_section_balance hL hc.convexOn x
  intro p hp
  obtain ⟨lam, Lam, hlam, hLam, hbound⟩ :=
    hmass (Metric.closedBall x 1) (isCompact_closedBall x 1)
  obtain ⟨h₀, hh₀, hbal⟩ := small_supportSection_reflection_balance hc hp
    (by norm_num : (0 : ℝ) < 1) hlam hLam hbound
  exact ⟨sectionBalanceFactor n lam Lam, h₀, sectionBalanceFactor_pos hlam hLam, hh₀, hbal⟩

/-- A genuine moment source for a bounded convex target with continuous
positive density is continuously differentiable. Strict convexity and
Alexandrov density bounds are derived from the actual transport identity;
no classical Monge--Ampère equation or regularity theorem is assumed. -/
theorem contDiff_one_of_target_density {φ V : E n → ℝ}
    {L : ℝ≥0} (hL : LipschitzWith L φ) (hc : ConvexOn ℝ univ φ)
    {K : Set (E n)} (hK : IsOpen K) (hKc : Convex ℝ K)
    (hKb : Bornology.IsBounded K) (hV : ContinuousOn V (closure K))
    (hmap : (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x)))).map
      (gradient φ) = volume.withDensity (fun x => ENNReal.ofReal
        (K.indicator (fun y => Real.exp (-V y)) x))) :
    ContDiff ℝ 1 φ := by
  apply contDiff_one_of_local_subgradientImage_bounds hL
    (strictConvexOn_of_target_density hL hc hK hKc hKb hV hmap)
  intro B hB
  exact local_subgradientImage_volume_bounds hL hc hK hKc hKb hV hmap hB

end GaussianTilt.MomentMapRegularity
