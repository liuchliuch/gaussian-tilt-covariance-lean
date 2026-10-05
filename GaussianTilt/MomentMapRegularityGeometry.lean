import Mathlib
import GaussianTilt.Reference.PaperStatements
import GaussianTilt.MomentMapFrechetDifferentiability

/-!
# Compact tilted sections of a genuine moment potential

The argument here is prior to elliptic regularity. Positivity of the target
measure on its open support and the actual gradient pushforward force every
interior target slope to have compact source sections. No smoothness or
strict convexity of the source is assumed.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators Gradient
namespace GaussianTilt.MomentMapRegularity

abbrev E (n : ℕ) := Reference.Space n
variable {n : ℕ}

/-- A tangent plane at a differentiability point of a finite convex function
is a global supporting plane. The proof uses the scalar convex slope bound. -/
theorem convex_gradient_support {φ : E n → ℝ} (hc : ConvexOn ℝ univ φ)
    {x : E n} (hx : DifferentiableAt ℝ φ x) (y : E n) :
    φ x + inner ℝ (gradient φ x) (y - x) ≤ φ y := by
  let F : ℝ → ℝ := fun t => φ (x + t • (y - x))
  have hFc : ConvexOn ℝ univ F := by
    refine ⟨convex_univ, ?_⟩
    intro a _ b _ s t hs ht hst
    have h := hc.2 (mem_univ (x + a • (y - x)))
      (mem_univ (x + b • (y - x))) hs ht hst
    have he : s • (x + a • (y - x)) + t • (x + b • (y - x)) =
        x + (s * a + t * b) • (y - x) := by
      rw [smul_add, smul_add, smul_smul, smul_smul]
      rw [show s • x + (s * a) • (y - x) + (t • x + (t * b) • (y - x)) =
        (s + t) • x + (s * a + t * b) • (y - x) by module, hst, one_smul]
    rw [he] at h
    exact h
  have hl : HasDerivAt (fun t : ℝ => x + t • (y - x)) (y - x) 0 := by
    simpa using (hasDerivAt_const (0 : ℝ) x).fun_add ((hasDerivAt_id (0 : ℝ)).smul_const (y - x))
  have hd : HasDerivAt F (inner ℝ (gradient φ x) (y - x)) 0 := by
    have hx' : HasFDerivAt φ ((InnerProductSpace.toDual ℝ (E n)) (gradient φ x))
        (x + (0 : ℝ) • (y - x)) := by simpa using hx.hasGradientAt.hasFDerivAt
    have h := hx'.comp_hasDerivAt 0 hl
    simpa [F, InnerProductSpace.toDual_apply] using h
  have h := hFc.le_slope_of_hasDerivAt (mem_univ 0) (mem_univ 1) (by norm_num) hd
  have h' : inner ℝ (gradient φ x) (y - x) ≤ φ y - φ x := by
    simpa [F, slope_def_field] using h
  linarith

/-- Compactness of the unit sphere turns strict supporting slopes in every
direction into a uniform linear coercivity estimate. -/
theorem linear_lower_bound_of_directional_support {φ : E n → ℝ}
    (hc : ConvexOn ℝ univ φ) (p : E n) {r : ℝ}
    (hdir : ∀ v : E n, ‖v‖ = 1 → ∃ x : E n,
      DifferentiableAt ℝ φ x ∧ r < inner ℝ (gradient φ x - p) v) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y, r * ‖y‖ - B ≤ φ y - inner ℝ p y := by
  classical
  let D := {x : E n // DifferentiableAt ℝ φ x}
  let U : D → Set (E n) := fun x => {v | r < inner ℝ (gradient φ x.val - p) v}
  have hU : ∀ x, IsOpen (U x) := fun x =>
    isOpen_lt continuous_const (continuous_const.inner continuous_id)
  have hcover : Metric.sphere (0 : E n) 1 ⊆ ⋃ x, U x := by
    intro v hv
    have hv' : ‖v‖ = 1 := by simpa using hv
    obtain ⟨x, hx, hxr⟩ := hdir v hv'
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxr⟩
  obtain ⟨s, hs⟩ := (isCompact_sphere (0 : E n) 1).elim_finite_subcover U hU hcover
  let B := |φ 0| + ∑ x ∈ s, |φ x.val - inner ℝ (gradient φ x.val) x.val|
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro y
  by_cases hy : y = 0
  · subst y
    simp only [norm_zero, mul_zero, inner_zero_right, sub_zero, zero_sub]
    have hb : |φ 0| ≤ B := by
      dsimp [B]
      exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
    linarith [neg_abs_le (φ 0)]
  have hyn : 0 < ‖y‖ := norm_pos_iff.mpr hy
  let v := ‖y‖⁻¹ • y
  have hv : ‖v‖ = 1 := by
    simp [v, norm_smul, hyn.ne']
  have hvs : v ∈ Metric.sphere (0 : E n) 1 := by simpa using hv
  obtain ⟨x, hxs⟩ := mem_iUnion.mp (hs hvs)
  obtain ⟨hxmem, hxr⟩ := mem_iUnion.mp hxs
  have hxB : |φ x.val - inner ℝ (gradient φ x.val) x.val| ≤ B := by
    calc
      _ ≤ ∑ z ∈ s, |φ z.val - inner ℝ (gradient φ z.val) z.val| :=
        Finset.single_le_sum (fun _ _ => abs_nonneg _) hxmem
      _ ≤ B := by dsimp [B]; exact le_add_of_nonneg_left (abs_nonneg _)
  have hplane := convex_gradient_support hc x.property y
  rw [inner_sub_right] at hplane
  have hyv : ‖y‖ • v = y := by simp [v, smul_smul, hyn.ne']
  have hinner : r * ‖y‖ ≤ inner ℝ (gradient φ x.val - p) y := by
    rw [← hyv, inner_smul_right, norm_smul, hv, mul_one, norm_norm]
    exact le_of_lt (by simpa [mul_comm] using mul_lt_mul_of_pos_left hxr hyn)
  rw [inner_sub_left] at hinner
  linarith [neg_abs_le (φ x.val - inner ℝ (gradient φ x.val) x.val)]

/-- Transport to a measure charging every target ball supplies actual
supporting gradients in all directions around an interior target point. -/
theorem directional_support_of_gradient_transport {φ : E n → ℝ}
    {ν μ : Measure (E n)} {K : Set (E n)}
    (hg : AEMeasurable (gradient φ) ν)
    (hd : ∀ᵐ x ∂ν, DifferentiableAt ℝ φ x)
    (hmap : ν.map (gradient φ) = μ)
    (hpos : ∀ q ∈ K, ∀ ε > 0, 0 < μ (Metric.ball q ε))
    {p : E n} {r : ℝ} (hr : 0 < r) (hball : Metric.ball p (3 * r) ⊆ K) :
    ∀ v : E n, ‖v‖ = 1 → ∃ x : E n,
      DifferentiableAt ℝ φ x ∧ r < inner ℝ (gradient φ x - p) v := by
  intro v hv
  let q := p + (2 * r) • v
  have hq : q ∈ K := by
    apply hball
    rw [Metric.mem_ball, dist_eq_norm]
    dsimp [q]
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), hv, mul_one]
    linarith
  have hmass : ν (gradient φ ⁻¹' Metric.ball q r) ≠ 0 := by
    rw [← Measure.map_apply_of_aemeasurable hg Metric.isOpen_ball.measurableSet, hmap]
    exact (hpos q hq r hr).ne'
  obtain ⟨x, hx, hdx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hmass
    (ae_restrict_of_ae hd)
  refine ⟨x, hdx, ?_⟩
  have hxnorm : ‖gradient φ x - q‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hx
  have hi := abs_real_inner_le_norm (gradient φ x - q) v
  rw [hv, mul_one] at hi
  have hlow := (neg_abs_le (inner ℝ (gradient φ x - q) v)).trans (le_refl _)
  have hid : inner ℝ (gradient φ x - p) v = inner ℝ (gradient φ x - q) v + 2 * r := by
    have he : gradient φ x - p = (gradient φ x - q) + (2 * r) • v := by dsimp [q]; module
    rw [he, inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq, hv]
    simp
  rw [hid]
  linarith

/-- Every interior target slope of an actual a.e.-differentiable convex
transport potential has a uniform linear growth gap at infinity. -/
theorem tilted_linear_lower_bound_of_gradient_transport {φ : E n → ℝ}
    (hc : ConvexOn ℝ univ φ) {ν μ : Measure (E n)} {K : Set (E n)}
    (hK : IsOpen K) (hg : AEMeasurable (gradient φ) ν)
    (hd : ∀ᵐ x ∂ν, DifferentiableAt ℝ φ x)
    (hmap : ν.map (gradient φ) = μ)
    (hpos : ∀ q ∈ K, ∀ ε > 0, 0 < μ (Metric.ball q ε))
    {p : E n} (hp : p ∈ K) :
    ∃ r B : ℝ, 0 < r ∧ 0 ≤ B ∧ ∀ y, r * ‖y‖ - B ≤ φ y - inner ℝ p y := by
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp (hK.mem_nhds hp)
  have hr : 0 < R / 3 := by positivity
  have hb : Metric.ball p (3 * (R / 3)) ⊆ K := by
    rw [show 3 * (R / 3) = R by ring]
    exact hball
  obtain ⟨B, hB, hgrowth⟩ := linear_lower_bound_of_directional_support hc p
    (directional_support_of_gradient_transport hg hd hmap hpos hr hb)
  exact ⟨R / 3, B, hr, hB, hgrowth⟩

/-- The sections needed for interior Monge--Ampère regularity are genuinely
compact, as a consequence of the source law and the target support. -/
theorem compact_tilted_section_of_gradient_transport {φ : E n → ℝ}
    (hφ : Continuous φ) (hc : ConvexOn ℝ univ φ)
    {ν μ : Measure (E n)} {K : Set (E n)}
    (hK : IsOpen K) (hg : AEMeasurable (gradient φ) ν)
    (hd : ∀ᵐ x ∂ν, DifferentiableAt ℝ φ x)
    (hmap : ν.map (gradient φ) = μ)
    (hpos : ∀ q ∈ K, ∀ ε > 0, 0 < μ (Metric.ball q ε))
    {p : E n} (hp : p ∈ K) (a : ℝ) :
    IsCompact {y | φ y - inner ℝ p y ≤ a} := by
  obtain ⟨r, B, hr, _, hbound⟩ :=
    tilted_linear_lower_bound_of_gradient_transport hc hK hg hd hmap hpos hp
  apply Metric.isCompact_of_isClosed_isBounded
    (isClosed_le (hφ.sub (continuous_const.inner continuous_id)) continuous_const)
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨(a + B) / r, ?_⟩
  intro y hy
  apply (le_div_iff₀ hr).mpr
  have h := hbound y
  change φ y - inner ℝ p y ≤ a at hy
  nlinarith

/-- Every ball centered in the open target support has positive mass for
the literal density exp(-V)1_K. V need only be continuous on K. -/
theorem target_ball_pos {K : Set (E n)} (hK : IsOpen K) {V : E n → ℝ}
    (hV : ContinuousOn V K) {q : E n} (hq : q ∈ K) {ε : ℝ} (hε : 0 < ε) :
    0 < (volume.withDensity (fun x => ENNReal.ofReal
      (K.indicator (fun y => Real.exp (-V y)) x))) (Metric.ball q ε) := by
  classical
  have hm : Measurable (K.indicator (fun y => Real.exp (-V y))) :=
    (Real.continuous_exp.comp_continuousOn hV.neg).measurable_piecewise
      continuousOn_const hK.measurableSet
  have he : {x | ENNReal.ofReal (K.indicator (fun y => Real.exp (-V y)) x) ≠ 0} = K := by
    ext x
    by_cases hx : x ∈ K
    · simp [hx, Real.exp_pos]
    · simp [hx]
  apply pos_iff_ne_zero.mpr
  intro hz
  have hm' : Measurable (fun x => ENNReal.ofReal (K.indicator (fun y => Real.exp (-V y)) x)) :=
    ENNReal.measurable_ofReal.comp hm
  have hz' := (withDensity_apply_eq_zero (μ := volume) hm').mp hz
  rw [he] at hz'
  exact ((hK.inter Metric.isOpen_ball).measure_pos volume
    ⟨q, hq, Metric.mem_ball_self hε⟩).ne' hz'

/-- Existence of every interior subgradient is obtained by minimizing a
compact tilted section, rather than postulated as a transport property. -/
theorem interior_target_subgradient {φ : E n → ℝ}
    (hφ : Continuous φ) (hc : ConvexOn ℝ univ φ)
    {ν μ : Measure (E n)} {K : Set (E n)}
    (hK : IsOpen K) (hg : AEMeasurable (gradient φ) ν)
    (hd : ∀ᵐ x ∂ν, DifferentiableAt ℝ φ x)
    (hmap : ν.map (gradient φ) = μ)
    (hpos : ∀ q ∈ K, ∀ ε > 0, 0 < μ (Metric.ball q ε))
    {p : E n} (hp : p ∈ K) :
    ∃ x : E n, ∀ y, φ x + inner ℝ p (y - x) ≤ φ y := by
  let F := fun y => φ y - inner ℝ p y
  have hFc : Continuous F := hφ.sub (continuous_const.inner continuous_id)
  have hcompact : IsCompact {y | F y ≤ F 0} :=
    compact_tilted_section_of_gradient_transport hφ hc hK hg hd hmap hpos hp (F 0)
  obtain ⟨x, hx, hmin⟩ := hcompact.exists_isMinOn ⟨0, show F 0 ≤ F 0 from le_rfl⟩ hFc.continuousOn
  refine ⟨x, fun y => ?_⟩
  have hxy : F x ≤ F y := by
    by_cases hy : F y ≤ F 0
    · exact hmin hy
    · exact hx.trans (le_of_not_ge hy)
  dsimp [F] at hxy
  rw [inner_sub_right]
  linarith

/-- The literal moment measure with the regular target density has compact
sections at every slope in K. Only a.e. source differentiation is needed. -/
theorem compact_tilted_section_of_target_density {φ V : E n → ℝ}
    (hφ : Continuous φ) (hc : ConvexOn ℝ univ φ) {K : Set (E n)}
    (hK : IsOpen K) (hV : ContinuousOn V K)
    (hmap : (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x)))).map
      (gradient φ) = volume.withDensity (fun x => ENNReal.ofReal
        (K.indicator (fun y => Real.exp (-V y)) x)))
    {p : E n} (hp : p ∈ K) (a : ℝ) :
    IsCompact {y | φ y - inner ℝ p y ≤ a} := by
  have hg : Measurable (gradient φ) :=
    (InnerProductSpace.toDual ℝ (E n)).symm.continuous.measurable.comp (measurable_fderiv ℝ φ)
  exact compact_tilted_section_of_gradient_transport hφ hc hK hg.aemeasurable
    ((withDensity_absolutelyContinuous volume _).ae_le
      (MomentMapCoercivity.convex_ae_differentiable hc)) hmap
    (fun q hq ε hε => target_ball_pos hK hV hq hε) hp a

end GaussianTilt.MomentMapRegularity
