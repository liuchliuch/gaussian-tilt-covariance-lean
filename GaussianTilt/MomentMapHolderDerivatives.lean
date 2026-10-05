import GaussianTilt.MomentMapHolderSegments

/-! # Actual derivatives from the closed FTC jet identities -/
noncomputable section
open Set Filter MeasureTheory Asymptotics
open scoped Topology BoundedContinuousFunction
namespace GaussianTilt.HolderSpace
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def extendValue {S : Set E} (α : ℝ) (f : Space S F α) (x : E) : F := by
  classical
  exact if hx : x ∈ S then value S F α f ⟨x, hx⟩ else 0

lemma extendValue_mem {S : Set E} (α : ℝ) (f : Space S F α) {x : E} (hx : x ∈ S) :
    extendValue α f x = value S F α f ⟨x, hx⟩ := by
  classical
  exact dif_pos hx

lemma continuousOn_extendValue {S : Set E} (α : ℝ) (f : Space S F α) :
    ContinuousOn (extendValue α f) S := by
  rw [continuousOn_iff_continuous_restrict]
  have he : S.restrict (extendValue α f) = value S F α f := by
    funext x
    exact extendValue_mem α f x.2
  rw [he]
  exact (value S F α f).continuous

/-- The FTC integral has a genuine higher-order remainder controlled by the
actual Hölder norm of its derivative field. -/
theorem segmentIntegral_remainder_norm {S : Set E} (hS : Convex ℝ S) {α : ℝ}
    (hα : 0 ≤ α) (D : Space S (E →L[ℝ] F) α) (x y : S) :
    ‖segmentIntegral hS α x y D - value S (E →L[ℝ] F) α D x ((y : E) - x)‖ ≤
      ‖D‖ * ‖(y : E) - x‖ ^ α * ‖(y : E) - x‖ := by
  have he : segmentIntegral hS α x y D - value S (E →L[ℝ] F) α D x ((y : E) - x) =
      ∫ t in (0 : ℝ)..1, (value S (E →L[ℝ] F) α D (segmentPoint hS x y t) -
        value S (E →L[ℝ] F) α D x) ((y : E) - x) := by
    simp only [ContinuousLinearMap.sub_apply]
    rw [intervalIntegral.integral_sub
      ((continuous_segmentIntegrand hS α D x y).intervalIntegrable 0 1)
      (intervalIntegrable_const)]
    simp only [intervalIntegral.integral_const, sub_zero, one_smul, segmentIntegral_apply]
  rw [he]
  have hbound : ∀ t ∈ uIoc (0 : ℝ) 1,
      ‖(value S (E →L[ℝ] F) α D (segmentPoint hS x y t) - value S (E →L[ℝ] F) α D x) ((y : E) - x)‖ ≤
        ‖D‖ * ‖(y : E) - x‖ ^ α * ‖(y : E) - x‖ := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by
      simp only [uIoc_of_le zero_le_one, mem_Ioc] at ht
      exact ⟨ht.1.le, ht.2⟩
    have hd : dist (segmentPoint hS x y t) x ≤ ‖(y : E) - x‖ := by
      rw [Subtype.dist_eq, dist_eq_norm, segmentPoint_eq hS x y ht', add_sub_cancel_left,
        norm_smul, Real.norm_eq_abs, abs_of_nonneg ht'.1]
      exact mul_le_of_le_one_left (norm_nonneg _) ht'.2
    have hH := norm_value_sub_le S (E →L[ℝ] F) α D (segmentPoint hS x y t) x
    have hpow := Real.rpow_le_rpow dist_nonneg hd hα
    exact ((value S (E →L[ℝ] F) α D (segmentPoint hS x y t) - value S (E →L[ℝ] F) α D x).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hH.trans (mul_le_mul_of_nonneg_left hpow (norm_nonneg D))) (norm_nonneg _))
  simpa only [sub_zero, abs_one, mul_one] using intervalIntegral.norm_integral_le_of_norm_le_const hbound

/-- FTC-compatible Hölder fields are the actual Fréchet derivatives in the
interior. A formal derivative field is not assumed to be a derivative. -/
theorem hasFDerivAt_extendValue_of_ftc {S : Set E} (hS : Convex ℝ S) {α : ℝ}
    (hα : 0 < α) (f : Space S F α) (D : Space S (E →L[ℝ] F) α)
    (hftc : ∀ x y : S, value S F α f y - value S F α f x = segmentIntegral hS α x y D)
    (x : S) (hx : (x : E) ∈ interior S) :
    HasFDerivAt (extendValue α f) (value S (E →L[ℝ] F) α D x) (x : E) := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff]
  intro ε hε
  have hc : Continuous (fun h : E => ‖D‖ * ‖h‖ ^ α) :=
    continuous_const.mul ((Real.continuous_rpow_const hα.le).comp continuous_norm)
  have hsmall : ∀ᶠ h : E in 𝓝 0, ‖D‖ * ‖h‖ ^ α < ε := by
    have he := (hc.continuousAt (x := 0)).eventually
      (gt_mem_nhds (show ‖D‖ * ‖(0 : E)‖ ^ α < ε by simpa [Real.zero_rpow hα.ne'] using hε))
    exact he
  have ht : Tendsto (fun h : E => (x : E) + h) (𝓝 0) (𝓝 (x : E)) := by
    simpa only [add_zero, id_eq] using ((continuous_const : Continuous (fun _ : E => (x : E))).add continuous_id).tendsto (0 : E)
  have hmem : ∀ᶠ h : E in 𝓝 0, (x : E) + h ∈ S := ht.eventually (mem_interior_iff_mem_nhds.mp hx)
  filter_upwards [hsmall, hmem] with h hh hSxh
  let y : S := ⟨(x : E) + h, hSxh⟩
  rw [extendValue_mem α f hSxh, extendValue_mem α f x.2]
  change ‖value S F α f y - value S F α f x - value S (E →L[ℝ] F) α D x h‖ ≤ ε * ‖h‖
  rw [hftc]
  have hv : (y : E) - x = h := by dsimp [y]; abel
  have hb := segmentIntegral_remainder_norm hS hα.le D x y
  rw [hv] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right hh.le (norm_nonneg h))

/-- The same genuine derivative statement holds within the closed domain,
including its boundary; no arbitrary extension derivative is used. -/
theorem hasFDerivWithinAt_extendValue_of_ftc {S : Set E} (hS : Convex ℝ S) {α : ℝ}
    (hα : 0 < α) (f : Space S F α) (D : Space S (E →L[ℝ] F) α)
    (hftc : ∀ x y : S, value S F α f y - value S F α f x = segmentIntegral hS α x y D)
    (x : S) :
    HasFDerivWithinAt (extendValue α f) (value S (E →L[ℝ] F) α D x) S (x : E) := by
  rw [HasFDerivWithinAt, hasFDerivAtFilter_iff_isLittleO, isLittleO_iff]
  intro ε hε
  have hc : Continuous (fun y : E => ‖D‖ * ‖y - (x : E)‖ ^ α) :=
    continuous_const.mul ((Real.continuous_rpow_const hα.le).comp ((continuous_id.sub continuous_const).norm))
  have hsmall : ∀ᶠ y : E in 𝓝 (x : E), ‖D‖ * ‖y - (x : E)‖ ^ α < ε := by
    have he := (hc.continuousAt (x := (x : E))).eventually
      (gt_mem_nhds (show ‖D‖ * ‖(x : E) - x‖ ^ α < ε by simpa [Real.zero_rpow hα.ne'] using hε))
    exact he
  filter_upwards [self_mem_nhdsWithin, hsmall.filter_mono nhdsWithin_le_nhds] with y hy hh
  rw [extendValue_mem α f hy, extendValue_mem α f x.2, hftc]
  have hb := segmentIntegral_remainder_norm hS hα.le D x ⟨y, hy⟩
  exact hb.trans (mul_le_mul_of_nonneg_right hh.le (norm_nonneg _))

end GaussianTilt.HolderSpace
