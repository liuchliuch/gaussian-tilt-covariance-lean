import GaussianTilt.MomentMapRegularityLocalizationSections

/-! # Exposed source contacts with an inward target tilt

Even a boundary-slope contact set has an exposed point. Compact tilted
source sections give a compact cap; a farthest-point construction with a
distant center places its exposed point strictly inside the cap. Convexity
extends the exposure globally, and the chosen direction enters the actual
open target. No Straszewicz or Caffarelli theorem is assumed.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators Gradient NNReal ENNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

lemma farthest_point_exposes {C : Set (E n)} {c x : E n}
    (hmax : ∀ y ∈ C, ‖y - c‖ ≤ ‖x - c‖) :
    ∀ y ∈ C, y ≠ x → inner ℝ (x - c) (y - x) < 0 := by
  intro y hy hne
  have hn := hmax y hy
  have hd : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hs := norm_sub_sq_real (y - c) (x - c)
  rw [show y - c - (x - c) = y - x by module] at hs
  have hi : inner ℝ (y - c) (x - c) = inner ℝ (x - c) (y - c) := real_inner_comm _ _
  rw [hi] at hs
  rw [show y - x = (y - c) - (x - c) by module, inner_sub_right,
    real_inner_self_eq_norm_sq]
  nlinarith [norm_nonneg (y - c), norm_nonneg (x - c), sq_pos_of_pos hd]

/-- Strict exposure of a relatively open piece of a convex set propagates
to the whole set by following a short segment from the exposed point. -/
lemma exposes_convex_of_exposes_local {C U : Set (E n)} (hC : Convex ℝ C)
    {x v : E n} (hx : x ∈ C) (hU : IsOpen U) (hxU : x ∈ U)
    (hv : ∀ y ∈ C ∩ U, y ≠ x → inner ℝ v (y - x) < 0) :
    ∀ y ∈ C, y ≠ x → inner ℝ v (y - x) < 0 := by
  intro y hy hne
  obtain ⟨δ, hδ, hδU⟩ := exists_small_tilt_mem_open hU hxU (y - x)
  let t : ℝ := min δ (1 / 2)
  have ht : 0 < t := lt_min hδ (by norm_num)
  have ht1 : t ≤ 1 := (min_le_right _ _).trans (by norm_num)
  let z := x + t • (y - x)
  have hzC : z ∈ C := by
    have hh := hC hx hy (sub_nonneg.mpr ht1) ht.le (by ring : (1 - t) + t = 1)
    convert hh using 1 <;> dsimp [z] <;> module
  have hzU : z ∈ U := hδU t ht.le (min_le_left _ _)
  have hzx : z ≠ x := by
    intro he
    have hz : t • (y - x) = 0 := by dsimp [z] at he; exact add_left_cancel (he.trans (add_zero x).symm)
    exact (smul_ne_zero ht.ne' (sub_ne_zero.mpr hne)) hz
  have hzv := hv z ⟨hzC, hzU⟩ hzx
  dsimp [z] at hzv
  rw [add_sub_cancel_left, inner_smul_right] at hzv
  nlinarith

/-- Every nonempty literal source contact set has an exposed point and a
positive tilt of its exposing direction lying inside K. This includes all
boundary supporting slopes and uses only the genuine moment law. -/
theorem contactSet_has_exposed_inward_tilt {φ V : E n → ℝ}
    (hφ : Continuous φ) (hc : ConvexOn ℝ univ φ)
    {K : Set (E n)} (hK : IsOpen K) (hV : ContinuousOn V K)
    (hmap : (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x)))).map
      (gradient φ) = volume.withDensity (fun x => ENNReal.ofReal
        (K.indicator (fun y => Real.exp (-V y)) x)))
    {q p : E n} (hq : q ∈ K) (hn : (contactSet φ p).Nonempty) :
    ∃ x ∈ contactSet φ p, ∃ v : E n, ∃ δ : ℝ, 0 < δ ∧ p + δ • v ∈ K ∧
      ∀ y ∈ contactSet φ p, y ≠ x → inner ℝ v (y - x) < 0 := by
  let F := fun y => φ y - inner ℝ q y
  have hF : Continuous F := hφ.sub (continuous_const.inner continuous_id)
  obtain ⟨x₀, hx₀⟩ := hn
  have hinitial : IsCompact (contactSet φ p ∩ {y | F y ≤ F x₀}) :=
    (compact_tilted_section_of_target_density hφ hc hK hV hmap hq (F x₀)).inter_left
      (isClosed_contactSet hφ p)
  obtain ⟨a, ha, hamin⟩ := hinitial.exists_isMinOn
    ⟨x₀, hx₀, show F x₀ ≤ F x₀ from le_rfl⟩ hF.continuousOn
  let B := contactSet φ p ∩ {y | F y ≤ F a + 1}
  have hB : IsCompact B :=
    (compact_tilted_section_of_target_density hφ hc hK hV hmap hq (F a + 1)).inter_left
      (isClosed_contactSet hφ p)
  have haB : a ∈ B := ⟨ha.1, by dsimp; linarith⟩
  obtain ⟨M, hM⟩ := hB.isBounded.exists_norm_le
  have hM0 : 0 ≤ M := (norm_nonneg a).trans (hM a haB)
  obtain ⟨r, hr, hrK⟩ := Metric.mem_nhds_iff.mp (hK.mem_nhds hq)
  let t := max (M ^ 2 + 1) (M / r + 1)
  have htM : M ^ 2 < t := lt_of_lt_of_le (lt_add_one _) (le_max_left _ _)
  have htr : M / r < t := lt_of_lt_of_le (lt_add_one _) (le_max_right _ _)
  have ht : 0 < t := lt_of_le_of_lt (sq_nonneg M) htM
  let c := t • (p - q)
  obtain ⟨x, hx, hxmax⟩ := hB.exists_isMaxOn ⟨a, haB⟩
    (continuous_id.sub continuous_const).norm.continuousOn
  have hxstrict : F x < F a + 1 := by
    by_contra hnot
    have he : F x = F a + 1 := le_antisymm hx.2 (le_of_not_gt hnot)
    have hlevel : φ x - inner ℝ p x = φ a - inner ℝ p a := by
      simpa only [contactSet_eq_level ha.1, mem_setOf_eq] using hx.1
    have hpx : inner ℝ (p - q) x - inner ℝ (p - q) a = 1 := by
      dsimp [F] at he
      rw [inner_sub_left, inner_sub_left]
      linarith
    have hnorm : ‖a - c‖ ≤ ‖x - c‖ := hxmax haB
    have hnormsq := pow_le_pow_left₀ (norm_nonneg (a - c)) hnorm 2
    have hs₁ := norm_sub_sq_real a c
    have hs₂ := norm_sub_sq_real x c
    have hac : inner ℝ a c = t * inner ℝ (p - q) a := by
      dsimp [c]
      rw [inner_smul_right, real_inner_comm]
    have hxc : inner ℝ x c = t * inner ℝ (p - q) x := by
      dsimp [c]
      rw [inner_smul_right, real_inner_comm]
    rw [hac] at hs₁
    rw [hxc] at hs₂
    have hMx := pow_le_pow_left₀ (norm_nonneg x) (hM x hx) 2
    nlinarith [sq_nonneg ‖a‖, congrArg (fun s : ℝ => t * s) hpx]
  have hexposes : ∀ y ∈ contactSet φ p, y ≠ x → inner ℝ (x - c) (y - x) < 0 := by
    apply exposes_convex_of_exposes_local (U := {y : E n | F y < F a + 1})
      (convex_contactSet hc p) hx.1
      (isOpen_lt hF continuous_const) hxstrict
    intro y hy hne
    exact farthest_point_exposes (C := B) (fun z hz => hxmax hz) y
      ⟨hy.1, (show F y < F a + 1 from hy.2).le⟩ hne
  have hqball : q + t⁻¹ • x ∈ Metric.ball q r := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
    calc
      t⁻¹ * ‖x‖ ≤ t⁻¹ * M := mul_le_mul_of_nonneg_left (hM x hx) (inv_nonneg.mpr ht.le)
      _ < r := by
        rw [inv_mul_lt_iff₀ ht]
        have hMr : M < t * r := (div_lt_iff₀ hr).mp htr
        simpa [mul_comm] using hMr
  refine ⟨x, hx.1, x - c, t⁻¹, inv_pos.mpr ht, ?_, hexposes⟩
  have he : p + t⁻¹ • (x - c) = q + t⁻¹ • x := by
    dsimp [c]
    rw [smul_sub, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
    module
  rw [he]
  exact hrK hqball

end GaussianTilt.MomentMapRegularity
