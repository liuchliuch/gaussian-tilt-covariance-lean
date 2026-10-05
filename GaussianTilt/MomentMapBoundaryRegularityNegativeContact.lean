import GaussianTilt.MomentMapBoundaryRegularityABP

/-! # ABP restricted to negative lower contact points -/
noncomputable section
open MeasureTheory Matrix Filter Set
open scoped Topology BigOperators ContDiff Gradient ENNReal
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

def negativeLowerContactSet (S : Set (E n)) (u : E n → ℝ) : Set (E n) :=
  lowerContactSet S u ∩ {x | u x < 0}

lemma measurableSet_negativeLowerContactSet {S : Set (E n)} {u : E n → ℝ}
    (hu : ContDiff ℝ ∞ u) : MeasurableSet (negativeLowerContactSet S u) :=
  (measurableSet_lowerContactSet hu).inter
    (isOpen_lt hu.continuous continuous_const).measurableSet

lemma ball_subset_gradient_negativeLowerContactSet {S : Set (E n)} {u : E n → ℝ}
    (hS : IsCompact S) (hu : ContDiff ℝ ∞ u) {x : E n} (hx : x ∈ S)
    {D : ℝ} (hD : 0 < D) (hdiam : Metric.diam S ≤ D) (hneg : u x < 0)
    (hb : ∀ y ∈ frontier S, 0 ≤ u y) :
    Metric.ball 0 (-u x / (2 * D)) ⊆ gradient u '' negativeLowerContactSet S u := by
  intro p hp
  have hp' : ‖p‖ < -u x / (2 * D) := by simpa only [Metric.mem_ball, dist_zero_right] using hp
  have hpbig : p ∈ Metric.ball 0 (-u x / D) := by
    simp only [Metric.mem_ball, dist_zero_right]
    apply hp'.trans_le
    apply div_le_div_of_nonneg_left (neg_nonneg.mpr hneg.le) hD
    linarith
  obtain ⟨z, hz, hzp⟩ := ball_subset_gradient_lowerContactSet hS hu hx hD hdiam hneg hb hpbig
  refine ⟨z, ⟨hz, ?_⟩, hzp⟩
  change u z < 0
  have hs := hz.2 x hx
  rw [hzp] at hs
  have hd : ‖z-x‖ ≤ D := by
    rw [← dist_eq_norm]
    exact (Metric.dist_le_diam_of_mem hS.isBounded (interior_subset hz.1) hx).trans hdiam
  have hi : inner ℝ p (z-x) < -u x / 2 := by
    calc
      _ ≤ ‖p‖ * ‖z-x‖ := real_inner_le_norm _ _
      _ ≤ ‖p‖ * D := mul_le_mul_of_nonneg_left hd (norm_nonneg _)
      _ < (-u x / (2 * D)) * D := mul_lt_mul_of_pos_right hp' hD
      _ = -u x / 2 := by field_simp
  rw [inner_sub_right] at hs hi
  linarith

lemma gradient_contact_subset_volume_le {S C : Set (E n)} {u : E n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hC : MeasurableSet C) (hCS : C ⊆ lowerContactSet S u) :
    volume (gradient u '' C) ≤
      ∫⁻ x in C, ENNReal.ofReal (coordinateHessian (coordinatePullback u) (coordinateEquiv n x)).det := by
  have harea := addHaar_image_le_lintegral_abs_det_fderiv volume hC
    (fun x _ => ((contDiff_gradient_of_smooth hu).differentiable (by simp) x).hasFDerivAt.hasFDerivWithinAt)
  refine harea.trans_eq ?_
  apply setLIntegral_congr_fun hC
  intro x hx
  dsimp only
  rw [determinant_fderiv_gradient_eq_coordinateHessian hu,
    abs_of_nonneg (hessian_posSemidef_of_lower_contact hu (hCS hx)).det_nonneg]

/-- Quantitative negative-contact measure from actual bounded forcing.
This is the contact-measure engine for the critical-density lemma. -/
theorem smooth_abp_negative_contact_measure {S : Set (E n)} {u : E n → ℝ}
    (hS : IsCompact S) (hu : ContDiff ℝ ∞ u) {x : E n} (hx : x ∈ S)
    {D lam F : ℝ} (hD : 0 < D) (hdiam : Metric.diam S ≤ D) (hlam : 0 < lam)
    (hF : 0 ≤ F) (hneg : u x < 0) (hb : ∀ y ∈ frontier S, 0 ≤ u y)
    {A : E n → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ y ∈ negativeLowerContactSet S u, (A y - lam • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef)
    (hL : ∀ y ∈ negativeLowerContactSet S u,
      linearizedMA (A y) (coordinatePullback u) (coordinateEquiv n y) ≤ F) :
    volume (Metric.ball (0 : E n) (-u x / (2 * D))) ≤
      ENNReal.ofReal ((n.factorial : ℝ) * (F / lam)^n) * volume (negativeLowerContactSet S u) := by
  calc
    _ ≤ volume (gradient u '' negativeLowerContactSet S u) :=
      measure_mono (ball_subset_gradient_negativeLowerContactSet hS hu hx hD hdiam hneg hb)
    _ ≤ ∫⁻ y in negativeLowerContactSet S u,
        ENNReal.ofReal (coordinateHessian (coordinatePullback u) (coordinateEquiv n y)).det :=
      gradient_contact_subset_volume_le hu (measurableSet_negativeLowerContactSet hu) inter_subset_left
    _ ≤ ∫⁻ _y in negativeLowerContactSet S u,
        ENNReal.ofReal ((n.factorial : ℝ) * (F / lam)^n) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (measurableSet_negativeLowerContactSet hu)] with y hy
      apply ENNReal.ofReal_le_ofReal
      simpa only [max_eq_left hF] using contact_determinant_bound hlam (hA y hy)
        (hessian_posSemidef_of_lower_contact hu hy.1) (hL y hy)
    _ = _ := by simp

end GaussianTilt.MomentMapRegularity
