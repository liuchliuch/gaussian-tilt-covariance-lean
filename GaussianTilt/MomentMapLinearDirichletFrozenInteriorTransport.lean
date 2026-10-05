import GaussianTilt.MomentMapLinearDirichletFrozenExcessEnergy

/-! # Genuine full-ball affine excess transport at arbitrary centers -/
noncomputable section
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 1000
open MeasureTheory Set Filter
open scoped Topology BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma fieldExcess_translate (U : KernelSpace n → KernelSpace n) (a q : KernelSpace n) (r : ℝ) :
    fieldExcess (fun x => U (x+a)) (Metric.ball (0:KernelSpace n) r) q=fieldExcess U (Metric.ball a r) q := by
  have hμ := measurePreserving_add_right (volume : Measure (KernelSpace n)) a
  have he : (fun x : KernelSpace n => x+a) ⁻¹' Metric.ball a r=Metric.ball 0 r := by
    ext x
    simp only [mem_preimage,Metric.mem_ball,dist_eq_norm,add_sub_cancel_right,sub_zero]
  have hh := hμ.setIntegral_preimage_emb (Homeomorph.addRight a).measurableEmbedding
    (fun x => ‖U x-q‖^2) (Metric.ball a r)
  rw [he] at hh
  exact hh

lemma inverse_ball_subset (P : KernelSpace n ≃L[ℝ] KernelSpace n) {N r : ℝ}
    (hN : 0 < N) (hI : ‖P.symm.toContinuousLinearMap‖ ≤ N) :
    P ⁻¹' Metric.ball (0:KernelSpace n) r ⊆ Metric.ball 0 (N*r) := by
  intro z hz
  have hnorm := P.symm.toContinuousLinearMap.le_opNorm (P z)
  rw [ContinuousLinearEquiv.coe_coe,P.symm_apply_apply] at hnorm
  have hbound := hnorm.trans (mul_le_mul_of_nonneg_right hI (norm_nonneg _))
  have hzN : ‖P z‖ < r := by simpa only [mem_preimage,Metric.mem_ball,dist_zero_right] using hz
  change ‖z-0‖ < N*r
  rw [sub_zero]
  exact hbound.trans_lt (mul_lt_mul_of_pos_left hzN hN)

theorem affine_ball_excess_decay (P : KernelSpace n ≃L[ℝ] KernelSpace n)
    {M N R C : ℝ} (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hC : 0 ≤ C)
    (hP : ‖P.toContinuousLinearMap‖ ≤ M) (hI : ‖P.symm.toContinuousLinearMap‖ ≤ N)
    {U V : KernelSpace n → KernelSpace n} (hU : MemLp U 2 volume) (hV : MemLp V 2 volume)
    (hVU : ∀ᵐ z ∂volume, z ∈ Metric.ball (0:KernelSpace n) (R/M) → V z=boundaryDualMap P (U (P z)))
    {p : KernelSpace n}
    (hdec : ∀ q : KernelSpace n, ∀ t : ℝ, 0 < t → t ≤ (R/M)/2 →
      fieldExcess V (Metric.ball (0:KernelSpace n) t) p ≤ C*(t/(R/M))^(n+2)*fieldExcess V (Metric.ball (0:KernelSpace n) (R/M)) q) :
    ∀ q : KernelSpace n, ∀ r : ℝ, 0 < r → r ≤ R/(2*M*N) →
      fieldExcess U (Metric.ball (0:KernelSpace n) r) (boundaryDualMap P.symm p) ≤
        (C*M^2*N^2*(M*N)^(n+2))*(r/R)^(n+2)*fieldExcess U (Metric.ball (0:KernelSpace n) R) q := by
  let δ := |P.toContinuousLinearMap.det|
  have hδ : 0 < δ := physical_affine_det_pos P
  have hL : 0 < R/M := div_pos hR hM
  have hpmap : boundaryDualMap P (boundaryDualMap P.symm p)=p := by
    have hh := congrArg (fun T : KernelSpace n →L[ℝ] KernelSpace n => T p) (boundaryDualMap_inverse P.symm)
    simpa only [ContinuousLinearEquiv.symm_symm,ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] using hh
  intro q r hr hsmall
  have hNr : N*r ≤ (R/M)/2 := by
    have hh := (le_div_iff₀ (show 0 < 2*M*N by positivity)).mp hsmall
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    apply (le_div_iff₀ hM).mpr
    nlinarith
  have hpre := inverse_ball_subset P hN hI (r := r)
  have hpreball : P ⁻¹' Metric.ball (0:KernelSpace n) r ⊆ Metric.ball (0:KernelSpace n) (R/M) :=
    hpre.trans (Metric.ball_subset_ball (hNr.trans (by linarith)))
  have hidSmall := affine_fieldExcess_identity P hVU Metric.isOpen_ball.measurableSet hpreball (boundaryDualMap P.symm p)
  rw [hpmap] at hidSmall
  have hsmallE : fieldExcess U (Metric.ball (0:KernelSpace n) r) (boundaryDualMap P.symm p) ≤
      N^2*δ*fieldExcess V (Metric.ball (0:KernelSpace n) (N*r)) p := by
    have hh := (affine_transformed_excess_bounds P hM.le hN.le hP hI hU (S := Metric.ball (0:KernelSpace n) r)
      Metric.isOpen_ball.measurableSet measure_ball_lt_top (boundaryDualMap P.symm p)).2
    rw [hpmap,← hidSmall] at hh
    have hm := fieldExcess_mono_set hV measure_ball_lt_top hpre p
    exact hh.trans (by
      calc
        _ = (N^2*δ)*fieldExcess V (P ⁻¹' Metric.ball (0:KernelSpace n) r) p := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hm (mul_nonneg (sq_nonneg N) hδ.le))
  let Z := Metric.ball (0:KernelSpace n) (R/M)
  let S := P '' Z
  have hSm : MeasurableSet S := (P.toHomeomorph.isOpenMap Z Metric.isOpen_ball).measurableSet
  have hSsub : S ⊆ Metric.ball (0:KernelSpace n) R := by
    rintro x ⟨z,hz,rfl⟩
    have hh := (P.toContinuousLinearMap.le_opNorm z).trans (mul_le_mul_of_nonneg_right hP (norm_nonneg _))
    have hzN : ‖z‖ < R/M := by simpa only [Z,Metric.mem_ball,dist_zero_right] using hz
    have hm := (lt_div_iff₀ hM).mp hzN
    change ‖P z-0‖ < R
    rw [sub_zero]
    change ‖P z‖ ≤ M*‖z‖ at hh
    nlinarith only [hh,hm]
  have hpreS : P ⁻¹' S=Z := P.injective.preimage_image Z
  have hidBig := affine_fieldExcess_identity P hVU hSm (by rw [hpreS]) q
  rw [hpreS] at hidBig
  have hlargeE : δ*fieldExcess V Z (boundaryDualMap P q) ≤ M^2*fieldExcess U (Metric.ball (0:KernelSpace n) R) q := by
    rw [hidBig]
    have hTG := hU.continuousLinearMap_comp (boundaryDualMap P)
    have hm := fieldExcess_mono_set hTG measure_ball_lt_top hSsub (boundaryDualMap P q)
    exact hm.trans (affine_transformed_excess_bounds P hM.le hN.le hP hI hU (S := Metric.ball (0:KernelSpace n) R)
      Metric.isOpen_ball.measurableSet measure_ball_lt_top q).1
  have hd := hdec (boundaryDualMap P q) (N*r) (mul_pos hN hr) hNr
  calc
    fieldExcess U (Metric.ball (0:KernelSpace n) r) (boundaryDualMap P.symm p)
      ≤ N^2*δ*fieldExcess V (Metric.ball (0:KernelSpace n) (N*r)) p := hsmallE
    _ ≤ N^2*δ*(C*(N*r/(R/M))^(n+2)*fieldExcess V Z (boundaryDualMap P q)) :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    _ = (N^2*C*(N*r/(R/M))^(n+2))*(δ*fieldExcess V Z (boundaryDualMap P q)) := by ring
    _ ≤ (N^2*C*(N*r/(R/M))^(n+2))*(M^2*fieldExcess U (Metric.ball (0:KernelSpace n) R) q) :=
      mul_le_mul_of_nonneg_left hlargeE (by positivity)
    _ = _ := by
      have he : N*r/(R/M)=(M*N)*(r/R) := by field_simp
      rw [he,mul_pow]
      ring

end GaussianTilt.MomentMapLinearDirichlet
