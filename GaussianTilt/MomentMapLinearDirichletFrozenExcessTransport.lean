import GaussianTilt.MomentMapLinearDirichletFrozenExcessEnergy

/-! # Quantitative transport of the proved normal half-ball excess decay -/
noncomputable section
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 1000
open MeasureTheory Set Filter
open scoped Topology BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma boundary_inverse_halfBall_subset (P : KernelSpace n ≃L[ℝ] KernelSpace n)
    (j : Fin n) {c N r : ℝ} (hc : 0 < c) (hN : 0 < N)
    (hI : ‖P.symm.toContinuousLinearMap‖ ≤ N) (hplane : ∀ x, (P x) j=c*x j) :
    P ⁻¹' upperCampanatoBall j 0 r ⊆ upperCampanatoBall j 0 (N*r) := by
  intro z hz
  have hnorm := P.symm.toContinuousLinearMap.le_opNorm (P z)
  rw [ContinuousLinearEquiv.coe_coe,P.symm_apply_apply] at hnorm
  have hbound := hnorm.trans (mul_le_mul_of_nonneg_right hI (norm_nonneg _))
  have hzN : ‖P z‖ < r := by simpa only [Metric.mem_ball,dist_zero_right] using hz.1
  refine ⟨?_,?_⟩
  · change ‖z-0‖ < N*r
    rw [sub_zero]
    exact hbound.trans_lt (mul_lt_mul_of_pos_left hzN hN)
  · have hh := hz.2
    change 0 < (P z) j at hh
    rw [hplane] at hh
    exact (mul_pos_iff_of_pos_left hc).mp hh

/-- All Jacobians are retained in the two real integral comparisons and
cancel in the final excess estimate. No transformed-energy assumption is
introduced beyond the actual almost-everywhere weak-gradient formula. -/
theorem affine_halfBall_excess_decay (P : KernelSpace n ≃L[ℝ] KernelSpace n)
    (j : Fin n) {c M N R C : ℝ} (hc : 0 < c) (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hC : 0 ≤ C)
    (hP : ‖P.toContinuousLinearMap‖ ≤ M) (hI : ‖P.symm.toContinuousLinearMap‖ ≤ N)
    (hplane : ∀ x, (P x) j=c*x j)
    {U V : KernelSpace n → KernelSpace n} (hU : MemLp U 2 volume) (hV : MemLp V 2 volume)
    (hVU : ∀ᵐ z ∂volume, z ∈ Metric.ball (0:KernelSpace n) (R/M) → V z=boundaryDualMap P (U (P z)))
    {p : KernelSpace n} (hp : ∀ i, i ≠ j → p i=0)
    (hdec : ∀ q : KernelSpace n, (∀ i, i ≠ j → q i=0) → ∀ t : ℝ, 0 < t → t ≤ (R/M)/2 →
      fieldExcess V (upperCampanatoBall j 0 t) p ≤ C*(t/(R/M))^(n+2)*fieldExcess V (upperCampanatoBall j 0 (R/M)) q) :
    (∀ i, i ≠ j → (c⁻¹ • p) i=0) ∧
      ∀ q : KernelSpace n, (∀ i, i ≠ j → q i=0) → ∀ r : ℝ, 0 < r → r ≤ R/(2*M*N) →
      fieldExcess U (upperCampanatoBall j 0 r) (c⁻¹ • p) ≤
        (C*M^2*N^2*(M*N)^(n+2))*(r/R)^(n+2)*fieldExcess U (upperCampanatoBall j 0 R) q := by
  let δ := |P.toContinuousLinearMap.det|
  have hδ : 0 < δ := physical_affine_det_pos P
  have hL : 0 < R/M := div_pos hR hM
  have hfin (t : ℝ) : volume (upperCampanatoBall j (0:KernelSpace n) t) < ⊤ :=
    lt_of_le_of_lt (measure_mono inter_subset_left) measure_ball_lt_top
  have hpmap : boundaryDualMap P (c⁻¹ • p)=p := by
    rw [map_smul,boundaryDualMap_normal P j hplane hp,smul_smul,inv_mul_cancel₀ hc.ne',one_smul]
  refine ⟨fun i hij => by simp only [PiLp.smul_apply,smul_eq_mul,hp i hij,mul_zero],?_⟩
  intro q hq r hr hsmall
  have hNr : N*r ≤ (R/M)/2 := by
    have hh := (le_div_iff₀ (show 0 < 2*M*N by positivity)).mp hsmall
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    apply (le_div_iff₀ hM).mpr
    nlinarith
  have hpre := boundary_inverse_halfBall_subset P j hc hN hI hplane (r := r)
  have hpreball : P ⁻¹' upperCampanatoBall j 0 r ⊆ Metric.ball (0:KernelSpace n) (R/M) := by
    intro z hz
    exact Metric.ball_subset_ball (hNr.trans (by linarith)) (hpre hz).1
  have hidSmall := affine_fieldExcess_identity P hVU (isOpen_upperCampanatoBall j 0 r).measurableSet hpreball (c⁻¹ • p)
  rw [hpmap] at hidSmall
  have hsmallE : fieldExcess U (upperCampanatoBall j 0 r) (c⁻¹ • p) ≤
      N^2*δ*fieldExcess V (upperCampanatoBall j 0 (N*r)) p := by
    have hh := (affine_transformed_excess_bounds P hM.le hN.le hP hI hU
      (isOpen_upperCampanatoBall j 0 r).measurableSet (hfin r) (c⁻¹ • p)).2
    rw [hpmap,← hidSmall] at hh
    have hm := fieldExcess_mono_set hV (hfin (N*r)) hpre p
    exact hh.trans (by
      calc
        _ = (N^2*δ)*fieldExcess V (P ⁻¹' upperCampanatoBall j 0 r) p := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hm (mul_nonneg (sq_nonneg N) hδ.le))
  let Z := upperCampanatoBall j (0:KernelSpace n) (R/M)
  let S := P '' Z
  have hSm : MeasurableSet S := (P.toHomeomorph.isOpenMap Z (isOpen_upperCampanatoBall j 0 (R/M))).measurableSet
  have hSsub : S ⊆ upperCampanatoBall j 0 R := by
    rintro x ⟨z,hz,rfl⟩
    have hz' : ‖z‖ < R/M ∧ 0 < z j := by
      simpa only [Z,upperCampanatoBall,mem_inter_iff,Metric.mem_ball,dist_zero_right,mem_setOf_eq] using hz
    have hh := (boundary_normalization_maps_halfball P j hc hM hP hplane).1 hz'
    simpa only [upperCampanatoBall,mem_inter_iff,Metric.mem_ball,dist_zero_right,mem_setOf_eq] using hh
  have hpreS : P ⁻¹' S=Z := P.injective.preimage_image Z
  have hidBig := affine_fieldExcess_identity P hVU hSm (by rw [hpreS]; exact inter_subset_left) q
  rw [hpreS] at hidBig
  have hlargeE : δ*fieldExcess V Z (boundaryDualMap P q) ≤ M^2*fieldExcess U (upperCampanatoBall j 0 R) q := by
    rw [hidBig]
    have hTG := hU.continuousLinearMap_comp (boundaryDualMap P)
    have hm := fieldExcess_mono_set hTG (hfin R) hSsub (boundaryDualMap P q)
    exact hm.trans (affine_transformed_excess_bounds P hM.le hN.le hP hI hU
      (isOpen_upperCampanatoBall j 0 R).measurableSet (hfin R) q).1
  have hqmap : ∀ i, i ≠ j → (boundaryDualMap P q) i=0 := by
    rw [boundaryDualMap_normal P j hplane hq]
    intro i hij
    simp only [PiLp.smul_apply,smul_eq_mul,hq i hij,mul_zero]
  have hd := hdec (boundaryDualMap P q) hqmap (N*r) (mul_pos hN hr) hNr
  have hpow : 0 ≤ (N*r/(R/M))^(n+2) := by positivity
  calc
    fieldExcess U (upperCampanatoBall j 0 r) (c⁻¹ • p)
      ≤ N^2*δ*fieldExcess V (upperCampanatoBall j 0 (N*r)) p := hsmallE
    _ ≤ N^2*δ*(C*(N*r/(R/M))^(n+2)*fieldExcess V Z (boundaryDualMap P q)) :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    _ = (N^2*C*(N*r/(R/M))^(n+2))*(δ*fieldExcess V Z (boundaryDualMap P q)) := by ring
    _ ≤ (N^2*C*(N*r/(R/M))^(n+2))*(M^2*fieldExcess U (upperCampanatoBall j 0 R) q) :=
      mul_le_mul_of_nonneg_left hlargeE (by positivity)
    _ = _ := by
      have he : N*r/(R/M)=(M*N)*(r/R) := by field_simp
      rw [he,mul_pow]
      ring

end GaussianTilt.MomentMapLinearDirichlet
