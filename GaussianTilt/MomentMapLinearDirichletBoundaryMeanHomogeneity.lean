import GaussianTilt.MomentMapLinearDirichletBoundaryMeanBounds

/-! # Data-homogeneous uniform bounds for actual normal means -/
noncomputable section
set_option maxHeartbeats 2500000
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma normalMean_smul {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (j : Fin n) (G : X → KernelSpace n) (a : ℝ) :
    normalMean μ j (fun x => a • G x)=a*normalMean μ j G := by
  simp only [normalMean,PiLp.smul_apply,smul_eq_mul,average_eq,integral_const_mul]
  ring

lemma integral_normal_error_smul {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (j : Fin n) (G : X → KernelSpace n) (a : ℝ) :
    (∫ x, ‖a • G x-normalMean μ j (fun y => a • G y) • EuclideanSpace.basisFun (Fin n) ℝ j‖^2 ∂μ) =
      a^2*(∫ x, ‖G x-normalMean μ j G • EuclideanSpace.basisFun (Fin n) ℝ j‖^2 ∂μ) := by
  rw [normalMean_smul]
  simp_rw [← smul_smul,← smul_sub,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  exact integral_const_mul _ _

/-- The coefficient bound is chosen before both energy and excess data.
This keeps affine-subtracted vector loads uniformly controlled in the
all-center interior Campanato iteration. -/
theorem exists_uniform_normalMean_square_bound [NeZero n]
    {R β : ℝ} (hR : 0 < R) (hβ : 0 < β) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ C M : ℝ, 0 ≤ C → 0 ≤ M →
      ∀ (j : Fin n) (z : KernelSpace n), 0 ≤ z j →
      ∀ (G : KernelSpace n → KernelSpace n),
      MemLp G 2 (volume.restrict (upperCampanatoBall j z R)) →
      (∫ x in upperCampanatoBall j z R, ‖G x‖^2) ≤ M →
      (∀ r, 0 < r → r ≤ R →
        (∫ x in upperCampanatoBall j z r,
          ‖G x-normalMean (volume.restrict (upperCampanatoBall j z r)) j G •
            EuclideanSpace.basisFun (Fin n) ℝ j‖^2) ≤ C*r^((n:ℝ)+β)) →
      ∀ r, 0 < r → r ≤ R →
        (normalMean (volume.restrict (upperCampanatoBall j z r)) j G)^2 ≤ K*(M+C) := by
  obtain ⟨L,hL,hbound⟩ := exists_uniform_normalMean_bound (n := n) hR (by norm_num : (0:ℝ)≤1) hβ (by norm_num : (0:ℝ)≤1)
  refine ⟨L^2,sq_nonneg _,?_⟩
  intro C M hC hM j z hz G hG hEnergy hExcess r hr hrR
  have hsub : upperCampanatoBall j z r ⊆ upperCampanatoBall j z R :=
    upperCampanatoBall_mono (by simpa only [dist_self,zero_add] using hrR)
  have hGr := hG.mono_measure (Measure.restrict_mono hsub le_rfl)
  haveI : Fact (volume (upperCampanatoBall j z r) < ∞) := ⟨(upperCampanatoBall_finite j z r).lt_top⟩
  haveI : NeZero (volume (upperCampanatoBall j z r)) :=
    ⟨upperCampanatoBall_measure_ne_zero_of_nonneg_center j z hz hr⟩
  by_cases hzero : M+C=0
  · have hMz : M=0 := by linarith
    have hEr : (∫ x in upperCampanatoBall j z r, ‖G x‖^2) ≤ (0:ℝ) := by
      apply le_trans (setIntegral_mono_set (hG.integrable_norm_pow (p := 2) (by norm_num))
        (ae_of_all _ (fun _ => sq_nonneg _)) (ae_of_all _ (fun x hx => hsub hx)))
      simpa only [hMz] using hEnergy
    have hb := normalMean_abs_le_sqrt_energy j hGr
      (mul_pos campanatoHalfBallVolume_pos (pow_pos hr _))
      (by simpa only [measureReal_restrict_apply_univ] using upperCampanatoBall_volume_lower j z hz hr) hEr
    simp only [zero_div,Real.sqrt_zero] at hb
    have hm : normalMean (volume.restrict (upperCampanatoBall j z r)) j G=0 := abs_nonpos_iff.mp hb
    rw [hm,hzero]
    simp
  · have hN : 0 < M+C := lt_of_le_of_ne (add_nonneg hM hC) (Ne.symm hzero)
    let b := Real.sqrt (M+C)
    have hb : 0 < b := Real.sqrt_pos.2 hN
    have hb2 : b^2=M+C := Real.sq_sqrt hN.le
    have hscaleM : b⁻¹^2*M ≤ 1 := by
      rw [inv_pow,inv_mul_le_iff₀ (sq_pos_of_pos hb)]
      linarith
    have hscaleC : b⁻¹^2*C ≤ 1 := by
      rw [inv_pow,inv_mul_le_iff₀ (sq_pos_of_pos hb)]
      linarith
    let G' := fun x => b⁻¹ • G x
    have hG' : MemLp G' 2 (volume.restrict (upperCampanatoBall j z R)) := by
      change MemLp (b⁻¹ • G) 2 (volume.restrict (upperCampanatoBall j z R))
      exact hG.const_smul (b⁻¹)
    have hE' : (∫ x in upperCampanatoBall j z R, ‖G' x‖^2) ≤ (1:ℝ) := by
      simp only [G',norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,integral_const_mul]
      exact (mul_le_mul_of_nonneg_left hEnergy (sq_nonneg _)).trans hscaleM
    have hX' : ∀ t, 0 < t → t ≤ R →
        (∫ x in upperCampanatoBall j z t,
          ‖G' x-normalMean (volume.restrict (upperCampanatoBall j z t)) j G' •
            EuclideanSpace.basisFun (Fin n) ℝ j‖^2) ≤ (1:ℝ)*t^((n:ℝ)+β) := by
      intro t ht htR
      rw [show G'=fun x => b⁻¹ • G x from rfl,integral_normal_error_smul]
      calc
        _ ≤ b⁻¹^2*(C*t^((n:ℝ)+β)) := mul_le_mul_of_nonneg_left (hExcess t ht htR) (sq_nonneg _)
        _ = (b⁻¹^2*C)*t^((n:ℝ)+β) := by ring
        _ ≤ 1*t^((n:ℝ)+β) := mul_le_mul_of_nonneg_right hscaleC (Real.rpow_nonneg ht.le _)
    have ht := hbound j z hz G' hG' hE' hX' r hr hrR
    rw [show G'=fun x => b⁻¹ • G x from rfl,normalMean_smul,abs_mul,abs_of_pos (inv_pos.mpr hb)] at ht
    have hm : |normalMean (volume.restrict (upperCampanatoBall j z r)) j G| ≤ b*L :=
      (inv_mul_le_iff₀ hb).mp ht
    have hs := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hb.le hL)).mpr hm
    rw [sq_abs,mul_pow,hb2] at hs
    nlinarith

end GaussianTilt.MomentMapLinearDirichlet
