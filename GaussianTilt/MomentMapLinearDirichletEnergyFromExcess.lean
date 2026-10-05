import GaussianTilt.MomentMapLinearDirichletBoundaryExcessComparison

/-! # Actual energy decay extracted from one common excess approximant -/
noncomputable section
set_option maxHeartbeats 3000000
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet

/-- A single approximating constant at all small radii gives true rⁿ
energy decay. Its size is extracted on an actual positive-volume
intermediate set; no pointwise value or pointwise gradient estimate enters. -/
theorem energy_decay_of_common_excess (n : ℕ) {X F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup F] (μ : Measure X) (S : ℝ → Set X) (G : X → F) (p : F)
    {R θ K c V : ℝ} (hR : 0 < R) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hK : 0 < K)
    (hc : 0 < c) (hV : 0 ≤ V) (hfin : μ (S R) ≠ ∞)
    (hsub : ∀ r : ℝ, 0 < r → r ≤ R → S r ⊆ S R)
    (hG : MemLp G 2 (μ.restrict (S R)))
    (hLower : c*(θ*R)^n ≤ μ.real (S (θ*R)))
    (hUpper : ∀ r : ℝ, 0 < r → r ≤ θ*R → μ.real (S r) ≤ V*r^n)
    (hExcess : ∀ r : ℝ, 0 < r → r ≤ θ*R →
      (∫ x in S r, ‖G x-p‖^2 ∂μ) ≤ K*(r/R)^(n+2)*(∫ x in S R, ‖G x‖^2 ∂μ)) :
    ∀ r : ℝ, 0 < r → r ≤ θ*R →
      (∫ x in S r, ‖G x‖^2 ∂μ) ≤
        (2*K+4*(K+1)*V/(c*θ^n))*(r/R)^n*(∫ x in S R, ‖G x‖^2 ∂μ) := by
  let E := ∫ x in S R, ‖G x‖^2 ∂μ
  have hE : 0 ≤ E := integral_nonneg (fun _ => sq_nonneg _)
  have hθR : 0 < θ*R := mul_pos hθ hR
  have hθRR : θ*R ≤ R := by nlinarith
  have hmeasure (r : ℝ) (hr : 0 < r) (hrR : r ≤ R) : μ (S r) ≠ ∞ :=
    ne_top_of_le_ne_top hfin (measure_mono (hsub r hr hrR))
  have hLp (r : ℝ) (hr : 0 < r) (hrR : r ≤ R) : MemLp G 2 (μ.restrict (S r)) :=
    hG.mono_measure (Measure.restrict_mono_set μ (hsub r hr hrR))
  have hGI := hG.integrable_norm_pow (p := 2) (by norm_num)
  have hmono (r : ℝ) (hr : 0 < r) (hrR : r ≤ R) : (∫ x in S r, ‖G x‖^2 ∂μ) ≤ E :=
    setIntegral_mono_set hGI (ae_of_all _ (fun _ => sq_nonneg _))
      (ae_of_all _ (fun _ hx => hsub r hr hrR hx))
  have hMidLp := hLp (θ*R) hθR hθRR
  haveI : Fact (μ (S (θ*R)) < ∞) := ⟨(hmeasure (θ*R) hθR hθRR).lt_top⟩
  have hMidErr : IntegrableOn (fun x => ‖G x-p‖^2) (S (θ*R)) μ :=
    (hMidLp.sub (memLp_const p)).integrable_norm_pow (p := 2) (by norm_num)
  have hMidZero : IntegrableOn (fun x => ‖G x-(0:F)‖^2) (S (θ*R)) μ := by
    simpa only [sub_zero] using hMidLp.integrable_norm_pow (p := 2) (by norm_num)
  have hcoh := l2_constant_coherence_sq (hmeasure (θ*R) hθR hθRR) G p 0 hMidErr hMidZero
  simp only [sub_zero] at hcoh
  have hMidBound : (∫ x in S (θ*R), ‖G x-p‖^2 ∂μ) ≤ K*E := by
    have hh := hExcess (θ*R) hθR le_rfl
    rw [mul_div_cancel_right₀ θ hR.ne'] at hh
    have hp := pow_le_one₀ hθ.le hθ1 (n := n+2)
    exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_right hp (mul_nonneg hK.le hE)])
  have hm : 0 < c*(θ*R)^n := mul_pos hc (pow_pos hθR _)
  have hpBound : ‖p‖^2 ≤ 2*(K+1)*E/(c*(θ*R)^n) := by
    apply (le_div_iff₀ hm).mpr
    have ht := mul_le_mul_of_nonneg_right hLower (sq_nonneg ‖p‖)
    have hmE := hmono (θ*R) hθR hθRR
    nlinarith
  intro r hr hrt
  have hrR : r ≤ R := hrt.trans hθRR
  have hGr := hLp r hr hrR
  haveI : Fact (μ (S r) < ∞) := ⟨(hmeasure r hr hrR).lt_top⟩
  have htriangle := integral_sq_norm_decomposition hGr (hGr.sub (memLp_const p))
    (memLp_const p) (ae_of_all _ (fun x => show G x=(G x-p)+p by abel))
  simp only [Pi.sub_apply,integral_const,smul_eq_mul,measureReal_restrict_apply_univ] at htriangle
  have hconst : μ.real (S r)*‖p‖^2 ≤
      (2*(K+1)*V/(c*θ^n))*(r/R)^n*E := by
    have ht := mul_le_mul (hUpper r hr hrt) hpBound (sq_nonneg ‖p‖) (mul_nonneg hV (pow_nonneg hr.le _))
    apply ht.trans_eq
    rw [mul_pow,div_pow]
    field_simp
  have hratio : 0 ≤ r/R := (div_pos hr hR).le
  have hratio1 : r/R ≤ 1 := (div_le_one hR).mpr hrR
  have hpow : (r/R)^(n+2) ≤ (r/R)^n := by
    rw [pow_add]
    exact mul_le_of_le_one_right (pow_nonneg hratio _) (pow_le_one₀ hratio hratio1)
  have hErr := hExcess r hr hrt
  have hErr' : (∫ x in S r, ‖G x-p‖^2 ∂μ) ≤ K*(r/R)^n*E :=
    hErr.trans (by nlinarith [mul_le_mul_of_nonneg_right hpow (mul_nonneg hK.le hE)])
  change (∫ x in S r, ‖G x‖^2 ∂μ) ≤ (2*K+4*(K+1)*V/(c*θ^n))*(r/R)^n*E
  calc
    _ ≤ 2*(K*(r/R)^n*E)+2*((2*(K+1)*V/(c*θ^n))*(r/R)^n*E) := by
      nlinarith only [htriangle,hconst,hErr']
    _ = _ := by ring

end GaussianTilt.MomentMapLinearDirichlet
