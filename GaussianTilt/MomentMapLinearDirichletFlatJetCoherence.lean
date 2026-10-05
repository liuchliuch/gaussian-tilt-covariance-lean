import GaussianTilt.MomentMapLinearDirichletFlatJetBounds

/-! # Cross-center compatibility from actual half-ball Taylor remainders -/
noncomputable section
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 1000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff Gradient ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapRegularity
variable {n : ℕ}

/-- Two distinct boundary centers have Hölder-coherent Hessians and the
correct first-jet Taylor compatibility. Only genuine one-sided polynomial
remainders are used; the comparison ball has radius equal to their distance. -/
theorem flat_boundary_jet_cross_center_coherence (j : Fin n) (u : KernelSpace n → ℝ)
    (a b pa pb : KernelSpace n) (Ta Tb : KernelSpace n →L[ℝ] KernelSpace n)
    (ha : a j = 0) (hb : b j = 0)
    (hTa : ∀ v w, inner ℝ (Ta v) w = inner ℝ v (Ta w))
    (hTb : ∀ v w, inner ℝ (Tb v) w = inner ℝ v (Tb w))
    {r M α : ℝ} (hM : 0 ≤ M) (hα : 0 ≤ α)
    (hd : 0 < ‖a-b‖) (hdr : 2*‖a-b‖ ≤ r)
    (hApproxA : ∀ h, ‖h‖ ≤ r → 0 ≤ h j →
      |u (a+h)-quadraticJet 0 pa 0 Ta h| ≤ M*‖h‖^(2+α))
    (hApproxB : ∀ h, ‖h‖ ≤ r → 0 ≤ h j →
      |u (b+h)-quadraticJet 0 pb 0 Tb h| ≤ M*‖h‖^(2+α)) :
    ‖Ta-Tb‖ ≤ (128*M*2^(2+α))*‖a-b‖^α ∧
    ‖pa-pb-Tb (a-b)‖ ≤ (72*M*2^(2+α))*‖a-b‖^(1+α) := by
  let d := ‖a-b‖
  let ε := M*(2*d)^(2+α)
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hd0 : 0 < d := hd
  have hboundA : ∀ h : KernelSpace n, ‖h‖ ≤ d → 0 ≤ h j →
      |u (a+h)-quadraticJet 0 pa 0 Ta h| ≤ ε := by
    intro h hh hhj
    apply (hApproxA h (by dsimp [d] at hh; linarith) hhj).trans
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg h) (by linarith) (by linarith)) hM
  have hboundB : ∀ h : KernelSpace n, ‖h‖ ≤ d → 0 ≤ h j →
      |u (a+h)-quadraticJet (quadraticJet 0 pb 0 Tb (a-b)) (pb+Tb (a-b)) 0 Tb h| ≤ ε := by
    intro h hh hhj
    have hz : ‖a-b+h‖ ≤ 2*d := (norm_add_le _ _).trans (by dsimp [d] at *; linarith)
    have hzj : 0 ≤ (a-b+h) j := by simpa only [PiLp.add_apply,PiLp.sub_apply,ha,hb,sub_self,zero_add] using hhj
    have hv := hApproxB (a-b+h) (hz.trans hdr) hzj
    have he : b+(a-b+h) = a+h := by abel
    rw [he] at hv
    have hrec := quadraticJet_recenter 0 pb (a-b) 0 h Tb hTb
    simp only [sub_zero,zero_add] at hrec
    rw [← hrec]
    exact hv.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) hz (by linarith)) hM)
  obtain ⟨_,hp,hT⟩ := quadraticJet_halfBall_coherence j
    (f := fun h => u (a+h)) 0 (quadraticJet 0 pb 0 Tb (a-b)) pa (pb+Tb (a-b)) Ta Tb
    hTa hTb hd0 hε hε hboundA hboundB
  have hpow2 : (2*d)^(2+α)/d^2 = 2^(2+α)*d^α := by
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hd0.le,Real.rpow_add hd0]
    norm_num only [Real.rpow_two]
    field_simp
  have hpow1 : (2*d)^(2+α)/d = 2^(2+α)*d^(1+α) := by
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hd0.le]
    have he : (2+α : ℝ) = 1+(1+α) := by ring
    rw [he,Real.rpow_add hd0,Real.rpow_one]
    field_simp
  constructor
  · convert hT using 1
    dsimp [ε,d] at *
    have he : 64*(M*(2*‖a-b‖)^(2+α)+M*(2*‖a-b‖)^(2+α))/‖a-b‖^2 =
        128*M*((2*‖a-b‖)^(2+α)/‖a-b‖^2) := by ring
    rw [he,hpow2]
    ring
  · have he : pa-pb-Tb (a-b) = pa-(pb+Tb (a-b)) := by abel
    rw [he]
    convert hp using 1
    have he : 36*(ε+ε)/d = 72*M*((2*d)^(2+α)/d) := by dsimp [ε]; ring
    rw [he,hpow1]
    dsimp [d]
    ring

end GaussianTilt.MomentMapLinearDirichlet
