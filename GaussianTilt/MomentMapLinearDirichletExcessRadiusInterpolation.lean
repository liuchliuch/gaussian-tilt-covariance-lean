import GaussianTilt.MomentMapLinearDirichletVariableBoundaryIteration

/-! # Genuine all-radius interpolation of the minimizing boundary excess -/
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma halfBallGradientExcess_mono [NeZero n] (u : VolumeJet n) (j : Fin n) {r R : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) : halfBallGradientExcess u j r ≤ halfBallGradientExcess u j R := by
  apply (halfBallGradientExcess_le_error u j hr (halfBallMeanNormal u j R)).trans
  haveI : Fact (volume (upperCampanatoBall j 0 R) < ∞) := ⟨(upperCampanatoBall_finite j 0 R).lt_top⟩
  have hI : IntegrableOn (fun x => ‖euclideanWeakGradient u x-
      halfBallMeanNormal u j R • EuclideanSpace.basisFun (Fin n) ℝ j‖^2) (upperCampanatoBall j 0 R) :=
    (((euclideanWeakGradient_memLp u).restrict _).sub (memLp_const _)).integrable_norm_pow (p := 2) (by norm_num)
  apply setIntegral_mono_set hI (ae_of_all _ (fun x => sq_nonneg _))
  exact ae_of_all _ (fun x hx => upperCampanatoBall_mono (by simpa only [dist_self,zero_add] using hrR) hx)

/-- A monotone actual excess with geometric-radius bounds has the same
power bound at every radius, with its explicit geometric interpolation factor. -/
theorem geometric_power_bound_to_all_radii (ω : ℝ → ℝ) {R ρ A s : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (hρ1 : ρ < 1) (hA : 0 ≤ A) (hs : 0 ≤ s)
    (hmono : MonotoneOn ω (Ioc 0 R))
    (hbound : ∀ k : ℕ, ω (R*ρ^k) ≤ A*(R*ρ^k)^s) :
    ∀ r : ℝ, 0 < r → r ≤ R → ω r ≤ (A*ρ^(-s))*r^s := by
  intro r hr hrR
  obtain ⟨k,hkl,hku⟩ := exists_nat_pow_near_of_lt_one (div_pos hr hR) ((div_le_one hR).mpr hrR) hρ hρ1
  have hrk : r ≤ R*ρ^k := by have hh := (div_le_iff₀ hR).mp hku; nlinarith
  have hkr : R*ρ^k ≤ r/ρ := by
    have hh := (lt_div_iff₀ hR).mp hkl
    rw [pow_succ] at hh
    apply (le_div_iff₀ hρ).mpr
    nlinarith
  have hkR : R*ρ^k ≤ R := by
    have hh := pow_le_one₀ hρ.le hρ1.le (n := k)
    nlinarith
  have hkpos := mul_pos hR (pow_pos hρ k)
  apply ((hmono ⟨hr,hrR⟩ ⟨hkpos,hkR⟩ hrk).trans (hbound k)).trans
  have hp := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hkpos.le hkr hs) hA
  rw [Real.div_rpow hr.le hρ.le] at hp
  convert hp using 1
  rw [Real.rpow_neg hρ.le]
  ring

/-- A convenient concrete all-radius form for the actual normal-mean excess. -/
theorem halfBallGradientExcess_bound_all_radii [NeZero n] (u : VolumeJet n) (j : Fin n)
    {R θ A β : ℝ} (hR : 0 < R) (hθ : 0 < θ) (hθ1 : θ < 1) (hA : 0 ≤ A) (hβ : 0 ≤ β)
    (hbound : ∀ k : ℕ, halfBallGradientExcess u j (R*θ^k) ≤ A*(R*θ^k)^((n:ℝ)+β)) :
    ∀ r : ℝ, 0 < r → r ≤ R → halfBallGradientExcess u j r ≤
      (A*θ^(-((n:ℝ)+β)))*r^((n:ℝ)+β) :=
  geometric_power_bound_to_all_radii (halfBallGradientExcess u j) hR hθ hθ1 hA (by positivity)
    (fun r hr s hs hrs => halfBallGradientExcess_mono u j hr.1 hrs) hbound

end GaussianTilt.MomentMapLinearDirichlet
