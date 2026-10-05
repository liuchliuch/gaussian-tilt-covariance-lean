import GaussianTilt.MomentMapRegularityImprovementDensityNormalization

/-! # Uniform physical amplitude bounds for centered source normalizations -/
noncomputable section
open Set Metric
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

lemma densityNormalizationFactor_inv {d : ℝ} (hd : 0≤d) :
    (densityNormalizationFactor n d)⁻¹=d^((n:ℝ)⁻¹) := by
  rw [densityNormalizationFactor,Real.inv_rpow hd,inv_inv]

/-- The inverse amplitude is uniformly bounded for every actual coordinate
map in a fixed operator ball and every source density in a fixed compact
interval. This uses continuity of the true determinant, not a determinant
bound or an amplitude bound passed as an extra assumption. -/
theorem exists_uniform_inverse_amplitude_bound (M C : ℝ) :
    ∃ Q : ℝ, 0 < Q ∧ ∀ L : E n →L[ℝ] E n, ‖L‖≤M → ∀ d : ℝ, 0≤d → d≤C →
      (densityNormalizationFactor n (|L.det|^2*d))⁻¹≤Q := by
  let K := closedBall (0:E n →L[ℝ] E n) M ×ˢ Icc (0:ℝ) C
  have hK : IsCompact K := (isCompact_closedBall _ _).prod isCompact_Icc
  let F : (E n →L[ℝ] E n) × ℝ → ℝ := fun q=>(|q.1.det|^2*q.2)^((n:ℝ)⁻¹)
  have hF : Continuous F := by
    apply (Real.continuous_rpow_const (by positivity : 0≤(n:ℝ)⁻¹)).comp
    exact (((ContinuousLinearMap.continuous_det.comp continuous_fst).abs.pow 2).mul continuous_snd)
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn hF.continuousOn
  refine ⟨max B 1,lt_of_lt_of_le (by norm_num) (le_max_right _ _),?_⟩
  intro L hL d hd hdC
  have hmem : (L,d)∈K := ⟨by simpa only [mem_closedBall,dist_zero_right] using hL,⟨hd,hdC⟩⟩
  rw [densityNormalizationFactor_inv (mul_nonneg (sq_nonneg _) hd)]
  have hbabs : |(|L.det|^2*d)^((n:ℝ)⁻¹)|≤B := by simpa only [Real.norm_eq_abs,F] using hB (L,d) hmem
  exact (le_abs_self _).trans (hbabs.trans (le_max_left _ _))

end GaussianTilt.MomentMapRegularity
