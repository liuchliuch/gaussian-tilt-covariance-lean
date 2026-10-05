import GaussianTilt.MomentMapRegularityImprovementSeed

/-! # Explicit first normalization scales from the desired value accuracy -/
noncomputable section
namespace GaussianTilt.MomentMapRegularity

lemma exists_initial_seed_scales {r R C N η : ℝ}
    (hr : 0 < r) (hC : 0≤C) (hN : 0 < N) (hη : 0 < η) :
    ∃ ρ δ : ℝ, 0 < ρ ∧ 0 < δ ∧ δ<1 ∧ ρ*N≤r/2 ∧
      δ*R^2/ρ^2+C*ρ*N^3≤η := by
  let ρ := min (r/(4*N)) (η/(4*(C*N^3+1)))
  have hden : 0 < 4*(C*N^3+1) := by positivity
  have hρ : 0 < ρ := lt_min (by positivity) (div_pos hη hden)
  have hρr : ρ*(4*N)≤r := (le_div_iff₀ (by positivity : 0 < 4*N)).mp (min_le_left _ _)
  have hρC : ρ*(4*(C*N^3+1))≤η := (le_div_iff₀ hden).mp (min_le_right _ _)
  let δ := min (1/2) (η*ρ^2/(4*(R^2+1)))
  have hdenR : 0 < 4*(R^2+1) := by positivity
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos (mul_pos hη (sq_pos_of_pos hρ)) hdenR)
  have hδR : δ*(4*(R^2+1))≤η*ρ^2 := (le_div_iff₀ hdenR).mp (min_le_right _ _)
  have hδhalf : δ≤1/2 := min_le_left _ _
  refine ⟨ρ,δ,hρ,hδ,by linarith,by nlinarith,?_⟩
  have hdensity : δ*R^2/ρ^2≤η/4 := by
    apply (div_le_iff₀ (sq_pos_of_pos hρ)).mpr
    nlinarith
  have hTaylor : C*ρ*N^3≤η/4 := by nlinarith
  linarith

end GaussianTilt.MomentMapRegularity
