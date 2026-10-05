import GaussianTilt.MomentMapLinearDirichletCampanatoL2Geometry

/-! # Exact scale-normalized L² coherence on genuine half-balls -/
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

def campanatoHalfBallVolume (n : ℕ) : ℝ :=
  (1/2 : ℝ)^n*volume.real (Metric.ball (0 : KernelSpace n) 1)

lemma campanatoHalfBallVolume_pos [NeZero n] : 0 < campanatoHalfBallVolume n :=
  upperCampanatoBall_volume_constant_pos

lemma campanato_energy_power {R α : ℝ} (hR : 0 < R) :
    R^((n : ℝ)+2*α) = R^n*(R^α)^2 := by
  rw [Real.rpow_add hR,Real.rpow_natCast]
  rw [mul_comm (2:ℝ) α,Real.rpow_mul hR.le,Real.rpow_two]

/-- Natural unnormalized mean-square errors on overlapping sets give the
correct α-power coefficient coherence. All volume factors are proved. -/
theorem l2_campanato_coherence_at_scale [NeZero n] {F : Type*} [NormedAddCommGroup F]
    (j : Fin n) (x : KernelSpace n) (hx : 0 ≤ x j) (G : KernelSpace n → F) (a b : F)
    {A B : Set (KernelSpace n)} {R ρ C α : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (hC : 0 ≤ C)
    (hSA : upperCampanatoBall j x (ρ*R) ⊆ A) (hSB : upperCampanatoBall j x (ρ*R) ⊆ B)
    (hIa : IntegrableOn (fun y => ‖G y-a‖^2) A)
    (hIb : IntegrableOn (fun y => ‖G y-b‖^2) B)
    (hea : (∫ y in A, ‖G y-a‖^2) ≤ C*R^((n : ℝ)+2*α))
    (heb : (∫ y in B, ‖G y-b‖^2) ≤ C*R^((n : ℝ)+2*α)) :
    ‖a-b‖ ≤ (2*Real.sqrt (C/(campanatoHalfBallVolume n*ρ^n)))*R^α := by
  let v := campanatoHalfBallVolume n
  have hv : 0 < v := campanatoHalfBallVolume_pos
  have hvol := upperCampanatoBall_volume_lower j x hx (mul_pos hρ hR)
  have hbound := l2_constant_coherence_on_overlap (upperCampanatoBall_finite j x (ρ*R)) hSA hSB
    (mul_pos hv (pow_pos (mul_pos hρ hR) _)) hvol
    (mul_nonneg hC (Real.rpow_nonneg hR.le _)) G a b hIa hIb hea heb
  have he : (C*R^((n:ℝ)+2*α))/(v*(ρ*R)^n) =
      (C/(v*ρ^n))*(R^α)^2 := by
    rw [campanato_energy_power hR,mul_pow]
    field_simp
  have hnon : 0 ≤ C/(v*ρ^n) := div_nonneg hC (mul_pos hv (pow_pos hρ _)).le
  rw [he,Real.sqrt_mul hnon,Real.sqrt_sq_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hR _)] at hbound
  convert hbound using 1 <;> ring

end GaussianTilt.MomentMapLinearDirichlet
