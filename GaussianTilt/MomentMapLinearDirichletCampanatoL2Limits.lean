import GaussianTilt.MomentMapLinearDirichletCampanatoL2Scale

/-! # Genuine limits of geometric-radius L² constant approximations -/
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapRegularity
variable {n : ℕ}

/-- Mean-square approximation at geometric radii constructs an actual
limiting coefficient and quantitative tails at every boundary center. -/
theorem exists_l2_campanato_geometric_limit [NeZero n]
    {F : Type*} [NormedAddCommGroup F] [CompleteSpace F]
    (j : Fin n) (x : KernelSpace n) (hx : 0 ≤ x j) (G : KernelSpace n → F) (p : ℕ → F)
    {R ρ C α : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (hρ1 : ρ < 1) (hC : 0 ≤ C) (hα : 0 < α)
    (hI : ∀ k, IntegrableOn (fun y => ‖G y-p k‖^2) (upperCampanatoBall j x (R*ρ^k)))
    (hE : ∀ k, (∫ y in upperCampanatoBall j x (R*ρ^k), ‖G y-p k‖^2) ≤
      C*(R*ρ^k)^((n:ℝ)+2*α)) :
    ∃ p₀ : F, Tendsto p atTop (𝓝 p₀) ∧ ∀ k,
      ‖p k-p₀‖ ≤ (2*Real.sqrt (C/(campanatoHalfBallVolume n*ρ^n)))*
        (R*ρ^k)^α/(1-ρ^α) := by
  let K := 2*Real.sqrt (C/(campanatoHalfBallVolume n*ρ^n))
  have hq : ρ^α < 1 := Real.rpow_lt_one hρ.le hρ1 hα
  have hstep : ∀ k, ‖p k-p (k+1)‖ ≤ (K*R^α)*(ρ^α)^k := by
    intro k
    have hRk : 0 < R*ρ^k := mul_pos hR (pow_pos hρ _)
    have he : R*ρ^(k+1) = ρ*(R*ρ^k) := by rw [pow_succ]; ring
    have hrmono : R*ρ^(k+1) ≤ R*ρ^k := by rw [he]; nlinarith
    have hsubset : upperCampanatoBall j x (ρ*(R*ρ^k)) ⊆ upperCampanatoBall j x (R*ρ^k) := by
      apply upperCampanatoBall_mono
      simp only [dist_self,zero_add]
      nlinarith
    have hsubself : upperCampanatoBall j x (ρ*(R*ρ^k)) ⊆ upperCampanatoBall j x (R*ρ^(k+1)) := by rw [he]
    have hNext : (∫ y in upperCampanatoBall j x (R*ρ^(k+1)), ‖G y-p (k+1)‖^2) ≤
        C*(R*ρ^k)^((n:ℝ)+2*α) := by
      apply (hE (k+1)).trans
      apply mul_le_mul_of_nonneg_left _ hC
      apply Real.rpow_le_rpow (by positivity) hrmono
      positivity
    have ht := l2_campanato_coherence_at_scale j x hx G (p k) (p (k+1)) hRk hρ hC
      hsubset hsubself (hI k) (hI (k+1)) (hE k) hNext
    convert ht using 1
    rw [Real.mul_rpow hR.le (pow_nonneg hρ.le k),← Real.rpow_pow_comm hρ.le]
    dsimp [K]
    ring
  obtain ⟨p₀,hp,ht⟩ := exists_limit_geometric_increments p hq hstep
  refine ⟨p₀,hp,?_⟩
  intro k
  convert ht k using 1
  rw [Real.mul_rpow hR.le (pow_nonneg hρ.le k),← Real.rpow_pow_comm hρ.le]
  dsimp [K]
  ring

end GaussianTilt.MomentMapLinearDirichlet
