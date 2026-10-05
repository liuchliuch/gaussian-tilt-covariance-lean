import GaussianTilt.MomentMapLinearDirichletEnergyDecay

/-! # Exact constants joining the genuine replacement and harmonic estimates -/
noncomputable section
set_option maxHeartbeats 1000000
namespace GaussianTilt.MomentMapLinearDirichlet

def replacementIterationConstant (Kh J : ℝ) : ℝ := (4*Kh+2)*(1+J)

lemma replacementIterationConstant_pos {Kh J : ℝ} (hKh : 0 < Kh) (hJ : 0 ≤ J) :
    0 < replacementIterationConstant Kh J := by unfold replacementIterationConstant; positivity

/-- The actual L² replacement triangles and correction bound combine into
exact energy/excess recurrence coefficients. This keeps the coefficient
oscillation term coupled to the original local energy, not its supremum. -/
theorem absorb_energy_excess_replacement (n : ℕ) {E X W E' X' Kh J θ δ F : ℝ}
    (hE : 0 ≤ E) (hX : 0 ≤ X) (hKh : 0 < Kh) (hJ : 0 ≤ J)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hF : 0 ≤ F)
    (hW : W ≤ J*δ^2*E+F)
    (hEnergy : E' ≤ 4*(Kh*θ^n)*E+(4*(Kh*θ^n)+2)*W)
    (hExcess : X' ≤ 4*(Kh*θ^(n+2))*X+(4*(Kh*θ^(n+2))+2)*W) :
    E' ≤ (replacementIterationConstant Kh J*θ^n+replacementIterationConstant Kh J*δ^2)*E+(4*Kh+2)*F ∧
    X' ≤ replacementIterationConstant Kh J*θ^(n+2)*X+
      replacementIterationConstant Kh J*δ^2*E+(4*Kh+2)*F := by
  let K := replacementIterationConstant Kh J
  have hKmain : 4*Kh ≤ K := by dsimp [K,replacementIterationConstant]; nlinarith
  have hKerr : (4*Kh+2)*J ≤ K := by dsimp [K,replacementIterationConstant]; nlinarith
  have hpow (k : ℕ) : θ^k ≤ 1 := pow_le_one₀ hθ hθ1
  have hpow0 (k : ℕ) : 0 ≤ θ^k := pow_nonneg hθ k
  have herror : 0 ≤ J*δ^2*E+F := by positivity
  have hbound (k : ℕ) : (4*(Kh*θ^k)+2)*W ≤ K*δ^2*E+(4*Kh+2)*F := by
    calc
      _ ≤ (4*(Kh*θ^k)+2)*(J*δ^2*E+F) := mul_le_mul_of_nonneg_left hW (by positivity)
      _ ≤ (4*Kh+2)*(J*δ^2*E+F) := mul_le_mul_of_nonneg_right (by nlinarith [hpow k]) herror
      _ ≤ _ := by
        have ht := mul_le_mul_of_nonneg_right hKerr (mul_nonneg (sq_nonneg δ) hE)
        nlinarith
  constructor
  · have hm := mul_le_mul_of_nonneg_right hKmain (mul_nonneg (hpow0 n) hE)
    have he := hbound n
    nlinarith
  · have hm := mul_le_mul_of_nonneg_right hKmain (mul_nonneg (hpow0 (n+2)) hX)
    have he := hbound (n+2)
    nlinarith

end GaussianTilt.MomentMapLinearDirichlet
