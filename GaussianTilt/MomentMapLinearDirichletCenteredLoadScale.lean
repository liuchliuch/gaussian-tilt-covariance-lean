import GaussianTilt.MomentMapLinearDirichletCenteredLoadBounds
import GaussianTilt.MomentMapLinearDirichletCampanatoL2Scale

/-! # The genuine centered load has the required dimensional forcing rate -/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Set
open scoped ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin
variable {n : ℕ}

/-- The actual radius-weighted scalar and centered vector load coefficient
has square O(r^(n+2β)), with no hidden scale-independent vector term. -/
theorem centered_load_coefficient_sq_bound {Ω : Set (CoordinateSpace n)}
    {r F H β V : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hF : 0 ≤ F) (hH : 0 ≤ H)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hV : 0 ≤ V)
    (hvol : volume.real Ω ≤ V*r^n) :
    ((2*r*F+(n:ℝ)*H*r^β)*Real.sqrt (volume.real Ω))^2 ≤
      ((2*F+(n:ℝ)*H)^2*V)*r^((n:ℝ)+2*β) := by
  have hrpow : r ≤ r^β := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hr hr1 hβ1
  have hco : 2*r*F+(n:ℝ)*H*r^β ≤ (2*F+(n:ℝ)*H)*r^β := by
    nlinarith [mul_le_mul_of_nonneg_right hrpow hF]
  have hco0 : 0 ≤ 2*r*F+(n:ℝ)*H*r^β := by positivity
  have hco1 : 0 ≤ (2*F+(n:ℝ)*H)*r^β := by positivity
  have hsq := (sq_le_sq₀ hco0 hco1).mpr hco
  calc
    _ = (2*r*F+(n:ℝ)*H*r^β)^2*volume.real Ω := by
      rw [mul_pow,Real.sq_sqrt (show 0 ≤ volume.real Ω from ENNReal.toReal_nonneg)]
    _ ≤ ((2*F+(n:ℝ)*H)*r^β)^2*(V*r^n) :=
      mul_le_mul hsq hvol ENNReal.toReal_nonneg (sq_nonneg _)
    _ = _ := by rw [campanato_energy_power hr]; ring

end GaussianTilt.MomentMapLinearDirichlet
