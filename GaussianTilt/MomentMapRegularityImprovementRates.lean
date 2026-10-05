import GaussianTilt.MomentMapRegularityImprovementScales

/-! # Explicit positive exponents for adaptive quadratic improvement -/
noncomputable section
namespace GaussianTilt.MomentMapRegularity

/-- The adaptive scale exponent is chosen from the actual density Hölder exponent. -/
def improvementScaleExponent (α : ℝ) : ℝ := α/16

def improvementRemainderExponent (α : ℝ) : ℝ :=
  improvementScaleExponent α / (2*(1+improvementScaleExponent α))

lemma improvement_exponents {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    0 < improvementScaleExponent α ∧
    0 < improvementRemainderExponent α ∧
    improvementRemainderExponent α ≤ 1 ∧
    (1+improvementScaleExponent α)^2*(2+improvementRemainderExponent α) ≤ 2+α ∧
    1 ≤ (1+improvementScaleExponent α)*(1-improvementRemainderExponent α) := by
  let c := improvementScaleExponent α
  have hc : 0 < c := by dsimp [c, improvementScaleExponent]; positivity
  have hc1 : c ≤ 1/16 := by dsimp [c, improvementScaleExponent]; linarith
  have hcα : α=16*c := by dsimp [c, improvementScaleExponent]; ring
  have hd : 0 < 2*(1+c) := by positivity
  change 0<c ∧ 0<c/(2*(1+c)) ∧ c/(2*(1+c))≤1 ∧
    (1+c)^2*(2+c/(2*(1+c)))≤2+α ∧ 1≤(1+c)*(1-c/(2*(1+c)))
  refine ⟨hc,div_pos hc hd,(div_le_one hd).mpr (by linarith),?_,?_⟩
  · have he : (1+c)^2*(2+c/(2*(1+c)))=(1+c)*(2+(5/2:ℝ)*c) := by
      field_simp
      ring
    rw [he,hcα]
    have hsq : c^2≤c/16 := by nlinarith
    nlinarith
  · have he : (1+c)*(1-c/(2*(1+c)))=1+c/2 := by
      field_simp
      ring
    rw [he]
    linarith

/-- The density Hölder modulus and the genuine cubic reference remainder
produce a fixed positive quadratic order throughout every adaptive gap. -/
lemma improvement_gap_remainder_bound {α r s A B : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hr : 0 < r) (hr1 : r ≤ 1) (hs : 0 < s)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hlower : r^((1+improvementScaleExponent α)^2) ≤ s)
    (hupper : s ≤ r^(1+improvementScaleExponent α)) :
    A*r^(2+α)+B*s^3/r ≤ (A+B)*s^(2+improvementRemainderExponent α) := by
  obtain ⟨hc,hβ,hβ1,hd,ht⟩ := improvement_exponents hα hα1
  exact adaptive_gap_remainder_bound hr hr1 hs hc.le hβ.le hβ1 hA hB hlower hupper hd ht

end GaussianTilt.MomentMapRegularity
