import GaussianTilt.MomentMapRegularityImprovementRates

/-! # Closing the numeric recurrence for genuine affine improvement -/
noncomputable section
namespace GaussianTilt.MomentMapRegularity

lemma improvement_coefficient_budget {R α γ d A B C : ℝ}
    (hR : 0 < R) (hR1 : R≤1) (hα : γ≤α) (hγd : γ=3*d)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) :
    4*(A*R^γ+(B*R^α)/2)/(R^d)^2+4*C*R^d ≤
      (4*(A+B/2+C))*R^d := by
  have hdensity : R^α≤R^γ := Real.rpow_le_rpow_of_exponent_ge hR hR1 hα
  have hnum : A*R^γ+(B*R^α)/2≤(A+B/2)*R^γ := by
    have hh:=mul_le_mul_of_nonneg_left hdensity hB
    nlinarith
  have hsq : 0 < (R^d)^2 := sq_pos_of_pos (Real.rpow_pos_of_pos hR _)
  have he : R^γ/(R^d)^2=R^d := by
    apply (div_eq_iff hsq.ne').mpr
    rw [← Real.rpow_natCast,← Real.rpow_mul hR.le,← Real.rpow_add hR,hγd]
    congr 1
    ring
  calc
    _ ≤ 4*((A+B/2)*R^γ)/(R^d)^2+4*C*R^d := by
      exact add_le_add_right (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnum (by norm_num)) hsq.le) _
    _ = (4*(A+B/2+C))*R^d := by
      rw [mul_div_assoc,mul_div_assoc,he]
      ring

lemma improvement_next_error_budget {R α c γ A B C θ : ℝ}
    (hR : 0 < R) (hR1 : R≤1) (hα : 3*c≤α) (hγ : (1+c)*γ=c)
    (hB : 0≤B) (hC : 0≤C) (hθ : 0≤θ) (hθhalf : θ≤1/2)
    (hA : B+8*C≤A) :
    (B*R^α)/(R^c)^2+C*R^c*(1+2*θ)^3 ≤ A*(R^(1+c))^γ := by
  have hpow : R^α≤R^(3*c) := Real.rpow_le_rpow_of_exponent_ge hR hR1 hα
  have hcpos : 0 < R^c := Real.rpow_pos_of_pos hR _
  have hcubic : R^(3*c)/(R^c)^2=R^c := by
    apply (div_eq_iff (sq_pos_of_pos hcpos).ne').mpr
    rw [← Real.rpow_natCast,← Real.rpow_mul hR.le,← Real.rpow_add hR]
    congr 1
    ring
  have hdensity : (B*R^α)/(R^c)^2≤B*R^c := by
    calc
      _ ≤ (B*R^(3*c))/(R^c)^2 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hB) (sq_nonneg _)
      _ = _ := by rw [mul_div_assoc,hcubic]
  have hcube : (1+2*θ)^3≤8 := by
    calc
      _ ≤ (2:ℝ)^3 := pow_le_pow_left₀ (by linarith) (by linarith) _
      _ = _ := by norm_num
  have ht := mul_le_mul_of_nonneg_left hcube (mul_nonneg hC hcpos.le)
  rw [← Real.rpow_mul hR.le,hγ]
  have hsum := mul_le_mul_of_nonneg_right hA hcpos.le
  nlinarith

lemma improvement_numeric_exponents {α : ℝ} (hα : 0 < α) (hα1 : α≤1) :
    let c := improvementScaleExponent α
    let γ := c/(1+c)
    let d := γ/3
    0 < c ∧ 0 < γ ∧ 0 < d ∧ γ≤α ∧ 3*c≤α ∧ (1+c)*γ=c ∧ γ=3*d := by
  dsimp only
  have hc : 0 < improvementScaleExponent α := (improvement_exponents hα hα1).1
  have hd : 0 < 1+improvementScaleExponent α := by linarith
  have hγ : 0 < improvementScaleExponent α/(1+improvementScaleExponent α) := div_pos hc hd
  refine ⟨hc,hγ,by positivity,?_,?_,?_,by ring⟩
  · apply (div_le_iff₀ hd).mpr
    dsimp [improvementScaleExponent]
    nlinarith [sq_nonneg α]
  · dsimp [improvementScaleExponent]
    linarith
  · exact mul_div_cancel₀ _ hd.ne'

end GaussianTilt.MomentMapRegularity
