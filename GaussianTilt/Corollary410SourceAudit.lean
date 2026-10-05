import GaussianTilt.Reference.Section4Statements

/-! # Independent arithmetic audit of the printed Corollary 4.10

No implementation theorem is imported. The false same-c chain is refuted
by field arithmetic alone. This does not invalidate the two-constant
interpretation or the main lower bound, and no source edit is made here.
-/
noncomputable section
open Set
namespace GaussianTilt.Reference

/-- For A>1 the displayed c/t is strictly smaller, not larger, than cD
when t=A/D. This is the entire source-level constant conflict. -/
theorem reciprocal_precision_constant_strict {A c D : ℝ}
    (hA : 1<A) (hc : 0<c) (hD : 0<D) : c/(A/D)<c*D := by
  have hA0 : 0<A := lt_trans zero_lt_one hA
  have he : c/(A/D)=(c*D)/A := by field_simp
  rw [he]
  exact div_lt_self (mul_pos hc hD) hA

/-- The precise dimension-scale form of the arithmetic conflict. -/
theorem printed410_chain_false {A c : ℝ} {d : ℕ}
    (hA : 1<A) (hc : 0<c) (hd : 0<d) :
    ¬ c*(d:ℝ)^(2/5:ℝ)≤c/Lower.precision d A := by
  exact not_le.mpr (reciprocal_precision_constant_strict hA hc
    (Real.rpow_pos_of_pos (by exact_mod_cast hd) _))

/-- Preserving the paper's arbitrary fixed A makes its literal same-c
numbered proposition false. The corrected target is a different Prop. -/
theorem not_Literal410 : ¬ Literal410 := by
  rintro ⟨A₀,hA₀,hall⟩
  let A := max (max 1 A₀) 2
  have hA : 1<A := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  obtain ⟨c,hc,d₀,hd₀⟩ := hall A (le_max_left _ _)
  let d := max d₀ 1
  have hd : 0<d := lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
  let i : Fin d := ⟨0,hd⟩
  have hcchain := (hd₀ d (le_max_left _ _) i).2.2
  exact printed410_chain_false hA hc hd hcchain

end GaussianTilt.Reference
