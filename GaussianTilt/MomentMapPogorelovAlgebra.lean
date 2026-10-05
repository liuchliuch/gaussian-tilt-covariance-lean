import GaussianTilt.LetwinPositivity

/-! # Coordinate-free third-derivative contraction for Pogorelov's estimate -/
noncomputable section
open Matrix
open scoped BigOperators
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

lemma weightedTrace_pair_comm (A X Y : Matrix (Fin n) (Fin n) ℝ) :
    trace (A * X * A * Y) = trace (A * Y * A * X) := by
  rw [Matrix.mul_assoc (A * X), Matrix.mul_assoc (A * Y)]
  exact Matrix.trace_mul_comm _ _

lemma weightedTrace_outer_right (A D : Matrix (Fin n) (Fin n) ℝ) (u v : Fin n → ℝ) :
    trace (A * D * A * vecMulVec u v) = v ⬝ᵥ (A *ᵥ (D *ᵥ (A *ᵥ u))) := by
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec]
  simp only [← Matrix.mulVec_mulVec]
  exact dotProduct_comm _ _

lemma weightedTrace_outer_left (A D : Matrix (Fin n) (Fin n) ℝ) (u v : Fin n → ℝ) :
    trace (A * vecMulVec u v * A * D) = v ⬝ᵥ (A *ᵥ (D *ᵥ (A *ᵥ u))) := by
  rw [weightedTrace_pair_comm, weightedTrace_outer_right]

lemma weightedTrace_outer_outer (A : Matrix (Fin n) (Fin n) ℝ) (u v w z : Fin n → ℝ) :
    trace (A * vecMulVec u v * A * vecMulVec w z) =
      (v ⬝ᵥ (A *ᵥ w)) * (z ⬝ᵥ (A *ᵥ u)) := by
  rw [weightedTrace_outer_right, Matrix.vecMulVec_mulVec]
  simp only [op_smul_eq_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

lemma weightedTrace_square_nonneg (A D : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosSemidef) (hD : D.IsSymm) : 0 ≤ trace (A * D * A * D) := by
  have h := GaussianTilt.Letwin.weighted_trace_gram_posSemidef A hA
    (fun _ : Unit => D) (fun _ => hD)
  have h' := h.2 (fun _ : Unit => (1 : ℝ))
  simpa [dotProduct, Matrix.mulVec] using h'

lemma symmetric_dot_mulVec (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    (v w : Fin n → ℝ) : v ⬝ᵥ (A *ᵥ w) = (A *ᵥ v) ⬝ᵥ w := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA.eq]

/-- The contraction inequality needed in the actual Pogorelov test-function
calculation. It is obtained by subtracting the weighted projection onto a
single row/column and proving the remaining matrix energy nonnegative. -/
theorem pogorelov_third_derivative_contraction
    (H D : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosDef) (hD : D.IsSymm)
    (e : Fin n → ℝ) (hw : 0 < e ⬝ᵥ (H *ᵥ e)) :
    2 * ((D *ᵥ e) ⬝ᵥ (H⁻¹ *ᵥ (D *ᵥ e))) / (e ⬝ᵥ (H *ᵥ e)) -
      (e ⬝ᵥ (D *ᵥ e)) ^ 2 / (e ⬝ᵥ (H *ᵥ e)) ^ 2 ≤
        trace (H⁻¹ * D * H⁻¹ * D) := by
  let A := H⁻¹
  let h := H *ᵥ e
  let d := D *ᵥ e
  let w := e ⬝ᵥ h
  let g := e ⬝ᵥ d
  have hw0 : w ≠ 0 := hw.ne'
  have hA : A.IsSymm := by
    simpa only [Matrix.IsSymm, Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hH.inv.isHermitian
  have hAh : A *ᵥ h = e := by
    dsimp [A, h]
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hH.det_pos.ne'),
      Matrix.one_mulVec]
  have hhh : h ⬝ᵥ (A *ᵥ h) = w := by rw [hAh, dotProduct_comm]
  have hdh : d ⬝ᵥ (A *ᵥ h) = g := by rw [hAh, dotProduct_comm]
  have hhd : h ⬝ᵥ (A *ᵥ d) = g := by rw [symmetric_dot_mulVec A hA, hAh]
  have hDD : h ⬝ᵥ (A *ᵥ (D *ᵥ (A *ᵥ d))) = d ⬝ᵥ (A *ᵥ d) := by
    rw [symmetric_dot_mulVec A hA, hAh, symmetric_dot_mulVec D hD]
  let C := D - w⁻¹ • vecMulVec h d - w⁻¹ • vecMulVec d h + (g / w ^ 2) • vecMulVec h h
  have hCs : C.IsSymm := by
    ext i j
    simp only [C, Matrix.transpose_apply, Matrix.sub_apply, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply]
    rw [hD.apply j i]
    ring
  have hpos := weightedTrace_square_nonneg A C hH.inv.posSemidef hCs
  have henergy : trace (A * C * A * C) = trace (A * D * A * D) -
      2 * (d ⬝ᵥ (A *ᵥ d)) / w + g ^ 2 / w ^ 2 := by
    dsimp only [C]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_sub,
      Matrix.trace_smul, smul_eq_mul]
    simp only [weightedTrace_outer_outer]
    simp only [weightedTrace_outer_left, weightedTrace_outer_right]
    simp only [hAh, show D *ᵥ e = d from rfl, hhd, hDD,
      show h ⬝ᵥ e = w from dotProduct_comm _ _, show d ⬝ᵥ e = g from dotProduct_comm _ _]
    field_simp
    <;> ring
  rw [henergy] at hpos
  change 2 * (d ⬝ᵥ (A *ᵥ d)) / w - g ^ 2 / w ^ 2 ≤ trace (A * D * A * D)
  linarith

end GaussianTilt.MomentMapRegularity
