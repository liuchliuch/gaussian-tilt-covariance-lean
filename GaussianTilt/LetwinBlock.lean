import Mathlib

/-! # Strict block positivity for the functional Brascamp--Lieb perturbation -/
noncomputable section
open Matrix
open scoped BigOperators
namespace GaussianTilt.Letwin

/-- Strict Schur-complement positivity, proved from the exact completing-
square identity. -/
theorem posDef_fromBlocks_of_schur {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] (A : Matrix m m ℝ) (B : Matrix m n ℝ) {D : Matrix n n ℝ}
    (hD : D.PosDef) (hS : (A - B * D⁻¹ * B.conjTranspose).PosDef) :
    (Matrix.fromBlocks A B B.conjTranspose D).PosDef := by
  letI := hD.isUnit.invertible
  refine ⟨(Matrix.IsHermitian.fromBlocks₂₂ A B hD.isHermitian).mpr hS.isHermitian, ?_⟩
  intro z hz
  let u := z ∘ Sum.inl
  let v := z ∘ Sum.inr
  have hsplit : Sum.elim u v = z := Sum.elim_comp_inl_inr z
  rw [← hsplit, dotProduct_mulVec, Matrix.schur_complement_eq₂₂ A B u v hD.isHermitian]
  by_cases hu : u = 0
  · have hv : v ≠ 0 := by
      intro hv
      apply hz
      rw [← hsplit, hu, hv]
      ext a
      cases a <;> rfl
    have hp := hD.2 v hv
    simpa only [hu, mulVec_zero, zero_add, star_zero, zero_vecMul, zero_dotProduct, add_zero,
      dotProduct_mulVec] using hp
  · have hp := hS.2 u hu
    have hn := hD.posSemidef.2 ((D⁻¹ * B.conjTranspose) *ᵥ u + v)
    rw [dotProduct_mulVec] at hp hn
    exact add_pos_of_nonneg_of_pos hn hp

/-- The strict positivity of the exact perturbation block with Schur
complement ε. -/
theorem gradient_energy_block_posDef {n : Type*} [Fintype n] [DecidableEq n]
    {H : Matrix n n ℝ} (hH : H.PosDef) (v : n → ℝ) {ε : ℝ} (hε : 0 < ε) :
    (Matrix.fromBlocks
      (fun _ _ : Unit => v ⬝ᵥ (H⁻¹ *ᵥ v) + ε)
      (fun (_ : Unit) j => v j)
      (fun i (_ : Unit) => v i) H).PosDef := by
  let B : Matrix Unit n ℝ := fun _ j => v j
  let Q : Matrix Unit Unit ℝ := fun _ _ => v ⬝ᵥ (H⁻¹ *ᵥ v) + ε
  have hBT : B.conjTranspose = (fun i (_ : Unit) => v i) := by ext i j; rfl
  have hquad (i j : Unit) : (B * H⁻¹ * B.conjTranspose) i j = v ⬝ᵥ (H⁻¹ *ᵥ v) := by
    change (v ᵥ* H⁻¹) ⬝ᵥ v = v ⬝ᵥ (H⁻¹ *ᵥ v)
    exact (dotProduct_mulVec _ _ _).symm
  have hschur : (Q - B * H⁻¹ * B.conjTranspose) =
      ε • (1 : Matrix Unit Unit ℝ) := by
    ext i j
    cases i
    cases j
    simp only [Matrix.sub_apply, Q, hquad, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    ring
  have h := posDef_fromBlocks_of_schur Q B hH
    (by rw [hschur]; exact Matrix.PosDef.one.smul hε)
  simpa only [hBT, B, Q] using h

/-- Directional version of the perturbation block, on a scalar-vector pair. -/
theorem gradient_energy_form_pos {n : Type*} [Fintype n] [DecidableEq n]
    {H : Matrix n n ℝ} (hH : H.PosDef) (g v : n → ℝ) (s : ℝ) {ε : ℝ} (hε : 0 < ε)
    (hsv : (s, v) ≠ 0) :
    0 < v ⬝ᵥ (H *ᵥ v) - 2 * s * (g ⬝ᵥ v) + s ^ 2 * (g ⬝ᵥ (H⁻¹ *ᵥ g) + ε) := by
  let z : Unit ⊕ n → ℝ := Sum.elim (fun _ => s) v
  have hz : z ≠ 0 := by
    intro hz
    apply hsv
    have hs : s = 0 := congrFun hz (Sum.inl ())
    have hv : v = 0 := by funext i; exact congrFun hz (Sum.inr i)
    simp [hs, hv]
  have hp := (gradient_energy_block_posDef hH (-g) hε).2 z hz
  let A : Matrix Unit Unit ℝ := fun _ _ => g ⬝ᵥ (H⁻¹ *ᵥ g) + ε
  let B : Matrix Unit n ℝ := fun _ i => -g i
  let C : Matrix n Unit ℝ := fun i _ => -g i
  have hAu : A *ᵥ (fun _ : Unit => s) = (fun _ => (g ⬝ᵥ (H⁻¹ *ᵥ g) + ε) * s) := by
    ext i
    simp [A, Matrix.mulVec, dotProduct]
  have hBv : B *ᵥ v = (fun _ : Unit => -(g ⬝ᵥ v)) := by
    ext i
    simp [B, Matrix.mulVec, dotProduct, Finset.sum_neg_distrib]
  have hCu : C *ᵥ (fun _ : Unit => s) = (-s) • g := by
    ext i
    simp [C, Matrix.mulVec, dotProduct]
    ring
  have heq : (star z ⬝ᵥ (Matrix.fromBlocks A B C H *ᵥ z)) =
      v ⬝ᵥ (H *ᵥ v) - 2 * s * (g ⬝ᵥ v) + s ^ 2 * (g ⬝ᵥ (H⁻¹ *ᵥ g) + ε) := by
    rw [star_trivial, Matrix.fromBlocks_mulVec]
    change Sum.elim (fun _ : Unit => s) v ⬝ᵥ
      Sum.elim (A *ᵥ (fun _ : Unit => s) + B *ᵥ v)
        (C *ᵥ (fun _ : Unit => s) + H *ᵥ v) = _
    rw [sumElim_dotProduct_sumElim, hAu, hBv, hCu]
    simp only [dotProduct_add, dotProduct_smul]
    rw [dotProduct_comm v g]
    simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton, smul_eq_mul]
    ring
  rw [← heq]
  simpa only [A, B, C, Pi.neg_apply, mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg] using hp

end GaussianTilt.Letwin
