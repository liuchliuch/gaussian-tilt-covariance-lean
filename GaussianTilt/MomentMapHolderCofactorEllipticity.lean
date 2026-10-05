import GaussianTilt.MomentMapHolderCofactorOperator
import GaussianTilt.MomentMapSchauderUniformEllipticity

/-! # Genuine uniform ellipticity of the cofactor Dirichlet homotopy -/
noncomputable section
set_option maxHeartbeats 1000000
open Set Matrix
open scoped Topology BoundedContinuousFunction
namespace GaussianTilt.HolderSpace
open GaussianTilt.MomentMapSchauder
variable {n : ℕ}

lemma posDef_adjugate {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosDef) : M.adjugate.PosDef := by
  have he : M.det • M⁻¹ = M.adjugate := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv, smul_smul, mul_inv_cancel₀ hM.det_pos.ne', one_smul]
  rw [← he]
  exact hM.inv.smul hM.det_pos

lemma posDef_identity_homotopy {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosDef)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : ((1-t) • (1 : Matrix (Fin n) (Fin n) ℝ) + t • M).PosDef := by
  by_cases he : t = 1
  · simp only [he, sub_self, zero_smul, one_smul, zero_add]
    exact hM
  · exact (Matrix.PosDef.one.smul (sub_pos.mpr (lt_of_le_of_ne ht.2 he))).add_posSemidef
      (hM.posSemidef.smul ht.1)

def cofactorHomotopyFields {S : Set (Coord (n := n))} (hS : Convex ℝ S) (α : ℝ)
    (j : Jet Coord ℝ hS α) (t : ℝ) : Fin n → Fin n → Space S ℝ α :=
  fun i k => (1-t) • identityFields S α i k + t • cofactorFields S α (hessianFields hS α j) i k

lemma value_cofactorHomotopyFields {S : Set (Coord (n := n))} (hS : Convex ℝ S) (α : ℝ)
    (j : Jet Coord ℝ hS α) (t : ℝ) (x : S) :
    (show Matrix (Fin n) (Fin n) ℝ from fun i k => value S ℝ α (cofactorHomotopyFields hS α j t i k) x) =
      (1-t) • (1 : Matrix (Fin n) (Fin n) ℝ) + t • (hessianMatrix hS α j x).adjugate := by
  ext i k
  simp only [cofactorHomotopyFields, map_add, map_smul, BoundedContinuousFunction.add_apply,
    BoundedContinuousFunction.smul_apply, identityFields, value_constant, value_cofactorFields,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rfl

/-- Positive stored Hessians on a genuine compact body provide uniform
cofactor-homotopy ellipticity. No ellipticity constants are assumed. -/
theorem exists_cofactorHomotopy_uniform_ellipticity
    {S : Set (Coord (n := n))} (hS : Convex ℝ S) (hSc : IsCompact S) (α : ℝ)
    (j : Jet Coord ℝ hS α) (hpd : ∀ x : S, (hessianMatrix hS α j x).PosDef) :
    ∃ lam Λ : ℝ, 0 < lam ∧ 0 < Λ ∧ ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : S,
      ∀ v : EuclideanSpace ℝ (Fin n),
        lam * ‖v‖ ^ 2 ≤ euclideanQuadratic
          ((1-t) • (1 : Matrix (Fin n) (Fin n) ℝ) + t • (hessianMatrix hS α j x).adjugate) v ∧
        euclideanQuadratic
          ((1-t) • (1 : Matrix (Fin n) (Fin n) ℝ) + t • (hessianMatrix hS α j x).adjugate) v ≤ Λ * ‖v‖ ^ 2 := by
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hSc
  let A : ℝ × S → Matrix (Fin n) (Fin n) ℝ := fun z =>
    fun i k => value S ℝ α (cofactorHomotopyFields hS α j z.1 i k) z.2
  have hAc : Continuous A := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro k
    change Continuous (fun z : ℝ × S => (1-z.1) * value S ℝ α (identityFields S α i k) z.2 +
      z.1 * value S ℝ α (cofactorFields S α (hessianFields hS α j) i k) z.2)
    exact ((continuous_const.sub continuous_fst).mul
      ((value S ℝ α (identityFields S α i k)).continuous.comp continuous_snd)).add
      (continuous_fst.mul ((value S ℝ α (cofactorFields S α (hessianFields hS α j) i k)).continuous.comp continuous_snd))
  have hAp : ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ (univ : Set S), (A z).PosDef := by
    intro z hz
    change (show Matrix (Fin n) (Fin n) ℝ from fun i k =>
      value S ℝ α (cofactorHomotopyFields hS α j z.1 i k) z.2).PosDef
    rw [value_cofactorHomotopyFields]
    exact posDef_identity_homotopy (posDef_adjugate (hpd z.2)) hz.1
  obtain ⟨lam, Λ, hlam, hΛ, hbound⟩ := exists_uniform_ellipticity_on_compact
    (isCompact_Icc.prod (isCompact_univ : IsCompact (univ : Set S))) hAc.continuousOn hAp
  refine ⟨lam, Λ, hlam, hΛ, ?_⟩
  intro t ht x v
  have hb := hbound (t, x) ⟨ht, mem_univ x⟩ v
  simpa only [A, value_cofactorHomotopyFields] using hb

/-- The actual coefficient Hölder constants are uniform along the whole
straight-line path. They are derived from the constructed Banach coefficients. -/
theorem exists_cofactorHomotopy_uniform_holder_bound
    {S : Set (Coord (n := n))} (hS : Convex ℝ S) (α : ℝ) (j : Jet Coord ℝ hS α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) 1, ∀ i k : Fin n,
      (∀ x : S, |value S ℝ α (cofactorHomotopyFields hS α j t i k) x| ≤ C) ∧
      (∀ x y : S, |value S ℝ α (cofactorHomotopyFields hS α j t i k) x -
          value S ℝ α (cofactorHomotopyFields hS α j t i k) y| ≤ C * dist x y ^ α) := by
  let A := identityFields (n := n) S α
  let B := cofactorFields S α (hessianFields hS α j)
  let C := ‖A‖ + ‖B‖
  have hC : 0 ≤ C := add_nonneg (norm_nonneg _) (norm_nonneg _)
  refine ⟨C, hC, ?_⟩
  intro t ht i k
  have hn : ‖cofactorHomotopyFields hS α j t i k‖ ≤ C := by
    have hAi : ‖A i k‖ ≤ ‖A‖ := (norm_le_pi_norm (A i) k).trans (norm_le_pi_norm A i)
    have hBi : ‖B i k‖ ≤ ‖B‖ := (norm_le_pi_norm (B i) k).trans (norm_le_pi_norm B i)
    change ‖(1-t) • A i k + t • B i k‖ ≤ C
    calc
      _ ≤ ‖(1-t) • A i k‖ + ‖t • B i k‖ := norm_add_le _ _
      _ = (1-t) * ‖A i k‖ + t * ‖B i k‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (sub_nonneg.mpr ht.2), abs_of_nonneg ht.1]
      _ ≤ C := by
        have h1 := mul_le_mul_of_nonneg_right (show 1-t ≤ 1 by linarith [ht.1]) (norm_nonneg (A i k))
        have h2 := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg (B i k))
        dsimp [C]
        nlinarith
  constructor
  · intro x
    exact (norm_value_apply_le S ℝ α _ x).trans hn
  · intro x y
    exact (norm_value_sub_le S ℝ α _ x y).trans
      (mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg dist_nonneg _))

end GaussianTilt.HolderSpace
