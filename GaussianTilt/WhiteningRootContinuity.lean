import GaussianTilt.WhiteningLimits
import GaussianTilt.NormTrace

/-! # Covariance-root convergence at isotropy in the actual operator norm -/
noncomputable section
open MeasureTheory Matrix Filter
open scoped BigOperators Matrix.Norms.L2Operator Topology MatrixOrder
namespace GaussianTilt.Whitening
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma diagonal_entry_le_opNorm (d : ι → ℝ) (i : ι) : |d i| ≤ ‖Matrix.diagonal d‖ := by
  letI : Nonempty ι := ⟨i⟩
  have h := (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) (Matrix.diagonal d)).le_opNorm
    (EuclideanSpace.single i 1)
  have he : Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) (Matrix.diagonal d)
      (EuclideanSpace.single i 1) = EuclideanSpace.single i (d i) := by
    apply WithLp.ofLp_injective
    rw [Matrix.ofLp_toEuclideanCLM]
    ext j
    simp [Matrix.mulVec_diagonal, EuclideanSpace.ofLp_single, Pi.single_apply]
    split_ifs with hj <;> simp_all
  rw [he] at h
  simpa only [EuclideanSpace.norm_single, Real.norm_eq_abs, abs_one, mul_one,
    Matrix.cstar_norm_def] using h

lemma norm_unitary_conjugate (U : Matrix.unitaryGroup ι ℝ) (A : Matrix ι ι ℝ) :
    ‖(U : Matrix ι ι ℝ) * A * star (U : Matrix ι ι ℝ)‖ = ‖A‖ := by
  rw [CStarRing.norm_mul_mem_unitary _ (unitary.star_mem _), CStarRing.norm_coe_unitary_mul]
  exact U.prop

lemma unitary_conjugate_sub_one (U : Matrix.unitaryGroup ι ℝ) (A : Matrix ι ι ℝ) :
    (U : Matrix ι ι ℝ) * A * star (U : Matrix ι ι ℝ) - 1 =
      (U : Matrix ι ι ℝ) * (A - 1) * star (U : Matrix ι ι ℝ) := by
  simp only [mul_sub, sub_mul, mul_one, Matrix.mem_unitaryGroup_iff.mp U.prop]

lemma norm_diagonal_sub_one (d : ι → ℝ) :
    ‖Matrix.diagonal d - 1‖ = ‖Matrix.diagonal (fun i ↦ d i - 1)‖ := by
  congr 1
  rw [← Matrix.diagonal_sub, Matrix.diagonal_one]

lemma root_eq_real_cfc {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    root A = cfc Real.sqrt A := by
  rw [root, CFC.sqrt_eq_real_sqrt A hA.nonneg, cfcₙ_eq_cfc]

/-- The positive root is norm-Lipschitz at the identity on the entire positive
semidefinite cone; this uses its actual spectral formula. -/
lemma root_sub_one_norm_le {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    ‖root A - 1‖ ≤ ‖A - 1‖ := by
  let U := hA.1.eigenvectorUnitary
  let d := hA.1.eigenvalues
  have hspec : A = (U : Matrix ι ι ℝ) * Matrix.diagonal d * star (U : Matrix ι ι ℝ) := by
    simpa only [RCLike.ofReal_real_eq_id, Function.id_comp] using hA.1.spectral_theorem
  have hroot : root A = (U : Matrix ι ι ℝ) * Matrix.diagonal (fun i ↦ Real.sqrt (d i)) *
      star (U : Matrix ι ι ℝ) := by
    rw [root_eq_real_cfc hA, hA.1.cfc_eq, Matrix.IsHermitian.cfc]
    rfl
  have hnorm : ‖A - 1‖ = ‖Matrix.diagonal (fun i ↦ d i - 1)‖ := by
    rw [hspec, unitary_conjugate_sub_one, norm_unitary_conjugate, norm_diagonal_sub_one]
  rw [hroot, unitary_conjugate_sub_one, norm_unitary_conjugate, norm_diagonal_sub_one]
  apply diagonal_opNorm_le (norm_nonneg _)
  intro i
  have hdi := hA.eigenvalues_nonneg i
  have hs := Real.sq_sqrt hdi
  have hr := Real.sqrt_nonneg (d i)
  have hscalar : |Real.sqrt (d i) - 1| ≤ |d i - 1| := by
    apply (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mp
    rw [sq_abs, sq_abs]
    have hnonneg := mul_nonneg (sq_nonneg (Real.sqrt (d i) - 1))
      (show 0 ≤ Real.sqrt (d i) * (Real.sqrt (d i) + 2) by positivity)
    dsimp [d] at hs hnonneg ⊢
    nlinarith
  exact hscalar.trans (hnorm.symm ▸ diagonal_entry_le_opNorm (fun i ↦ d i - 1) i)

variable {α : Type*} {l : Filter α} {C : α → Matrix ι ι ℝ}

lemma root_tendsto_one (hC : Tendsto C l (𝓝 1))
    (hp : ∀ᶠ k in l, (C k).PosSemidef) :
    Tendsto (fun k ↦ root (C k)) l (𝓝 1) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun k : α ↦ norm_nonneg (root (C k) - 1)))
    (hp.mono (fun _ h ↦ root_sub_one_norm_le h))
  exact tendsto_iff_norm_sub_tendsto_zero.mp hC

lemma inverseRoot_tendsto_one (hC : Tendsto C l (𝓝 1))
    (hp : ∀ᶠ k in l, (C k).PosSemidef) :
    Tendsto (fun k ↦ inverseRoot (C k)) l (𝓝 1) := by
  have hi : ContinuousAt (Inv.inv : Matrix ι ι ℝ → Matrix ι ι ℝ) 1 := by
    apply continuousAt_matrix_inv
    simpa only [Matrix.det_one, Ring.inverse_eq_inv'] using
      (continuousAt_inv₀ (by norm_num : (1 : ℝ) ≠ 0))
  simpa only [inverseRoot, Function.comp_def, inv_one] using
    hi.tendsto.comp (root_tendsto_one hC hp)

end GaussianTilt.Whitening
