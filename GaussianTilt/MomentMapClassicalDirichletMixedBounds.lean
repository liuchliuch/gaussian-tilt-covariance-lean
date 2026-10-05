import GaussianTilt.MomentMapClassicalDirichletMixedCalculus

/-! # Actual trace-weighted bounds for the mixed boundary equation -/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

lemma abs_matrix_entry_le_trace {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef)
    (i j : Fin n) : |A i j| ≤ A.trace := by
  have hdiag (k : Fin n) : 0 ≤ A k k := by
    simpa [dotProduct, Matrix.mulVec, Pi.single_apply] using hA.2 (Pi.single k (1 : ℝ))
  have hle (k : Fin n) : A k k ≤ A.trace :=
    Finset.single_le_sum (fun l _ => hdiag l) (Finset.mem_univ k)
  have hp := hA.2 (Pi.single i (1 : ℝ) + Pi.single j (1 : ℝ))
  have hm := hA.2 (Pi.single i (1 : ℝ) - Pi.single j (1 : ℝ))
  have hs : A j i = A i j := by simpa only [star_trivial] using hA.isHermitian.apply i j
  simp only [star_trivial, Matrix.mulVec_add, dotProduct_add, add_dotProduct,
    Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct,
    Matrix.mulVec_single_one, single_dotProduct, one_mul, Matrix.col_apply, hs] at hp hm
  apply abs_le.mpr
  constructor <;> linarith [hle i, hle j]

lemma abs_linearizedMA_le_trace_bound {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) {f : CoordinateSpace n → ℝ} (x : CoordinateSpace n)
    {K : ℝ} (hK : 0 ≤ K) (hH : ∀ i j, |coordinateHessian f x i j| ≤ K) :
    |linearizedMA A f x| ≤ (n : ℝ) ^ 2 * K * A.trace := by
  unfold linearizedMA Matrix.trace Matrix.diag
  simp only [Matrix.mul_apply]
  calc
    |∑ i, ∑ j, A i j * coordinateHessian f x j i| ≤
        ∑ i, ∑ j, |A i j * coordinateHessian f x j i| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, A.trace * K := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul (abs_matrix_entry_le_trace hA i j) (hH j i)
        (abs_nonneg _) hA.trace_nonneg
    _ = _ := by simp [Matrix.trace, Matrix.diag]; ring

/-- An actual determinant upper bound gives a quantitative positive lower
bound for inverse-Hessian trace; no eigenvalue bound is assumed. -/
theorem trace_inverse_lower_of_det_upper [NeZero n]
    {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.PosDef) {F : ℝ} (hF : H.det ≤ F) :
    1 ≤ max 1 F * H⁻¹.trace := by
  let C := max 1 F
  have hC : 0 < C := zero_lt_one.trans_le (le_max_left _ _)
  have hC1 : 1 ≤ C := le_max_left _ _
  have hpow : H.det ≤ C ^ n := hF.trans ((le_max_right _ _).trans (le_self_pow₀ hC1 (NeZero.ne n)))
  have hd : 1 ≤ (C • H⁻¹).det := by
    rw [Matrix.det_smul, Fintype.card_fin, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', ← div_eq_mul_inv]
    exact (le_div_iff₀ hH.det_pos).mpr (by simpa using hpow)
  have hp := log_det_le_trace_sub_card (hH.inv.smul hC)
  have hl := Real.log_nonneg hd
  rw [Matrix.trace_smul] at hp
  simp only [smul_eq_mul, Fintype.card_fin] at hp
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  change 1 ≤ C * H⁻¹.trace
  linarith

/-- The tangential derivative forcing is controlled by the actual inverse
trace, using only C¹ source control and fixed chart/forcing derivatives. -/
theorem tangential_derivative_forcing_trace_bound [NeZero n]
    {u F β : CoordinateSpace n → ℝ} (hu : ContDiff ℝ ∞ u)
    {x : CoordinateSpace n} (hβ : ContDiffAt ℝ 2 β x)
    (hH : (coordinateHessian u x).PosDef)
    (hMA : ∀ᶠ y in 𝓝 x, (coordinateHessian u y).det = Real.exp (F y)) (a j : Fin n)
    {M B₀ B₁ B₂ K D : ℝ} (hM : 0 ≤ M) (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁)
    (hB₂ : 0 ≤ B₂) (hK : 0 ≤ K)
    (hug : |coordinateDerivative j u x| ≤ M) (hβ0 : |β x| ≤ B₀)
    (hβ1 : |coordinateDerivative j β x| ≤ B₁)
    (hβ2 : ∀ l m, |coordinateHessian β x l m| ≤ B₂)
    (hFa : |coordinateDerivative a F x| ≤ K) (hFj : |coordinateDerivative j F x| ≤ K)
    (hdet : (coordinateHessian u x).det ≤ D) :
    |linearizedMA (coordinateHessian u x)⁻¹
      (fun y => coordinateDerivative a u y - β y * coordinateDerivative j u y) x| ≤
      ((K + B₀ * K + 2 * B₁) * max 1 D + M * (n : ℝ) ^ 2 * B₂) *
        (coordinateHessian u x)⁻¹.trace := by
  let A := (coordinateHessian u x)⁻¹
  have htr : 0 ≤ A.trace := hH.inv.posSemidef.trace_nonneg
  have hLβ := abs_linearizedMA_le_trace_bound hH.inv.posSemidef x hB₂ hβ2
  have htrlo := trace_inverse_lower_of_det_upper hH hdet
  rw [linearizedMA_tangential_derivative hu hβ hH hMA a j]
  have hfirst : |coordinateDerivative a F x - β x * coordinateDerivative j F x| ≤ K + B₀ * K := by
    apply (abs_sub _ _).trans
    rw [abs_mul]
    exact add_le_add hFa (mul_le_mul hβ0 hFj (abs_nonneg _) hB₀)
  have hsecond : |coordinateDerivative j u x * linearizedMA A β x| ≤
      M * ((n : ℝ) ^ 2 * B₂ * A.trace) := by
    rw [abs_mul]
    exact mul_le_mul hug hLβ (abs_nonneg _) hM
  have hthird : |2 * coordinateDerivative j β x| ≤ 2 * B₁ := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left hβ1 (by norm_num)
  have hbound := (abs_sub
    (coordinateDerivative a F x - β x * coordinateDerivative j F x - coordinateDerivative j u x * linearizedMA A β x)
    (2 * coordinateDerivative j β x)).trans
    (add_le_add ((abs_sub _ _).trans (add_le_add hfirst hsecond)) hthird)
  change _ ≤ _ * A.trace
  apply hbound.trans
  have hcoeff : 0 ≤ K + B₀ * K + 2 * B₁ := by positivity
  have hmul := mul_le_mul_of_nonneg_left htrlo hcoeff
  dsimp [A] at *
  nlinarith

end GaussianTilt.MomentMapRegularity
