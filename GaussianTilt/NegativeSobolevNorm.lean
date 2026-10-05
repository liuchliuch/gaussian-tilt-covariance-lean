import GaussianTilt.NegativeSobolevDuality

/-! # Identification with the source H⁻¹ supremum -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ContDiff Topology ENNReal
namespace GaussianTilt.Letwin

lemma gradientSquare_neg {n : ℕ} (g : CoordinateSpace n → ℝ) :
    gradientSquare (-g) = gradientSquare g := by
  funext x
  change gradientSquare (fun y => -g y) x = gradientSquare g x
  simp only [gradientSquare, coordinateDerivative_neg, neg_sq]

/-- The signed supremum used verbatim in the source definition. Finite
Dirichlet energy is explicit to avoid the junk value of the Bochner integral
on nonintegrable functions. -/
def signedNegativeSobolevNorm {n : ℕ} (μ : Measure (CoordinateSpace n))
    (f : CoordinateSpace n → ℝ) : ℝ≥0∞ :=
  ⨆ (g : CoordinateSpace n → ℝ) (_ : MemLp g 2 μ) (_ : LocallyLipschitz g)
    (_ : Integrable (gradientSquare g) μ)
    (_ : (∫ x, gradientSquare g x ∂μ) ≤ 1), ENNReal.ofReal (∫ x, f x * g x ∂μ)

/-- The absolute-pairing norm used by the formal development is exactly the
signed supremum in Letwin equation (2.19), since the true test class is closed
under negation. -/
theorem negativeSobolevNorm_eq_signed {n : ℕ} (μ : Measure (CoordinateSpace n))
    (f : CoordinateSpace n → ℝ) : negativeSobolevNorm μ f = signedNegativeSobolevNorm μ f := by
  apply le_antisymm
  · refine iSup_le fun g => iSup_le fun hg => iSup_le fun hgl =>
      iSup_le fun hgi => iSup_le fun hge => ?_
    by_cases hp : 0 ≤ ∫ x, f x * g x ∂μ
    · rw [abs_of_nonneg hp]
      exact le_iSup_of_le g (le_iSup_of_le hg (le_iSup_of_le hgl
        (le_iSup_of_le hgi (le_iSup_of_le hge le_rfl))))
    · have hngi : Integrable (gradientSquare (-g)) μ := by rw [gradientSquare_neg]; exact hgi
      have hnge : (∫ x, gradientSquare (-g) x ∂μ) ≤ 1 := by rw [gradientSquare_neg]; exact hge
      have hnp : (∫ x, f x * (-g) x ∂μ) = -(∫ x, f x * g x ∂μ) := by
        simp only [Pi.neg_apply, mul_neg, integral_neg]
      rw [abs_of_neg (lt_of_not_ge hp), ← hnp]
      exact le_iSup_of_le (-g) (le_iSup_of_le hg.neg (le_iSup_of_le hgl.neg
        (le_iSup_of_le hngi (le_iSup_of_le hnge le_rfl))))
  · refine iSup_le fun g => iSup_le fun hg => iSup_le fun hgl =>
      iSup_le fun hgi => iSup_le fun hge => ?_
    exact (ENNReal.ofReal_le_ofReal (le_abs_self _)).trans
      (le_iSup_of_le g (le_iSup_of_le hg (le_iSup_of_le hgl
        (le_iSup_of_le hgi (le_iSup_of_le hge le_rfl)))))

/-- A finite H⁻¹ norm forces mean zero. Constant tests, whose actual
Dirichlet energy is zero, supply the proof. -/
theorem integral_eq_zero_of_negativeSobolevNorm_ne_top {n : ℕ}
    {μ : Measure (CoordinateSpace n)} [IsFiniteMeasure μ] (f : CoordinateSpace n → ℝ)
    (hN : negativeSobolevNorm μ f ≠ ⊤) : (∫ x, f x ∂μ) = 0 := by
  let C := (negativeSobolevNorm μ f).toReal
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have htest (c : ℝ) : |c * ∫ x, f x ∂μ| ≤ C := by
    have hg : gradientSquare (fun _ : CoordinateSpace n => c) = 0 := by
      funext x
      simp [gradientSquare, coordinateDerivative]
    have hi : Integrable (gradientSquare (fun _ : CoordinateSpace n => c)) μ := by rw [hg]; exact integrable_zero _ _ _
    have he : (∫ x, gradientSquare (fun _ : CoordinateSpace n => c) x ∂μ) ≤ 1 := by rw [hg]; simp
    have hn : ENNReal.ofReal |∫ x, f x * c ∂μ| ≤ negativeSobolevNorm μ f :=
      le_iSup_of_le (fun _ => c) (le_iSup_of_le (memLp_const c)
        (le_iSup_of_le (LocallyLipschitz.const c) (le_iSup_of_le hi (le_iSup_of_le he le_rfl))))
    have hb := (ENNReal.ofReal_le_iff_le_toReal hN).mp hn
    rw [integral_mul_const] at hb
    simpa only [mul_comm] using hb
  by_contra hm
  have hmabs : 0 < |∫ x, f x ∂μ| := abs_pos.mpr hm
  have ht := htest ((C + 1) / |∫ x, f x ∂μ|)
  rw [abs_mul, abs_of_pos (div_pos (by linarith) hmabs), div_mul_cancel₀ _ hmabs.ne'] at ht
  linarith

end GaussianTilt.Letwin
