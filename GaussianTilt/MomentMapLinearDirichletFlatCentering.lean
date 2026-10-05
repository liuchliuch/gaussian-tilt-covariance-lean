import GaussianTilt.MomentMapLinearDirichletFlatAmplitude
import GaussianTilt.MomentMapLinearDirichletFlatSubtraction
import GaussianTilt.MomentMapSchauderHolderInterpolation

/-! # Genuine constant-forcing correction at the flat boundary center -/
noncomputable section
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 1000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapSchauder
variable {n : ℕ}

def flatNormalQuadraticForm (j : Fin n) (c : ℝ) :
    KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ :=
  c • (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) j).smulRight
    (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) j)

lemma flatNormalQuadraticForm_apply (j : Fin n) (c : ℝ) (v w : KernelSpace n) :
    flatNormalQuadraticForm j c v w = c*v j*w j := by
  simp only [flatNormalQuadraticForm, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  change c*(v j*w j) = c*v j*w j
  ring

lemma flatNormalQuadraticForm_symmetric (j : Fin n) (c : ℝ) (v w : KernelSpace n) :
    flatNormalQuadraticForm j c v w = flatNormalQuadraticForm j c w v := by
  rw [flatNormalQuadraticForm_apply,flatNormalQuadraticForm_apply]; ring

lemma flatNormalQuadratic_polynomial (j : Fin n) (c : ℝ) (x : KernelSpace n) :
    flatTaylorPolynomial 0 (flatNormalQuadraticForm j c) x = c/2*(x j)^2 := by
  rw [flatTaylorPolynomial, ContinuousLinearMap.zero_apply, flatNormalQuadraticForm_apply]
  ring

lemma flatNormalQuadratic_laplacian (j : Fin n) (c : ℝ) (x : KernelSpace n) :
    kernelLaplacian (flatTaylorPolynomial 0 (flatNormalQuadraticForm j c)) x = c := by
  classical
  rw [kernelLaplacian_flatTaylorPolynomial]
  simp only [flatNormalQuadraticForm_apply]
  have he (i : Fin n) : c*(EuclideanSpace.basisFun (Fin n) ℝ i) j *
      (EuclideanSpace.basisFun (Fin n) ℝ i) j = if i=j then c else 0 := by
    by_cases hij : i=j
    · subst i; simp
    · simp [EuclideanSpace.basisFun_apply, EuclideanSpace.single_apply,hij,Ne.symm hij]
  simp only [he,Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte]

/-- One fixed compact cutoff supplies a uniform Hölder extension of the
centered forcing. The constant is independent of the forcing value at zero. -/
theorem exists_flat_centered_forcing_bound {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ D : ℝ, 0 < D ∧ ∀ (f : KernelSpace n → ℝ) (H : ℝ), 0 ≤ H →
      (∀ x y, |f x-f y| ≤ H*‖x-y‖^α) →
      ∀ x y, |flatResidualBump n x*(f x-f 0)-flatResidualBump n y*(f y-f 0)| ≤
        (D*H)*‖x-y‖^α := by
  let χ : KernelSpace n → ℝ := flatResidualBump n
  have hc : ContDiff ℝ ∞ χ := (flatResidualBump n).contDiff
  have hcs : HasCompactSupport χ := (flatResidualBump n).hasCompactSupport
  obtain ⟨L,hL⟩ := (hcs.fderiv ℝ).exists_bound_of_continuous (hc.continuous_fderiv (by simp))
  let M := max L 0
  have hM : 0 ≤ M := le_max_right _ _
  have hLip : ∀ x y, ‖χ x-χ y‖ ≤ M*‖x-y‖ := by
    intro x y
    exact Convex.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hc.differentiable (by simp) z)
      (fun z _ => (hL z).trans (le_max_left _ _)) convex_univ (mem_univ y) (mem_univ x)
  have hχb : ∀ x, |χ x| ≤ 1 := fun x => by
    rw [abs_of_nonneg (flatResidualBump n).nonneg]
    exact (flatResidualBump n).le_one
  have hχh : ∀ x y, |χ x-χ y| ≤ (M+2)*‖x-y‖^α := by
    intro x y
    simpa only [Real.norm_eq_abs,Real.one_rpow,mul_one] using
      holder_bound_of_sup_and_lipschitz zero_le_one hM hα hα1 zero_lt_one
        (fun x (_ : x ∈ (univ : Set (KernelSpace n))) => by simpa only [Real.norm_eq_abs] using hχb x)
        (fun x _ y _ => hLip x y) x (mem_univ x) y (mem_univ y)
  refine ⟨1+4^α*(M+2),by positivity,?_⟩
  intro f H hH hf
  have hfB : ∀ x ∈ Metric.ball (0 : KernelSpace n) 4, |f x-f 0| ≤ H*4^α := by
    intro x hx
    have hn : ‖x‖ ≤ 4 := (by simpa only [Metric.mem_ball,dist_zero_right] using hx : ‖x‖ < 4).le
    have hb := hf x 0
    simp only [sub_zero] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg x) hn hα) hH)
  have hh := global_holder_cutoff_product (χ := χ) (f := fun x => f x-f 0)
    zero_le_one (mul_nonneg hH (Real.rpow_nonneg (by norm_num) α)) (by positivity : 0 ≤ M+2) hH
    hχb hfB hχh (fun x _ y _ => by simpa only [sub_sub_sub_cancel_right] using hf x y)
    (fun x hx => by
      apply (flatResidualBump n).zero_of_le_dist
      change 3 ≤ dist x 0
      have hn : 4 ≤ dist x 0 := le_of_not_gt hx
      linarith)
  intro x y
  convert hh x y using 1 <;> ring

end GaussianTilt.MomentMapLinearDirichlet
