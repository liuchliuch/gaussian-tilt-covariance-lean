import GaussianTilt.MomentMapLinearDirichletFlatEndpoint

/-! # Removing the flat boundary normalization by actual amplitude scaling -/
noncomputable section
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 1000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff Gradient ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma flatTaylorPolynomial_smul (s : ℝ) (A : KernelSpace n →L[ℝ] ℝ)
    (Q : KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ) (x : KernelSpace n) :
    flatTaylorPolynomial (s • A) (s • Q) x = s*flatTaylorPolynomial A Q x := by
  simp only [flatTaylorPolynomial, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- Uniform boundary expansion for arbitrary amplitude and Hölder seminorm,
with zero forcing at the center. No smallness or normalized-size premise remains. -/
theorem exists_centered_flat_boundary_expansion [NeZero n] {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : Fin n) (u f : KernelSpace n → ℝ),
      FlatWeakPoisson j u f → Continuous f → HasCompactSupport f → ∀ B H : ℝ,
      0 ≤ B → 0 ≤ H → (∀ x y, |f x-f y| ≤ H*‖x-y‖^α) → f 0 = 0 →
      (∀ x ∈ Metric.ball (0 : KernelSpace n) 2, |u x| ≤ B) →
      ∃ A : KernelSpace n →L[ℝ] ℝ, ∃ Q : KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ,
        (∀ v w, Q v w = Q w v) ∧
        (∀ x, x j = 0 → flatTaylorPolynomial A Q x = 0) ∧
        (∀ x, kernelLaplacian (flatTaylorPolynomial A Q) x = 0) ∧
        (∀ x, ‖x‖ ≤ 1 → 0 ≤ x j →
          |u x-flatTaylorPolynomial A Q x| ≤ C*(B+H)*‖x‖^(2+α)) := by
  obtain ⟨ε,M,hε,hM,hNorm⟩ := exists_normalized_flat_boundary_expansion (n := n) hα hα1
  let K := 2^α/ε
  have hK : 0 < K := div_pos (Real.rpow_pos_of_pos (by norm_num) _) hε
  refine ⟨M*(1+K), by positivity, ?_⟩
  intro j u f hu hfc hfs B H hB hH hfH hf0 huB
  let N := B+H*K
  have hN : 0 ≤ N := add_nonneg hB (mul_nonneg hH hK.le)
  by_cases hn : N = 0
  · have hB0 : B = 0 := by dsimp [N] at hn; nlinarith [mul_nonneg hH hK.le]
    refine ⟨0,0,by simp,by simp [flatTaylorPolynomial],?_,?_⟩
    · intro x
      rw [kernelLaplacian_flatTaylorPolynomial]
      simp
    · intro x hx hxj
      have hxb : x ∈ Metric.ball (0 : KernelSpace n) 2 := by
        rw [Metric.mem_ball, dist_zero_right]; linarith
      have hux : u x = 0 := abs_nonpos_iff.mp (by simpa only [hB0] using huB x hxb)
      simp only [hux, flatTaylorPolynomial, ContinuousLinearMap.zero_apply, mul_zero, add_zero,
        sub_zero, abs_zero]
      positivity
  have hNp : 0 < N := lt_of_le_of_ne hN (Ne.symm hn)
  have hNi : 0 ≤ N⁻¹ := inv_nonneg.mpr hN
  have hscaled : ∀ x y, |N⁻¹*f x-N⁻¹*f y| ≤ (N⁻¹*H)*‖x-y‖^α := by
    intro x y
    rw [← mul_sub, abs_mul, abs_of_nonneg hNi]
    exact (mul_le_mul_of_nonneg_left (hfH x y) hNi).trans_eq (by ring)
  have hsmall : (N⁻¹*H)*2^α ≤ ε := by
    have hh : H*K ≤ N := le_add_of_nonneg_left hB
    have he : H*2^α ≤ N*ε := by
      have ht := mul_le_mul_of_nonneg_right hh hε.le
      dsimp [K] at ht
      field_simp at ht
      nlinarith
    calc
      (N⁻¹*H)*2^α = N⁻¹*(H*2^α) := by ring
      _ ≤ N⁻¹*(N*ε) := mul_le_mul_of_nonneg_left he hNi
      _ = ε := by field_simp
  have hub : ∀ x ∈ Metric.ball (0 : KernelSpace n) 2, |N⁻¹*u x| ≤ 1 := by
    intro x hx
    rw [abs_mul, abs_of_nonneg hNi]
    calc
      _ ≤ N⁻¹*B := mul_le_mul_of_nonneg_left (huB x hx) hNi
      _ ≤ N⁻¹*N := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (mul_nonneg hH hK.le)) hNi
      _ = 1 := inv_mul_cancel₀ hn
  obtain ⟨A,Q,hQs,hP0,hPl,hRem⟩ := hNorm j (fun x => N⁻¹*u x) (fun x => N⁻¹*f x)
    (hu.amplitude N⁻¹) (continuous_const.mul hfc) (hfs.mul_left) (N⁻¹*H)
    (mul_nonneg hNi hH) hscaled (by simp only [hf0,mul_zero]) hsmall hub
  refine ⟨N • A,N • Q,?_,?_,?_,?_⟩
  · intro v w
    simpa only [ContinuousLinearMap.smul_apply, smul_eq_mul] using congrArg (N * ·) (hQs v w)
  · intro x hx
    rw [flatTaylorPolynomial_smul,hP0 x hx,mul_zero]
  · intro x
    have he : flatTaylorPolynomial (N • A) (N • Q) = fun y => N*flatTaylorPolynomial A Q y :=
      funext (flatTaylorPolynomial_smul N A Q)
    rw [he,kernelLaplacian_const_mul_C2 _ (contDiff_infty.mp (contDiff_flatTaylorPolynomial A Q) 2),hPl,mul_zero]
  · intro x hx hxj
    have hb := mul_le_mul_of_nonneg_left (hRem x hx hxj) hN
    have he : u x-flatTaylorPolynomial (N • A) (N • Q) x =
        N*(N⁻¹*u x-flatTaylorPolynomial A Q x) := by
      rw [flatTaylorPolynomial_smul]
      field_simp
    rw [he,abs_mul,abs_of_nonneg hN]
    apply hb.trans
    have hNN : N ≤ (1+K)*(B+H) := by
      dsimp [N]
      nlinarith [mul_nonneg hK.le hB]
    have ht := mul_le_mul_of_nonneg_left hNN hM.le
    have hp := Real.rpow_nonneg (norm_nonneg x) (2+α)
    nlinarith [mul_le_mul_of_nonneg_right ht hp]

end GaussianTilt.MomentMapLinearDirichlet
