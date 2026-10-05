import GaussianTilt.MomentMapLinearDirichletFlatTranslation

/-! # Uniform actual quadratic approximation along the flat boundary -/
noncomputable section
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 1000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma flatTaylorPolynomial_dilate (A : KernelSpace n →L[ℝ] ℝ)
    (Q : KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ) (r : ℝ) (x : KernelSpace n) :
    flatTaylorPolynomial (r • A) ((r^2) • Q) x = flatTaylorPolynomial A Q (r • x) := by
  simp only [flatTaylorPolynomial,ContinuousLinearMap.smul_apply,map_smul,smul_eq_mul]
  ring

lemma flat_recenter_source_holder {f : KernelSpace n → ℝ} {H α r : ℝ}
    (hH : 0 ≤ H) (hα : 0 ≤ α) (hr : 0 < r) (hr1 : r ≤ 1)
    (hf : ∀ x y, |f x-f y| ≤ H*‖x-y‖^α) (a : KernelSpace n) :
    ∀ x y, |r^2*f (r • x+a)-r^2*f (r • y+a)| ≤ H*‖x-y‖^α := by
  intro x y
  rw [← mul_sub,abs_mul,abs_of_nonneg (sq_nonneg r)]
  have hb := hf (r • x+a) (r • y+a)
  rw [add_sub_add_right_eq_sub,← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos hr,
    Real.mul_rpow hr.le (norm_nonneg _)] at hb
  have hrp : r^α ≤ 1 := Real.rpow_le_one hr.le hr1 hα
  have hr2 : r^2 ≤ 1 := by nlinarith
  have hpow := Real.rpow_nonneg (norm_nonneg (x-y)) α
  calc
    _ ≤ r^2*(H*(r^α*‖x-y‖^α)) := mul_le_mul_of_nonneg_left hb (sq_nonneg r)
    _ ≤ H*‖x-y‖^α := by
      have ht := mul_le_mul_of_nonneg_right hrp hpow
      have hu := mul_le_mul_of_nonneg_left ht hH
      nlinarith [mul_le_mul_of_nonneg_left hu (sq_nonneg r),
        mul_le_mul_of_nonneg_right hr2 (mul_nonneg hH hpow)]

/-- Every flat boundary center in the unit disk has a genuine compatible
quadratic approximation on a fixed quarter-radius half-ball. The constant
is uniform in the center and derives from the weak Poisson equation. -/
theorem exists_uniform_flat_boundary_poisson_expansions [NeZero n] {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : Fin n) (u f : KernelSpace n → ℝ),
      FlatWeakPoisson j u f → Continuous f → ∀ B H : ℝ,
      0 ≤ B → 0 ≤ H → (∀ x y, |f x-f y| ≤ H*‖x-y‖^α) →
      (∀ x ∈ Metric.ball (0 : KernelSpace n) 2, |u x| ≤ B) →
      ∀ a : KernelSpace n, ‖a‖ ≤ 1 → a j = 0 →
      ∃ A : KernelSpace n →L[ℝ] ℝ, ∃ Q : KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ,
        (∀ v w, Q v w = Q w v) ∧
        (∀ h, h j = 0 → flatTaylorPolynomial A Q h = 0) ∧
        (∀ h, kernelLaplacian (flatTaylorPolynomial A Q) h = -f a) ∧
        (∀ h, ‖h‖ ≤ 1/4 → 0 ≤ h j →
          |u (a+h)-flatTaylorPolynomial A Q h| ≤ C*(B+H+|f a|)*‖h‖^(2+α)) := by
  obtain ⟨C,hC,hExpansion⟩ := exists_flat_boundary_poisson_expansion (n := n) hα hα1
  refine ⟨C*4^(2+α),by positivity,?_⟩
  intro j u f hu hfc B H hB hH hfH huB a ha haj
  let r : ℝ := 1/4
  have hr : 0 < r := by norm_num [r]
  have hr1 : r ≤ 1 := by norm_num [r]
  have har : ‖a‖+2*r ≤ 2 := by dsimp [r]; linarith
  let v := fun x => u (r • x+a)
  let g := fun x => r^2*f (r • x+a)
  have hv := hu.recenter a haj hr har
  have hg : Continuous g := continuous_const.mul (hfc.comp ((continuous_const.smul continuous_id).add continuous_const))
  have hgH : ∀ x y, |g x-g y| ≤ H*‖x-y‖^α := flat_recenter_source_holder hH hα.le hr hr1 hfH a
  have hvB : ∀ x ∈ Metric.ball (0 : KernelSpace n) 2, |v x| ≤ B :=
    fun x hx => huB _ (flat_recenter_mem_ball hr har hx)
  obtain ⟨A,Q,hQs,hP0,hPl,hRem⟩ := hExpansion j v g hv hg B H hB hH hgH hvB
  have he : flatTaylorPolynomial ((4 : ℝ) • A) ((4 : ℝ)^2 • Q) = fun h => flatTaylorPolynomial A Q ((4 : ℝ) • h) :=
    funext (flatTaylorPolynomial_dilate A Q 4)
  refine ⟨(4 : ℝ) • A,(4 : ℝ)^2 • Q,?_,?_,?_,?_⟩
  · intro v w
    simp only [ContinuousLinearMap.smul_apply,smul_eq_mul]
    rw [hQs v w]
  · intro h hh
    rw [he]
    exact hP0 _ (by simp only [PiLp.smul_apply,smul_eq_mul,hh,mul_zero])
  · intro h
    rw [he,kernelLaplacian_comp_smul_C2 (contDiff_infty.mp (contDiff_flatTaylorPolynomial A Q) 2),hPl]
    simp only [g,smul_zero,zero_add]
    dsimp [r]
    ring
  · intro h hh hhj
    have hnorm : ‖(4 : ℝ) • h‖ ≤ 1 := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0 : ℝ)<4)]; linarith
    have hj : 0 ≤ ((4 : ℝ) • h) j := by
      simp only [PiLp.smul_apply,smul_eq_mul]; positivity
    have hb := hRem ((4 : ℝ) • h) hnorm hj
    have hval : v ((4 : ℝ) • h) = u (a+h) := by
      dsimp [v,r]
      rw [smul_smul]
      norm_num
      rw [add_comm]
    have hg0 : |g 0| ≤ |f a| := by
      simp only [g,smul_zero,zero_add,abs_mul,abs_of_nonneg (sq_nonneg r)]
      dsimp [r]
      nlinarith [abs_nonneg (f a)]
    rw [hval,← flatTaylorPolynomial_dilate] at hb
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<4),
      Real.mul_rpow (by norm_num : (0:ℝ)≤4) (norm_nonneg h)] at hb
    apply hb.trans
    have hp := Real.rpow_nonneg (norm_nonneg h) (2+α)
    have hp4 : 0 ≤ (4:ℝ)^(2+α) := Real.rpow_nonneg (by norm_num) _
    have ht := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg0 hC.le) (mul_nonneg hp4 hp)
    nlinarith

end GaussianTilt.MomentMapLinearDirichlet
