import GaussianTilt.MomentMapSchauderSourceCoefficients
import Mathlib.Analysis.Calculus.Taylor

/-!
# Interpolation estimates for the coefficient-freezing argument

The scalar estimates are consequences of actual Taylor's theorem, and
are then used along lines to control Hessians by a small Hölder term and
a multiple of the function supremum.
-/
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace GaussianTilt.MomentMapSchauder

lemma exists_second_order_taylor_point {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {a b : ℝ} (hab : a < b) :
    ∃ c ∈ Ioo a b, f b - f a - deriv f a * (b - a) =
      deriv (deriv f) c * (b - a) ^ 2 / 2 := by
  obtain ⟨c, hc, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) hab
    (show ContDiffOn ℝ (↑(1 : ℕ) + 1) f (Icc a b) from hf.contDiffOn)
  refine ⟨c, hc, ?_⟩
  have hda : derivWithin f (Icc a b) a = deriv f a := by
    exact (hf.differentiable (by norm_num) a).derivWithin (uniqueDiffOn_Icc hab a ⟨le_rfl, hab.le⟩)
  simp only [taylorWithinEval_succ, taylor_within_zero_eval, iteratedDerivWithin_one,
    hda, Nat.cast_one, Nat.factorial_zero, Nat.cast_zero, Nat.cast_succ,
    one_mul, zero_add, one_add_one_eq_two, inv_one, pow_one, smul_eq_mul,
    iteratedDeriv_succ, iteratedDeriv_zero, Nat.factorial_succ] at he
  have hi : iteratedDeriv 2 f = deriv (deriv f) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  norm_num only [Nat.factorial, hi, Nat.reduceMul, Nat.cast_ofNat] at he
  convert he using 1 <;> ring

section Lines
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma deriv_comp_affineLine {u : E → ℝ} (hu : Differentiable ℝ u)
    (x v : E) (t : ℝ) :
    deriv (fun r : ℝ => u (x + r • v)) t = fderiv ℝ u (x + t • v) v := by
  simpa only [Function.comp_def, id_eq, one_smul] using
    ((hu (x + t • v)).hasFDerivAt.comp_hasDerivAt t
      (((hasDerivAt_id t).smul_const v).const_add x)).deriv

lemma secondDeriv_comp_affineLine {u : E → ℝ} (hu : ContDiff ℝ 2 u)
    (x v : E) (t : ℝ) :
    deriv (deriv (fun r : ℝ => u (x + r • v))) t =
      fderiv ℝ (fderiv ℝ u) (x + t • v) v v := by
  have hud := hu.differentiable (by norm_num)
  have hDu : Differentiable ℝ (fderiv ℝ u) :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiable le_rfl
  have hF : Differentiable ℝ (fun y => fderiv ℝ u y v) :=
    hDu.clm_apply (differentiable_const v)
  have he : deriv (fun r : ℝ => u (x + r • v)) =
      (fun t => fderiv ℝ u (x + t • v) v) :=
    funext (deriv_comp_affineLine hud x v)
  rw [he, deriv_comp_affineLine hF, fderiv_clm_apply (hDu _) (differentiableAt_const v)]
  simp

/-- Actual second-order Taylor remainder from a Hölder bound on the second
Fréchet derivative along the segment. There is no third derivative premise. -/
theorem taylor_second_remainder_holder_bound {u : E → ℝ} (hu : ContDiff ℝ 2 u)
    {C α : ℝ} (hC : 0 ≤ C) (hα : 0 ≤ α) (x v : E)
    (hH : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ u) (x + t • v) - fderiv ℝ (fderiv ℝ u) x‖ ≤
        C * ‖t • v‖ ^ α) :
    |u (x + v) - u x - fderiv ℝ u x v -
      (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ u) x v v| ≤
        (C / 2) * ‖v‖ ^ α * ‖v‖ ^ 2 := by
  have hg : ContDiff ℝ 2 (fun t : ℝ => u (x + t • v)) :=
    hu.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  obtain ⟨t, ht, he⟩ := exists_second_order_taylor_point hg (show (0 : ℝ) < 1 by norm_num)
  simp only [zero_smul, one_smul, add_zero, sub_zero, one_pow, mul_one,
    deriv_comp_affineLine (hu.differentiable (by norm_num)),
    secondDeriv_comp_affineLine hu] at he
  let L := fderiv ℝ (fderiv ℝ u) (x + t • v) - fderiv ℝ (fderiv ℝ u) x
  have hnorm : ‖t • v‖ ≤ ‖v‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
    exact mul_le_of_le_one_left (norm_nonneg _) ht.2.le
  have hpow : ‖t • v‖ ^ α ≤ ‖v‖ ^ α := Real.rpow_le_rpow (norm_nonneg _) hnorm hα
  have hL : ‖L‖ ≤ C * ‖v‖ ^ α :=
    (hH t (Ioo_subset_Icc_self ht)).trans (mul_le_mul_of_nonneg_left hpow hC)
  have hLv : |L v v| ≤ C * ‖v‖ ^ α * ‖v‖ ^ 2 := by
    have h1 := (L v).le_opNorm v
    have h2 := L.le_opNorm v
    have h3 := mul_le_mul_of_nonneg_right h2 (norm_nonneg v)
    have h4 := mul_le_mul_of_nonneg_right hL (sq_nonneg ‖v‖)
    rw [Real.norm_eq_abs] at h1
    nlinarith
  have hr : u (x + v) - u x - fderiv ℝ u x v -
      (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ u) x v v = (1 / 2 : ℝ) * L v v := by
    dsimp [L]
    linarith
  rw [hr, abs_mul]
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  nlinarith

/-- The local-set form used by quadratic approximation and coefficient
freezing. Segment containment is explicit and can be discharged by convexity
of an interior ball. -/
theorem taylor_second_remainder_holder_on {u : E → ℝ} (hu : ContDiff ℝ 2 u)
    {C α : ℝ} (hC : 0 ≤ C) (hα : 0 ≤ α) {S : Set E}
    (hH : ∀ y ∈ S, ∀ z ∈ S,
      ‖fderiv ℝ (fderiv ℝ u) y - fderiv ℝ (fderiv ℝ u) z‖ ≤ C * ‖y - z‖ ^ α)
    {x v : E} (hx : x ∈ S) (hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • v ∈ S) :
    |u (x + v) - u x - fderiv ℝ u x v -
      (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ u) x v v| ≤
        (C / 2) * ‖v‖ ^ α * ‖v‖ ^ 2 := by
  apply taylor_second_remainder_holder_bound hu hC hα x v
  intro t ht
  simpa only [add_sub_cancel_left] using hH (x + t • v) (hseg t ht) x hx

end Lines

end GaussianTilt.MomentMapSchauder
