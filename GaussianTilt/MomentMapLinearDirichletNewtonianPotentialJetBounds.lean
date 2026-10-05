import GaussianTilt.MomentMapLinearDirichletNewtonianPotentialEstimates
import GaussianTilt.MomentMapLinearDirichletNewtonianPotentialBounds
import GaussianTilt.MomentMapHolderJetBounds

/-! # Parameter-uniform genuine C²,α jet bounds for smooth-data potentials -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff Convolution
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapSchauder
variable {n : ℕ}

lemma holder_bound_on_of_lipschitz_and_bound {X F : Type*} [MetricSpace X] [NormedAddCommGroup F]
    {S : Set X} {f : X → F} {B α : ℝ} (hB : 0 ≤ B) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hb : ∀ x ∈ S, ‖f x‖ ≤ B)
    (hl : ∀ x ∈ S, ∀ y ∈ S, ‖f x - f y‖ ≤ B * dist x y) :
    ∀ x ∈ S, ∀ y ∈ S, ‖f x - f y‖ ≤ 2 * B * dist x y ^ α := by
  intro x hx y hy
  by_cases hd : dist x y ≤ 1
  · have hh := Real.self_le_rpow_of_le_one dist_nonneg hd hα1
    exact (hl x hx y hy).trans ((mul_le_mul_of_nonneg_left hh hB).trans
      (by nlinarith [Real.rpow_nonneg (dist_nonneg (x := x) (y := y)) α]))
  · have hn : ‖f x - f y‖ ≤ 2 * B := (norm_sub_le _ _).trans (by linarith [hb x hx, hb y hy])
    exact hn.trans (le_mul_of_one_le_right (by positivity) (Real.one_le_rpow (le_of_lt (lt_of_not_ge hd)) hα))

/-- The bound is uniform over all smooth data with the same support,
supremum and Hölder bounds. This is the actual compactness input. -/
theorem exists_newtonianPotential_jet_bound [NeZero n]
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) {A R F H : ℝ}
    (hR : 0 ≤ R) (hF : 0 ≤ F) (hH : 0 ≤ H) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : KernelSpace n → ℝ,
      ContDiff ℝ ∞ f → HasCompactSupport f →
      (Function.support f ⊆ Metric.closedBall 0 A) →
      (∀ x, |f x| ≤ F) → (∀ x y, |f x - f y| ≤ H * ‖x - y‖ ^ α) →
      ∃ j : GaussianTilt.HolderSpace.Jet (KernelSpace n) ℝ (convex_closedBall (0 : KernelSpace n) R) α,
        ‖j‖ ≤ C ∧
        (∀ x : Metric.closedBall (0 : KernelSpace n) R,
          GaussianTilt.HolderSpace.value (Metric.closedBall (0 : KernelSpace n) R) ℝ α
            (GaussianTilt.HolderSpace.jetValue (KernelSpace n) ℝ (convex_closedBall (0 : KernelSpace n) R) α j) x = newtonianPotential f x) ∧
        (∀ x : Metric.closedBall (0 : KernelSpace n) R,
          GaussianTilt.HolderSpace.value (Metric.closedBall (0 : KernelSpace n) R) (KernelSpace n →L[ℝ] ℝ) α
            (GaussianTilt.HolderSpace.jetFirst (KernelSpace n) ℝ (convex_closedBall (0 : KernelSpace n) R) α j) x = fderiv ℝ (newtonianPotential f) x) ∧
        (∀ x : Metric.closedBall (0 : KernelSpace n) R,
          GaussianTilt.HolderSpace.value (Metric.closedBall (0 : KernelSpace n) R) (KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ) α
            (GaussianTilt.HolderSpace.jetSecond (KernelSpace n) ℝ (convex_closedBall (0 : KernelSpace n) R) α j) x = fderiv ℝ (fderiv ℝ (newtonianPotential f)) x) := by
  obtain ⟨Ch, hCh, hholder⟩ := exists_newtonianPotential_secondFrechet_holder (n := n) hα hα1
  let U := F * newtonianLocalMass n (R + 1 + A)
  let L := Ch * (F + H)
  let B := 16 * U + 3 * L + 1
  have hU : 0 ≤ U := mul_nonneg hF (newtonianLocalMass_nonneg _ _)
  have hL : 0 ≤ L := mul_nonneg hCh.le (add_nonneg hF hH)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨2 * B, by positivity, ?_⟩
  intro f hf hfc hfs hfb hfh
  let P := newtonianPotential f
  have hP := smooth_newtonianPotential hf hfc
  have hP2 := contDiff_infty.mp hP 2
  have hsize : ∀ x : KernelSpace n, ‖x‖ ≤ R + 1 → |P x| ≤ U :=
    fun x hx => newtonianPotential_local_bound hF hfb hfs hx
  have hloc : ∀ x y : KernelSpace n, ‖x - y‖ ≤ 1 →
      ‖fderiv ℝ (fderiv ℝ P) x - fderiv ℝ (fderiv ℝ P) y‖ ≤ L * ‖x - y‖ ^ α :=
    hholder f hf hfc F H hF hH hfb hfh
  have hhalf : (1 / 2 : ℝ) ^ α ≤ 1 := Real.rpow_le_one (by norm_num) (by norm_num) hα.le
  have hsmall (x : KernelSpace n) (hx : x ∈ Metric.closedBall 0 R) :
      (∀ y ∈ Metric.closedBall x (1 / 2 : ℝ), |P y| ≤ U) ∧
      (∀ y ∈ Metric.closedBall x (1 / 2 : ℝ), ∀ z ∈ Metric.closedBall x (1 / 2 : ℝ),
        ‖fderiv ℝ (fderiv ℝ P) y - fderiv ℝ (fderiv ℝ P) z‖ ≤ L * ‖y - z‖ ^ α) := by
    have hxn : ‖x‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    constructor
    · intro y hy
      apply hsize
      have hyn : ‖y - x‖ ≤ 1 / 2 := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hy
      have ht : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by simpa only [sub_zero] using norm_sub_le_norm_sub_add_norm_sub y x 0
      linarith
    · intro y hy z hz
      apply hloc
      have hyn : ‖y - x‖ ≤ 1 / 2 := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hy
      have hzn : ‖x - z‖ ≤ 1 / 2 := by simpa only [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hz
      have ht := norm_sub_le_norm_sub_add_norm_sub y x z
      linarith
  have hPbound : ∀ x ∈ Metric.closedBall (0 : KernelSpace n) R, ‖P x‖ ≤ B := by
    intro x hx
    have hx' : ‖x‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    have hb := hsize x (by linarith)
    rw [Real.norm_eq_abs]
    exact hb.trans (by dsimp [B]; linarith)
  have hDbound : ∀ x ∈ Metric.closedBall (0 : KernelSpace n) R, ‖fderiv ℝ P x‖ ≤ B := by
    intro x hx
    have hb := gradient_interpolation_on_closedBall hP2 (by norm_num : (0 : ℝ) < 1 / 2) hU hL hα.le (hsmall x hx).1 (hsmall x hx).2
    norm_num at hb
    dsimp [B]
    nlinarith [mul_le_mul_of_nonneg_left hhalf (show 0 ≤ L / 2 by positivity)]
  have hHbound : ∀ x ∈ Metric.closedBall (0 : KernelSpace n) R, ‖fderiv ℝ (fderiv ℝ P) x‖ ≤ B := by
    intro x hx
    have hb := hessian_interpolation_on_closedBall hP2 (by norm_num : (0 : ℝ) < 1 / 2) hU hL hα.le (hsmall x hx).1 (hsmall x hx).2
    norm_num at hb
    dsimp [B]
    nlinarith [mul_le_mul_of_nonneg_left hhalf (show 0 ≤ 2 * L by positivity)]
  have hpLip : ∀ x ∈ Metric.closedBall (0 : KernelSpace n) R, ∀ y ∈ Metric.closedBall 0 R,
      ‖P x - P y‖ ≤ B * dist x y := by
    intro x hx y hy
    rw [dist_eq_norm]
    exact (convex_closedBall (0 : KernelSpace n) R).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hP.differentiable (by simp) z) hDbound hy hx
  have hdLip : ∀ x ∈ Metric.closedBall (0 : KernelSpace n) R, ∀ y ∈ Metric.closedBall 0 R,
      ‖fderiv ℝ P x - fderiv ℝ P y‖ ≤ B * dist x y := by
    intro x hx y hy
    rw [dist_eq_norm]
    exact (convex_closedBall (0 : KernelSpace n) R).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => (hP.fderiv_right (m := ∞) (by simp)).differentiable (by simp) z) hHbound hy hx
  have hpHolder := holder_bound_on_of_lipschitz_and_bound hB hα.le hα1.le hPbound hpLip
  have hdHolder := holder_bound_on_of_lipschitz_and_bound hB hα.le hα1.le hDbound hdLip
  have hhHolder : ∀ x ∈ Metric.closedBall (0 : KernelSpace n) R, ∀ y ∈ Metric.closedBall 0 R,
      ‖fderiv ℝ (fderiv ℝ P) x - fderiv ℝ (fderiv ℝ P) y‖ ≤ 2 * B * dist x y ^ α := by
    intro x hx y hy
    by_cases hxy : ‖x - y‖ ≤ 1
    · exact (hloc x y hxy).trans (by
        rw [dist_eq_norm]
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (norm_nonneg _) _)
        dsimp [B]; linarith)
    · have hn := (norm_sub_le (fderiv ℝ (fderiv ℝ P) x) (fderiv ℝ (fderiv ℝ P) y)).trans
        (show ‖fderiv ℝ (fderiv ℝ P) x‖ + ‖fderiv ℝ (fderiv ℝ P) y‖ ≤ 2 * B by linarith [hHbound x hx, hHbound y hy])
      apply hn.trans
      apply le_mul_of_one_le_right (by positivity)
      exact Real.one_le_rpow (by rw [dist_eq_norm]; exact le_of_lt (lt_of_not_ge hxy)) hα.le
  obtain ⟨j, hj₀, hj₁, hj₂⟩ := GaussianTilt.HolderSpace.exists_jet_of_smooth
    (convex_closedBall (0 : KernelSpace n) R) (isCompact_closedBall 0 R) hα.le hα1.le P hP
  refine ⟨j, ?_, hj₀, hj₁, hj₂⟩
  apply GaussianTilt.HolderSpace.norm_jet_le_of_field_norms
  · apply GaussianTilt.HolderSpace.norm_le_of_value_bounds (by positivity)
    · intro x; rw [hj₀]; exact (hPbound x x.2).trans (by linarith)
    · intro x y; rw [hj₀, hj₀]; exact hpHolder x x.2 y y.2
  · apply GaussianTilt.HolderSpace.norm_le_of_value_bounds (by positivity)
    · intro x; rw [hj₁]; exact (hDbound x x.2).trans (by linarith)
    · intro x y; rw [hj₁, hj₁]; exact hdHolder x x.2 y y.2
  · apply GaussianTilt.HolderSpace.norm_le_of_value_bounds (by positivity)
    · intro x; rw [hj₂]; exact (hHbound x x.2).trans (by linarith)
    · intro x y; rw [hj₂, hj₂]; exact hhHolder x x.2 y y.2

end GaussianTilt.MomentMapLinearDirichlet
