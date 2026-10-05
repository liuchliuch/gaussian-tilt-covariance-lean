import GaussianTilt.MomentMapEllipticFundamentalSolutionHessianGreen
import GaussianTilt.MomentMapSchauderNewtonianOperator
import GaussianTilt.MomentMapSchauderNewtonianTail

/-!
# Convergence of the regularized Hessian kernels

The actual regularized Hessians have a common inverse-dimension bound.
Subtracting the source value removes the singularity, allowing genuine
Bochner dominated convergence to the compensated Newtonian operator.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapElliptic
open GaussianTilt.MomentMapSchauder
variable {n : ℕ}

def regularizedHessianEntry (a : ℝ) (i j : Fin n) (x : KernelSpace n) : ℝ :=
  directionalHessian (regularizedNewtonian n a) x (EuclideanSpace.basisFun (Fin n) ℝ i)
    (EuclideanSpace.basisFun (Fin n) ℝ j)

lemma regularizedHessianEntry_formula {a : ℝ} {x : KernelSpace n}
    (ht : 0 < a + ‖x‖ ^ 2) (i j : Fin n) :
    regularizedHessianEntry a i j x =
      -(2 * (n : ℝ)) * (a + ‖x‖ ^ 2) ^ (-((n : ℝ) + 2) / 2) * x i * x j +
        2 * (a + ‖x‖ ^ 2) ^ (-(n : ℝ) / 2) * (if i = j then 1 else 0) := by
  rw [regularizedHessianEntry, directionalHessian_regularizedNewtonian ht]
  have hb := (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal
  rw [orthonormal_iff_ite] at hb
  rw [hb i j, EuclideanSpace.inner_basisFun_real, EuclideanSpace.inner_basisFun_real]

lemma continuous_regularizedHessianEntry {a : ℝ} (ha : 0 < a) (i j : Fin n) :
    Continuous (regularizedHessianEntry a i j) :=
  continuous_directionalHessian (contDiff_regularizedNewtonian ha) _ _

/-- The regularized Hessian has a singularity bound independent of its
regularization parameter, including in the logarithmic dimension. -/
theorem regularized_directionalHessian_bound {a : ℝ} (ha : 0 ≤ a)
    {x : KernelSpace n} (hx : x ≠ 0) {v w : KernelSpace n}
    (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    |directionalHessian (regularizedNewtonian n a) x v w| ≤
      (2 * ((n : ℝ) + 1)) * ‖x‖ ^ (-(n : ℝ)) := by
  let S := ‖x‖ ^ 2
  let T := a + S
  have hS : 0 < S := sq_pos_of_pos (norm_pos_iff.mpr hx)
  have hT : 0 < T := by dsimp [T]; linarith
  have hST : S ≤ T := by dsimp [T]; linarith
  have hvx := abs_inner_le_norm_of_norm_le_one (x := x) hv
  have hwx := abs_inner_le_norm_of_norm_le_one (x := x) hw
  have hvw : |inner ℝ v w| ≤ 1 := (abs_inner_le_norm_of_norm_le_one hw).trans hv
  have hprod : |inner ℝ x v| * |inner ℝ x w| ≤ T :=
    ((mul_le_mul hvx hwx (abs_nonneg _) (norm_nonneg x)).trans_eq (sq ‖x‖).symm).trans hST
  have hp : T ^ (-((n : ℝ) + 2) / 2) * T = T ^ (-(n : ℝ) / 2) := by
    rw [← Real.rpow_add_one hT.ne']
    congr 1
    ring
  have hdec : T ^ (-(n : ℝ) / 2) ≤ S ^ (-(n : ℝ) / 2) :=
    Real.rpow_le_rpow_of_nonpos hS hST (by have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n; linarith)
  rw [directionalHessian_regularizedNewtonian hT]
  calc
    _ ≤ |-(2 * (n : ℝ)) * T ^ (-((n : ℝ) + 2) / 2) * inner ℝ x v * inner ℝ x w| +
        |2 * T ^ (-(n : ℝ) / 2) * inner ℝ v w| := abs_add_le _ _
    _ = (2 * (n : ℝ)) * T ^ (-((n : ℝ) + 2) / 2) * (|inner ℝ x v| * |inner ℝ x w|) +
        2 * T ^ (-(n : ℝ) / 2) * |inner ℝ v w| := by
      simp only [abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ)),
        abs_of_nonneg (show 0 ≤ (n : ℝ) from Nat.cast_nonneg n), abs_of_nonneg (Real.rpow_nonneg hT.le _)]
      ring
    _ ≤ (2 * (n : ℝ)) * T ^ (-((n : ℝ) + 2) / 2) * T + 2 * T ^ (-(n : ℝ) / 2) * 1 :=
      add_le_add (mul_le_mul_of_nonneg_left hprod (by positivity))
        (mul_le_mul_of_nonneg_left hvw (by positivity))
    _ = (2 * ((n : ℝ) + 1)) * T ^ (-(n : ℝ) / 2) := by rw [mul_assoc _ _ T, hp]; ring
    _ ≤ (2 * ((n : ℝ) + 1)) * S ^ (-(n : ℝ) / 2) := mul_le_mul_of_nonneg_left hdec (by positivity)
    _ = _ := by rw [show S = ‖x‖ ^ 2 from rfl, squaredNorm_rpow]; congr 2; ring

lemma regularizedHessianEntry_bound {a : ℝ} (ha : 0 ≤ a) {x : KernelSpace n}
    (hx : x ≠ 0) (i j : Fin n) :
    |regularizedHessianEntry a i j x| ≤ (2 * ((n : ℝ) + 1)) * ‖x‖ ^ (-(n : ℝ)) :=
  regularized_directionalHessian_bound ha hx
    ((EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.norm_eq_one i).le
    ((EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.norm_eq_one j).le

lemma tendsto_regularizedHessianEntry {x : KernelSpace n} (hx : x ≠ 0) (i j : Fin n) :
    Tendsto (fun c : ℝ => regularizedHessianEntry ((c ^ 2)⁻¹) i j x) atTop
      (𝓝 (newtonianHessianEntry i j x)) := by
  have hS : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  have ht : Tendsto (fun c : ℝ => (c ^ 2)⁻¹ + ‖x‖ ^ 2) atTop (𝓝 (‖x‖ ^ 2)) := by
    simpa only [zero_add] using tendsto_inv_sq_atTop.add_const (‖x‖ ^ 2)
  have hp (t : ℝ) : Tendsto (fun c : ℝ => ((c ^ 2)⁻¹ + ‖x‖ ^ 2) ^ t) atTop (𝓝 ((‖x‖ ^ 2) ^ t)) :=
    (continuousAt_id.rpow_const (Or.inl hS.ne')).tendsto.comp ht
  have hh := ((((hp (-((n : ℝ) + 2) / 2)).const_mul (-(2 * (n : ℝ)))).mul_const (x i)).mul_const (x j)).add
    (((hp (-(n : ℝ) / 2)).const_mul 2).mul_const (if i = j then 1 else 0))
  convert hh using 1
  · funext c
    exact regularizedHessianEntry_formula (by positivity) i j
  · rw [newtonianHessianEntry_formula hx]

lemma standardRadialCutoff_one {t : ℝ} (ht : |t| ≤ 1) : standardRadialCutoff t = 1 := by
  apply (default : ContDiffBump (0 : ℝ)).one_of_mem_closedBall
  simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using ht

lemma standardRadialCutoff_norm_compact (n : ℕ) :
    HasCompactSupport (fun x : KernelSpace n => standardRadialCutoff ‖x‖) := by
  apply HasCompactSupport.intro' (isCompact_closedBall 0 2) Metric.isClosed_closedBall
  intro x hx
  apply standardRadialCutoff_zero
  have hh : ¬‖x‖ ≤ 2 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  exact lt_of_not_ge hh

/-- Dominated convergence for the compensated local Hessian integral.
The subtracted source value cancels the genuine inverse-dimension
singularity; the dominating radial power is proved integrable. -/
theorem tendsto_regularized_compensated_hessian [NeZero n]
    {f : KernelSpace n → ℝ} (hfm : Measurable f) {H α : ℝ} (hH : 0 ≤ H)
    (hα : 0 < α) (hαn : α < (n : ℝ))
    (hf : ∀ x y, |f x - f y| ≤ H * ‖x - y‖ ^ α) (i j : Fin n) :
    Tendsto (fun c : ℝ => ∫ x, standardRadialCutoff ‖x‖ * regularizedHessianEntry ((c ^ 2)⁻¹) i j x * (f x - f 0))
      atTop (𝓝 (∫ x, cutoffNewtonianHessian standardRadialCutoff i j x * (f x - f 0))) := by
  let M := (Metric.closedBall (0 : KernelSpace n) 2).indicator
    (fun x => (2 * ((n : ℝ) + 1) * H) * ‖x‖ ^ (α - (n : ℝ)))
  have hMi : Integrable M := by
    rw [integrable_indicator_iff Metric.isClosed_closedBall.measurableSet]
    apply Integrable.const_mul
    have hh := (holderKernel_integrable_and_scale (μ := (volume : Measure (KernelSpace n))) hα
      (by simpa only [KernelSpace, finrank_euclideanSpace_fin] using hαn) (R := 2) (by norm_num)).1
    simpa only [KernelSpace, finrank_euclideanSpace_fin] using hh
  have hne : ∀ᵐ x : KernelSpace n ∂volume, x ≠ 0 := by apply ae_iff.mpr; simp
  apply tendsto_integral_filter_of_dominated_convergence M
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
    exact (((standardRadialCutoff_contDiff.continuous.comp continuous_norm).measurable.mul
      (continuous_regularizedHessianEntry (by positivity) i j).measurable).mul
      (hfm.sub measurable_const)).aestronglyMeasurable
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
    filter_upwards [hne] with x hx
    by_cases hxB : x ∈ Metric.closedBall (0 : KernelSpace n) 2
    · dsimp only [M]
      rw [indicator_of_mem hxB, Real.norm_eq_abs, abs_mul, abs_mul]
      have hχ := standardRadialCutoff_abs_le_one ‖x‖
      have hk := regularizedHessianEntry_bound (by positivity : 0 ≤ (c ^ 2)⁻¹) hx i j
      have hf0 := hf x 0
      simp only [sub_zero] at hf0
      have hprod := mul_le_mul (mul_le_mul hχ hk (abs_nonneg _) (by norm_num)) hf0
        (abs_nonneg _) (by positivity)
      apply hprod.trans_eq
      rw [one_mul]
      have hp : ‖x‖ ^ (-(n : ℝ)) * ‖x‖ ^ α = ‖x‖ ^ (α - (n : ℝ)) := by
        rw [← Real.rpow_add (norm_pos_iff.mpr hx)]
        congr 1
        ring
      calc
        _ = (2 * ((n : ℝ) + 1) * H) * (‖x‖ ^ (-(n : ℝ)) * ‖x‖ ^ α) := by ring
        _ = _ := by rw [hp]
    · have hχ0 : standardRadialCutoff ‖x‖ = 0 := standardRadialCutoff_zero (by
        simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hxB)
      simp only [hχ0, zero_mul, norm_zero, M, indicator_of_notMem hxB, le_refl]
  · exact hMi
  · filter_upwards [hne] with x hx
    have hh := ((tendsto_regularizedHessianEntry hx i j).const_mul (standardRadialCutoff ‖x‖)).mul_const (f x - f 0)
    exact hh

/-- The complementary regularized Hessian pairing converges by a uniform
bounded multiplier. The cutoff removes the origin before the limit. -/
theorem tendsto_regularized_hessian_tail [NeZero n] {f : KernelSpace n → ℝ}
    (hf : Continuous f) (hs : HasCompactSupport f) (i j : Fin n) :
    Tendsto (fun c : ℝ => ∫ x, (1 - standardRadialCutoff ‖x‖) *
      regularizedHessianEntry ((c ^ 2)⁻¹) i j x * f x) atTop
      (𝓝 (∫ x, standardNewtonianTail i j x * f x)) := by
  let M := fun x : KernelSpace n => (4 * ((n : ℝ) + 1)) * ‖f x‖
  have hMi : Integrable M := (hf.integrable_of_hasCompactSupport hs).norm.const_mul _
  have hne : ∀ᵐ x : KernelSpace n ∂volume, x ≠ 0 := by apply ae_iff.mpr; simp
  apply tendsto_integral_filter_of_dominated_convergence M
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
    exact (((continuous_const.sub (standardRadialCutoff_contDiff.continuous.comp continuous_norm)).mul
      (continuous_regularizedHessianEntry (by positivity) i j)).mul hf).aestronglyMeasurable
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
    filter_upwards [hne] with x hx
    by_cases hx1 : ‖x‖ ≤ 1
    · have hχ : standardRadialCutoff ‖x‖ = 1 := standardRadialCutoff_one (by simpa only [abs_of_nonneg (norm_nonneg x)] using hx1)
      simp only [hχ, sub_self, zero_mul, norm_zero]
      dsimp [M]
      positivity
    · have hr : 1 ≤ ‖x‖ := (lt_of_not_ge hx1).le
      have hχ : |1 - standardRadialCutoff ‖x‖| ≤ 2 := by
        apply (abs_sub _ _).trans
        have hh := standardRadialCutoff_abs_le_one ‖x‖
        norm_num only [abs_one]
        linarith
      have hpow : ‖x‖ ^ (-(n : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hr (by have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n; linarith)
      have hk : |regularizedHessianEntry ((c ^ 2)⁻¹) i j x| ≤ 2 * ((n : ℝ) + 1) :=
        (regularizedHessianEntry_bound (by positivity) hx i j).trans
          (by simpa using mul_le_mul_of_nonneg_left hpow (show 0 ≤ 2 * ((n : ℝ) + 1) by positivity))
      rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_right (mul_le_mul hχ hk (abs_nonneg _) (by norm_num)) (norm_nonneg _)).trans_eq (by dsimp [M]; ring)
  · exact hMi
  · filter_upwards [hne] with x hx
    exact ((tendsto_regularizedHessianEntry hx i j).const_mul (1 - standardRadialCutoff ‖x‖)).mul_const (f x)

end GaussianTilt.MomentMapElliptic
