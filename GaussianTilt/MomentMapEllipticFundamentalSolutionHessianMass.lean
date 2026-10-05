import GaussianTilt.MomentMapEllipticFundamentalSolutionHessianLimit

/-!
# The concentrated local part of the Newtonian Hessian

Measured orthogonal symmetry makes all diagonal regularized Hessian masses
equal and all off-diagonal masses zero. Their trace is the actual probability
approximation already proved. This derives the local Kronecker correction in
the singular-integral Hessian representation.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapElliptic
open GaussianTilt.MomentMapSchauder
variable {n : ℕ}

def weightedRegularizedHessian (a : ℝ) (i j : Fin n) (x : KernelSpace n) : ℝ :=
  standardRadialCutoff ‖x‖ * regularizedHessianEntry a i j x

lemma integrable_weightedRegularizedHessian {a : ℝ} (ha : 0 < a) (i j : Fin n) :
    Integrable (weightedRegularizedHessian a i j) :=
  integrable_compact_mul (standardRadialCutoff_contDiff.continuous.comp continuous_norm)
    (standardRadialCutoff_norm_compact n) (continuous_regularizedHessianEntry ha i j)

lemma integral_weightedRegularizedHessian_offDiagonal {a : ℝ} (ha : 0 < a)
    (i j : Fin n) (hij : i ≠ j) : (∫ x, weightedRegularizedHessian a i j x) = 0 := by
  classical
  let T : KernelSpace n ≃ₗᵢ[ℝ] KernelSpace n := LinearIsometryEquiv.piLpCongrRight 2
    (fun k => if k = i then (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ)
      else LinearIsometryEquiv.refl ℝ ℝ)
  have hTi (x : KernelSpace n) : T x i = -x i := by simp [T, LinearIsometryEquiv.piLpCongrRight_apply]
  have hTj (x : KernelSpace n) : T x j = x j := by simp [T, LinearIsometryEquiv.piLpCongrRight_apply, Ne.symm hij]
  have hchange := T.measurePreserving.integral_comp T.toHomeomorph.measurableEmbedding
    (weightedRegularizedHessian a i j)
  have he : (fun x => weightedRegularizedHessian a i j (T x)) =
      (fun x => -(weightedRegularizedHessian a i j x)) := by
    funext x
    simp only [weightedRegularizedHessian, regularizedHessianEntry_formula (by positivity : 0 < a + ‖T x‖ ^ 2),
      regularizedHessianEntry_formula (by positivity : 0 < a + ‖x‖ ^ 2), T.norm_map, hTi, hTj, if_neg hij, mul_zero, add_zero]
    ring
  rw [he, integral_neg] at hchange
  linarith

lemma integral_weightedRegularizedHessian_diagonal_eq {a : ℝ} (ha : 0 < a) (i j : Fin n) :
    (∫ x, weightedRegularizedHessian a i i x) = ∫ x, weightedRegularizedHessian a j j x := by
  classical
  let T : KernelSpace n ≃ₗᵢ[ℝ] KernelSpace n := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j)
  have hTi (x : KernelSpace n) : T x i = x j := by
    change x ((Equiv.swap i j).symm i) = x j
    rw [Equiv.symm_swap, Equiv.swap_apply_left]
  have hchange := T.measurePreserving.integral_comp T.toHomeomorph.measurableEmbedding
    (weightedRegularizedHessian a i i)
  have he : (fun x => weightedRegularizedHessian a i i (T x)) = weightedRegularizedHessian a j j := by
    funext x
    simp only [weightedRegularizedHessian, regularizedHessianEntry_formula (by positivity : 0 < a + ‖T x‖ ^ 2),
      regularizedHessianEntry_formula (by positivity : 0 < a + ‖x‖ ^ 2), T.norm_map, hTi, if_true]
  rw [he] at hchange
  exact hchange.symm

lemma integral_weightedRegularizedHessian_diagonal_trace [NeZero n] {a : ℝ}
    (ha : 0 < a) (i : Fin n) :
    (∫ x, weightedRegularizedHessian a i i x) = (n : ℝ)⁻¹ *
      ∫ x, standardRadialCutoff ‖x‖ * kernelLaplacian (regularizedNewtonian n a) x := by
  have hsum : (∫ x, standardRadialCutoff ‖x‖ * kernelLaplacian (regularizedNewtonian n a) x) =
      ∑ k : Fin n, ∫ x, weightedRegularizedHessian a k k x := by
    simp only [kernelLaplacian, Finset.mul_sum]
    exact integral_finset_sum Finset.univ (fun k _ => integrable_weightedRegularizedHessian ha k k)
  have heq (k : Fin n) : (∫ x, weightedRegularizedHessian a k k x) =
      ∫ x, weightedRegularizedHessian a i i x := integral_weightedRegularizedHessian_diagonal_eq ha k i
  simp_rw [heq] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  rw [hsum, inv_mul_cancel_left₀ (Nat.cast_ne_zero.mpr (NeZero.ne n))]

lemma tendsto_standard_weighted_regularized_laplacian :
    Tendsto (fun c : ℝ => ∫ x : KernelSpace n, standardRadialCutoff ‖x‖ *
      kernelLaplacian (regularizedNewtonian n ((c ^ 2)⁻¹)) x) atTop
      (𝓝 (2 * (n : ℝ) * fundamentalApproxMass n)) := by
  let G : KernelSpace n → ℝ := fun x => standardRadialCutoff ‖x‖
  have hGc : Continuous G := standardRadialCutoff_contDiff.continuous.comp continuous_norm
  have hGs : HasCompactSupport G := standardRadialCutoff_norm_compact n
  have hG0 : G 0 = 1 := by
    change standardRadialCutoff ‖(0 : KernelSpace n)‖ = 1
    rw [norm_zero]
    exact standardRadialCutoff_one (by simp)
  have happrox := fundamentalApproxDensity_approximate_identity (x₀ := 0)
    (hGc.integrable_of_hasCompactSupport hGs) hGc.continuousAt
  have heven (x : KernelSpace n) : fundamentalApproxDensity n (-x) = fundamentalApproxDensity n x := by
    simp only [fundamentalApproxDensity, fundamentalApproxBase, norm_neg]
  have hpeak : Tendsto (fun c : ℝ => ∫ x, (c ^ n * fundamentalApproxDensity n (c • x)) * G x)
      atTop (𝓝 1) := by
    simpa only [zero_sub, smul_neg, heven, hG0] using happrox
  have ht := hpeak.const_mul (2 * (n : ℝ) * fundamentalApproxMass n)
  simp only [mul_one] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
  simp only [kernelLaplacian_regularized_eq_approxDensity hc]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by dsimp [G]; ring)

/-- The local Hessian mass is derived from its trace and orthogonal
symmetry. This is the actual delta correction, not a normalization premise. -/
theorem tendsto_weightedRegularizedHessian_mass [NeZero n] (i j : Fin n) :
    Tendsto (fun c : ℝ => ∫ x, weightedRegularizedHessian ((c ^ 2)⁻¹) i j x) atTop
      (𝓝 (if i = j then 2 * fundamentalApproxMass n else 0)) := by
  by_cases hij : i = j
  · subst j
    simp only [if_true]
    have ht := (tendsto_standard_weighted_regularized_laplacian (n := n)).const_mul ((n : ℝ)⁻¹)
    have he : (n : ℝ)⁻¹ * (2 * (n : ℝ) * fundamentalApproxMass n) = 2 * fundamentalApproxMass n := by
      field_simp [Nat.cast_ne_zero.mpr (NeZero.ne n)]
    rw [he] at ht
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
    exact (integral_weightedRegularizedHessian_diagonal_trace (by positivity) i).symm
  · simp only [if_neg hij]
    apply (tendsto_const_nhds (x := (0 : ℝ))).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
    exact (integral_weightedRegularizedHessian_offDiagonal (by positivity) i j hij).symm

end GaussianTilt.MomentMapElliptic
