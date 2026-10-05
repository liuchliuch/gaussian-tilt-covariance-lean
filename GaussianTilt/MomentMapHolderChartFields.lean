import GaussianTilt.MomentMapHolderChartBounds

/-! # Actual curved-chart jet fields and fixed quantitative bounds -/
noncomputable section
set_option maxHeartbeats 2000000
open Set Filter
open scoped Topology
namespace GaussianTilt.HolderSpace
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def chartFirst (D : F → F →L[ℝ] ℝ) (ψ : E → F) (x : E) : E →L[ℝ] ℝ :=
  (D (ψ x)).comp (fderiv ℝ ψ x)
def chartSecond (D : F → F →L[ℝ] ℝ) (H : F → F →L[ℝ] F →L[ℝ] ℝ)
    (ψ : E → F) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (H (ψ x)).bilinearComp (fderiv ℝ ψ x) (fderiv ℝ ψ x) +
    postcomposeBilinear (D (ψ x)) (fderiv ℝ (fderiv ℝ ψ) x)

lemma continuousOn_of_holder_bound_general {V : Type*} [NormedAddCommGroup V]
    {T : Set E} {G : E → V} {α C : ℝ} (hα : 0 < α)
    (hG : ∀ x ∈ T, ∀ y ∈ T, ‖G x-G y‖ ≤ C*‖x-y‖^α) : ContinuousOn G T := by
  rw [continuousOn_iff_continuous_restrict]
  apply continuous_iff_continuousAt.mpr
  intro x
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht : Tendsto (fun y : T => C*‖(y : E)-x‖^α) (𝓝 x) (𝓝 0) := by
    convert (continuous_const.mul ((Real.continuous_rpow_const hα.le).comp
      ((continuous_subtype_val.sub continuous_const).norm))).tendsto x using 1
    simp [Real.zero_rpow hα.ne']
  exact squeeze_zero (fun y => norm_nonneg _) (fun y => hG y y.2 x x.2) ht

theorem chart_first_bounds {T : Set E} {α K N L : ℝ}
    (hN : 0 ≤ N) (hL : 0 ≤ L) {ψ : E → F} (hψ : SmoothChartBounds ψ T α K)
    (D : F → F →L[ℝ] ℝ)
    (hD : ∀ x ∈ T, ‖D (ψ x)‖ ≤ N)
    (hDH : ∀ x ∈ T, ∀ y ∈ T, ‖D (ψ x)-D (ψ y)‖ ≤ N*L*‖x-y‖^α) :
    (∀ x ∈ T, ‖chartFirst D ψ x‖ ≤ N*K) ∧
    (∀ x ∈ T, ∀ y ∈ T, ‖chartFirst D ψ x-chartFirst D ψ y‖ ≤ N*(L*K+K)*‖x-y‖^α) := by
  constructor
  · intro x hx
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (hD x hx) (hψ.first_bound x hx) (norm_nonneg _) hN)
  · intro x hx y hy
    calc
      _ ≤ ‖D (ψ x)-D (ψ y)‖*‖fderiv ℝ ψ x‖+‖D (ψ y)‖*‖fderiv ℝ ψ x-fderiv ℝ ψ y‖ :=
        norm_clm_comp_sub_le _ _ _ _
      _ ≤ (N*L*‖x-y‖^α)*K+N*(K*‖x-y‖^α) := add_le_add
        (mul_le_mul (hDH x hx y hy) (hψ.first_bound x hx) (norm_nonneg _) (by positivity))
        (mul_le_mul (hD y hy) (hψ.first_holder x hx y hy) (norm_nonneg _) hN)
      _ = _ := by ring

theorem chart_second_bounds {T : Set E} {α K N L : ℝ}
    (hN : 0 ≤ N) (hL : 0 ≤ L) {ψ : E → F} (hψ : SmoothChartBounds ψ T α K)
    (D : F → F →L[ℝ] ℝ) (H : F → F →L[ℝ] F →L[ℝ] ℝ)
    (hD : ∀ x ∈ T, ‖D (ψ x)‖ ≤ N) (hH : ∀ x ∈ T, ‖H (ψ x)‖ ≤ N)
    (hDH : ∀ x ∈ T, ∀ y ∈ T, ‖D (ψ x)-D (ψ y)‖ ≤ N*L*‖x-y‖^α)
    (hHH : ∀ x ∈ T, ∀ y ∈ T, ‖H (ψ x)-H (ψ y)‖ ≤ N*L*‖x-y‖^α) :
    (∀ x ∈ T, ‖chartSecond D H ψ x‖ ≤ N*(K*K+K)) ∧
    (∀ x ∈ T, ∀ y ∈ T, ‖chartSecond D H ψ x-chartSecond D H ψ y‖ ≤
      N*(L*K*K+2*K*K+L*K+K)*‖x-y‖^α) := by
  have hK := hψ.nonneg
  constructor
  · intro x hx
    unfold chartSecond
    calc
      _ ≤ ‖(H (ψ x)).bilinearComp (fderiv ℝ ψ x) (fderiv ℝ ψ x)‖+
          ‖postcomposeBilinear (D (ψ x)) (fderiv ℝ (fderiv ℝ ψ) x)‖ := norm_add_le ((H (ψ x)).bilinearComp (fderiv ℝ ψ x) (fderiv ℝ ψ x)) (postcomposeBilinear (D (ψ x)) (fderiv ℝ (fderiv ℝ ψ) x))
      _ ≤ ‖H (ψ x)‖*‖fderiv ℝ ψ x‖*‖fderiv ℝ ψ x‖+
          ‖D (ψ x)‖*‖fderiv ℝ (fderiv ℝ ψ) x‖ :=
        add_le_add (norm_bilinearComp_two_le _ _ _) (norm_postcomposeBilinear_le _ _)
      _ ≤ N*K*K+N*K := add_le_add
        (mul_le_mul (mul_le_mul (hH x hx) (hψ.first_bound x hx) (norm_nonneg _) hN)
          (hψ.first_bound x hx) (norm_nonneg _) (mul_nonneg hN hK))
        (mul_le_mul (hD x hx) (hψ.second_bound x hx) (norm_nonneg (fderiv ℝ (fderiv ℝ ψ) x)) hN)
      _ = _ := by ring
  · intro x hx y hy
    let P := fderiv ℝ ψ x
    let Q := fderiv ℝ ψ y
    let Z := fderiv ℝ (fderiv ℝ ψ) x
    let W := fderiv ℝ (fderiv ℝ ψ) y
    have he : chartSecond D H ψ x-chartSecond D H ψ y =
        ((H (ψ x)).bilinearComp P P-(H (ψ y)).bilinearComp Q Q)+
        (postcomposeBilinear (D (ψ x)) Z-postcomposeBilinear (D (ψ y)) W) := by
      unfold chartSecond; dsimp only [P,Q,Z,W]; abel
    rw [he]
    calc
      _ ≤ ‖(H (ψ x)).bilinearComp P P-(H (ψ y)).bilinearComp Q Q‖+
          ‖postcomposeBilinear (D (ψ x)) Z-postcomposeBilinear (D (ψ y)) W‖ := norm_add_le ((H (ψ x)).bilinearComp P P-(H (ψ y)).bilinearComp Q Q) (postcomposeBilinear (D (ψ x)) Z-postcomposeBilinear (D (ψ y)) W)
      _ ≤ (‖H (ψ x)-H (ψ y)‖*‖P‖*‖P‖+‖H (ψ y)‖*‖P-Q‖*‖P‖+
          ‖H (ψ y)‖*‖Q‖*‖P-Q‖)+(‖D (ψ x)-D (ψ y)‖*‖Z‖+‖D (ψ y)‖*‖Z-W‖) :=
        add_le_add (norm_bilinearComp_diagonal_sub_le _ _ _ _) (norm_postcomposeBilinear_sub_le _ _ _ _)
      _ ≤ ((N*L*‖x-y‖^α)*K*K+N*(K*‖x-y‖^α)*K+N*K*(K*‖x-y‖^α))+
          ((N*L*‖x-y‖^α)*K+N*(K*‖x-y‖^α)) := by
        apply add_le_add
        · apply add_le_add
          · apply add_le_add
            · exact mul_le_mul (mul_le_mul (hHH x hx y hy) (hψ.first_bound x hx)
                (norm_nonneg _) (by positivity)) (hψ.first_bound x hx) (norm_nonneg _) (by positivity)
            · exact mul_le_mul (mul_le_mul (hH y hy) (hψ.first_holder x hx y hy)
                (norm_nonneg _) hN) (hψ.first_bound x hx) (norm_nonneg _) (by positivity)
          · exact mul_le_mul (mul_le_mul (hH y hy) (hψ.first_bound y hy)
              (norm_nonneg _) hN) (hψ.first_holder x hx y hy) (norm_nonneg _) (by positivity)
        · exact add_le_add
            (mul_le_mul (hDH x hx y hy) (hψ.second_bound x hx) (norm_nonneg Z) (by positivity))
            (mul_le_mul (hD y hy) (hψ.second_holder x hx y hy) (norm_nonneg (Z-W)) hN)
      _ = _ := by ring

end GaussianTilt.HolderSpace
