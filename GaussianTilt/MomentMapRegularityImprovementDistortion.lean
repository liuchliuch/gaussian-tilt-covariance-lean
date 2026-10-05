import GaussianTilt.MomentMapRegularityImprovementNormalization

/-! # Genuine control of accumulated affine normalization

Actual near-identity normalization maps are composed in their true order.
Both forward and inverse distortion are bounded by finite exponential sums,
and therefore uniformly by the derived geometric summability budget.
-/
noncomputable section
open Set
open scoped BigOperators
namespace GaussianTilt.MomentMapRegularity
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 1000
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def normalizationProduct (L : ℕ → X ≃L[ℝ] X) : ℕ → X ≃L[ℝ] X
  | 0 => ContinuousLinearEquiv.refl ℝ X
  | k+1 => (L k).trans (normalizationProduct L k)

lemma norm_le_exp_of_sub_identity_le (T : X →L[ℝ] X) {δ : ℝ} (hT : ‖T-1‖ ≤ δ) :
    ‖T‖ ≤ Real.exp δ := by
  have hnorm : ‖T‖ ≤ ‖T-1‖+‖(1 : X →L[ℝ] X)‖ := by
    simpa only [sub_add_cancel] using norm_add_le (T-1) (1 : X →L[ℝ] X)
  have h1 : ‖(1 : X →L[ℝ] X)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  exact (show ‖T‖ ≤ δ+1 by linarith).trans (by simpa [add_comm] using Real.add_one_le_exp δ)

/-- The actual forward and inverse products obey the same exponential
budget; no bounded affine distortion is assumed. -/
theorem normalizationProduct_norms_le_exp_sum (L : ℕ → X ≃L[ℝ] X) (δ : ℕ → ℝ)
    (hL : ∀ k, ‖(L k : X →L[ℝ] X)-1‖ ≤ δ k)
    (hI : ∀ k, ‖((L k).symm : X →L[ℝ] X)-1‖ ≤ δ k) (k : ℕ) :
    ‖(normalizationProduct L k : X →L[ℝ] X)‖ ≤ Real.exp (∑ i ∈ Finset.range k, δ i) ∧
      ‖((normalizationProduct L k).symm : X →L[ℝ] X)‖ ≤ Real.exp (∑ i ∈ Finset.range k, δ i) := by
  induction k with
  | zero =>
    constructor <;> simpa only [normalizationProduct,Finset.range_zero,Finset.sum_empty,Real.exp_zero]
      using (ContinuousLinearMap.norm_id_le (𝕜:=ℝ) (E:=X))
  | succ k ih =>
    have hLk := norm_le_exp_of_sub_identity_le (L k : X →L[ℝ] X) (hL k)
    have hIk := norm_le_exp_of_sub_identity_le ((L k).symm : X →L[ℝ] X) (hI k)
    rw [Finset.sum_range_succ,Real.exp_add]
    constructor
    · change ‖(normalizationProduct L k : X →L[ℝ] X)*(L k : X →L[ℝ] X)‖ ≤ _
      exact (norm_mul_le _ _).trans (mul_le_mul ih.1 hLk (norm_nonneg _) (Real.exp_pos _).le)
    · change ‖((L k).symm : X →L[ℝ] X)*((normalizationProduct L k).symm : X →L[ℝ] X)‖ ≤ _
      exact (norm_mul_le _ _).trans ((mul_le_mul hIk ih.2 (norm_nonneg _) (Real.exp_pos _).le).trans_eq (mul_comm _ _))

/-- A genuinely geometric near-identity rate implies a uniform forward and
inverse affine bound, with an explicit total distortion budget. -/
theorem normalizationProduct_norms_le_geometric_budget (L : ℕ → X ≃L[ℝ] X)
    {a q : ℝ} (ha : 0 ≤ a) (hq : 0 ≤ q) (hq1 : q < 1)
    (hL : ∀ k, ‖(L k : X →L[ℝ] X)-1‖ ≤ a*q^k)
    (hI : ∀ k, ‖((L k).symm : X →L[ℝ] X)-1‖ ≤ a*q^k) (k : ℕ) :
    ‖(normalizationProduct L k : X →L[ℝ] X)‖ ≤ Real.exp (a/(1-q)) ∧
      ‖((normalizationProduct L k).symm : X →L[ℝ] X)‖ ≤ Real.exp (a/(1-q)) := by
  have hs : (∑ i ∈ Finset.range k, a*q^i) ≤ a/(1-q) := by
    have hh := sum_le_hasSum (Finset.range k) (fun i _ => mul_nonneg ha (pow_nonneg hq i))
      ((hasSum_geometric_of_lt_one hq hq1).mul_left a)
    simpa only [div_eq_mul_inv] using hh
  have hh := normalizationProduct_norms_le_exp_sum L (fun k => a*q^k) hL hI k
  exact ⟨hh.1.trans (Real.exp_le_exp.mpr hs),hh.2.trans (Real.exp_le_exp.mpr hs)⟩

end GaussianTilt.MomentMapRegularity
