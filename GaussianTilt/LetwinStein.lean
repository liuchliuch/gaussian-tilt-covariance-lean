import GaussianTilt.LetwinTraceBound

/-! # Actual Stein identities supplied by the moment potential -/
noncomputable section
open MeasureTheory Matrix Set
open scoped BigOperators ContDiff
namespace GaussianTilt.Letwin

lemma integrable_comp_gradient {n : ℕ} {φ : CoordinateSpace n → ℝ}
    [IsFiniteMeasure (potentialMeasure φ)] (hφ : ContDiff ℝ 1 φ)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (hgrad : ∀ x, coordinateGradient φ x ∈ K)
    {g : CoordinateSpace n → ℝ} (hg : Continuous g) :
    Integrable (fun x => g (coordinateGradient φ x)) (potentialMeasure φ) := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  exact Integrable.of_bound (hg.comp (continuous_coordinateGradient hφ)).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => hC _ (hgrad x))

lemma integrable_hessian_gradient_test {n : ℕ} {φ g : CoordinateSpace n → ℝ}
    [IsFiniteMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ ∞ φ) (hg : ContDiff ℝ 1 g)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (hgrad : ∀ x, coordinateGradient φ x ∈ K)
    (S : ℝ) (hHb : ∀ x i j, |coordinateHessian φ x i j| ≤ S) (i j : Fin n) :
    Integrable (fun x => coordinateDerivative j g (coordinateGradient φ x) * coordinateHessian φ x j i)
      (potentialMeasure φ) := by
  have hHji : Integrable (fun x => coordinateHessian φ x j i) (potentialMeasure φ) :=
    Integrable.of_bound (smooth_coordinateHessian hφ j i).continuous.aestronglyMeasurable S
      (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hHb x j i)
  have hdg := (contDiff_coordinateDerivative hg (m := 0) (by norm_num) j).continuous
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hdg.continuousOn
  exact hHji.bdd_mul
    (hdg.comp (continuous_coordinateGradient (contDiff_infty.mp hφ 1))).aestronglyMeasurable
    ⟨C, fun x => hC _ (hgrad x)⟩

set_option maxHeartbeats 800000 in
/-- The Stein identity in the actual moment-map coupling X=∇φ(Y). It is
proved from A3 and the chain rule and does not assume a Stein kernel. Compact
support of g is unnecessary because the gradient image is compact. -/
theorem moment_map_stein_identity {n : ℕ} {φ g : CoordinateSpace n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ ∞ φ) (hg : ContDiff ℝ 1 g)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (hgrad : ∀ x, coordinateGradient φ x ∈ K)
    (S : ℝ) (hHb : ∀ x i j, |coordinateHessian φ x i j| ≤ S) (i : Fin n) :
    (∫ x, coordinateGradient φ x i * g (coordinateGradient φ x) ∂potentialMeasure φ) =
      ∫ x, ∑ j, coordinateHessian φ x i j * coordinateDerivative j g (coordinateGradient φ x)
        ∂potentialMeasure φ := by
  have hφ2 : ContDiff ℝ 2 φ := contDiff_infty.mp hφ 2
  have hφ1 : ContDiff ℝ 1 φ := contDiff_infty.mp hφ 1
  have hgd := hg.differentiable le_rfl
  have hgradd : Differentiable ℝ (coordinateGradient φ) := differentiable_pi.mpr
    (fun j => (smooth_coordinateDerivative hφ j).differentiable (by simp))
  have hcomp : Differentiable ℝ (g ∘ coordinateGradient φ) := hgd.comp hgradd
  have hdint : Integrable (coordinateDerivative i (g ∘ coordinateGradient φ)) (potentialMeasure φ) := by
    have heq : coordinateDerivative i (g ∘ coordinateGradient φ) =
        (fun x => ∑ j, coordinateDerivative j g (coordinateGradient φ x) * coordinateHessian φ x j i) :=
      funext (coordinateDerivative_comp_gradient hφ2 (fun x => hgd _) i)
    rw [heq]
    exact integrable_finset_sum _ (fun j _ => integrable_hessian_gradient_test hφ hg hK hgrad S hHb i j)
  have hfgint : Integrable (fun x => (g ∘ coordinateGradient φ) x * coordinateDerivative i φ x)
      (potentialMeasure φ) :=
    integrable_comp_gradient hφ1 hK hgrad (hg.continuous.mul (continuous_apply i))
  have hfi : Integrable (g ∘ coordinateGradient φ) (potentialMeasure φ) :=
    integrable_comp_gradient hφ1 hK hgrad hg.continuous
  have h := integral_coordinateDerivative i (hφ.differentiable (by simp)) hcomp hdint hfgint hfi
  calc
    _ = ∫ x, (g ∘ coordinateGradient φ) x * coordinateDerivative i φ x ∂potentialMeasure φ := by
      apply integral_congr_ae
      filter_upwards with x
      exact mul_comm _ _
    _ = ∫ x, coordinateDerivative i (g ∘ coordinateGradient φ) x ∂potentialMeasure φ := h.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [coordinateDerivative_comp_gradient hφ2 (fun x => hgd _)]
      apply Finset.sum_congr rfl
      intro j _
      rw [(coordinateHessian_isSymm hφ2 x).apply i j]
      ring

/-- A matrix acts on coordinate space by a genuine continuous linear map. -/
def coordinateMatrixMap {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ) :
    CoordinateSpace n →L[ℝ] CoordinateSpace n :=
  (Matrix.toLin' T).toContinuousLinearMap

@[simp] lemma coordinateMatrixMap_apply {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ)
    (x : CoordinateSpace n) : coordinateMatrixMap T x = T *ᵥ x := rfl

lemma coordinateDerivative_comp_matrix {n : ℕ} {g : CoordinateSpace n → ℝ}
    (hg : Differentiable ℝ g) (T : Matrix (Fin n) (Fin n) ℝ)
    (i : Fin n) (x : CoordinateSpace n) :
    coordinateDerivative i (g ∘ coordinateMatrixMap T) x =
      (Tᵀ *ᵥ coordinateGradient g (T *ᵥ x)) i := by
  unfold coordinateDerivative
  rw [fderiv_comp x (hg _) (coordinateMatrixMap T).differentiableAt,
    (coordinateMatrixMap T).fderiv, ContinuousLinearMap.comp_apply,
    fderiv_apply_eq_sum_coordinates]
  simp [coordinateMatrixMap_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    coordinateGradient, Pi.single_apply]

lemma integrable_stein_row {n : ℕ} {φ g : CoordinateSpace n → ℝ}
    [IsFiniteMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ ∞ φ) (hg : ContDiff ℝ 1 g)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (hgrad : ∀ x, coordinateGradient φ x ∈ K)
    (S : ℝ) (hHb : ∀ x i j, |coordinateHessian φ x i j| ≤ S) (i : Fin n) :
    Integrable (fun x => (coordinateHessian φ x *ᵥ coordinateGradient g (coordinateGradient φ x)) i)
      (potentialMeasure φ) := by
  simp only [Matrix.mulVec, dotProduct]
  apply integrable_finset_sum
  intro j _
  have h := integrable_hessian_gradient_test hφ hg hK hgrad S hHb i j
  convert h using 1
  funext x
  change coordinateHessian φ x i j * _ = _
  rw [← (coordinateHessian_isSymm (contDiff_infty.mp hφ 2) x).apply i j]
  exact mul_comm _ _

set_option maxHeartbeats 800000 in
/-- The Stein identity transports through every linear map, directly in the
moment-map coupling; no inverse gradient or conditional kernel is assumed. -/
theorem moment_map_stein_linear_image {n : ℕ} {φ g : CoordinateSpace n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ ∞ φ) (hg : ContDiff ℝ 1 g)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (hgrad : ∀ x, coordinateGradient φ x ∈ K)
    (S : ℝ) (hHb : ∀ x i j, |coordinateHessian φ x i j| ≤ S)
    (T : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    (∫ x, (T *ᵥ coordinateGradient φ x) i * g (T *ᵥ coordinateGradient φ x)
      ∂potentialMeasure φ) =
    ∫ x, ((T * coordinateHessian φ x * Tᵀ) *ᵥ
      coordinateGradient g (T *ᵥ coordinateGradient φ x)) i ∂potentialMeasure φ := by
  let q : CoordinateSpace n → ℝ := g ∘ coordinateMatrixMap T
  have hq : ContDiff ℝ 1 q := hg.comp (coordinateMatrixMap T).contDiff
  have hφ1 : ContDiff ℝ 1 φ := contDiff_infty.mp hφ 1
  have hleft (a : Fin n) : Integrable
      (fun x => coordinateGradient φ x a * q (coordinateGradient φ x)) (potentialMeasure φ) :=
    integrable_comp_gradient hφ1 hK hgrad ((continuous_apply a).mul hq.continuous)
  have hright (a : Fin n) := integrable_stein_row hφ hq hK hgrad S hHb a
  have hident (a : Fin n) := moment_map_stein_identity hφ hq hK hgrad S hHb a
  have hchain (z : CoordinateSpace n) :
      coordinateGradient q z = Tᵀ *ᵥ coordinateGradient g (T *ᵥ z) := by
    funext a
    exact coordinateDerivative_comp_matrix (hg.differentiable le_rfl) T a z
  calc
    _ = ∫ x, ∑ a, T i a * (coordinateGradient φ x a * q (coordinateGradient φ x))
        ∂potentialMeasure φ := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, q, Function.comp_apply,
        coordinateMatrixMap_apply, mul_assoc]
    _ = ∑ a, T i a * (∫ x, coordinateGradient φ x a * q (coordinateGradient φ x)
        ∂potentialMeasure φ) := by
      rw [integral_finset_sum _ (fun a _ => (hleft a).const_mul (T i a))]
      simp only [integral_const_mul]
    _ = ∑ a, T i a * (∫ x,
        (coordinateHessian φ x *ᵥ coordinateGradient q (coordinateGradient φ x)) a
          ∂potentialMeasure φ) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [hident a]
      rfl
    _ = ∫ x, ∑ a, T i a *
        (coordinateHessian φ x *ᵥ coordinateGradient q (coordinateGradient φ x)) a
        ∂potentialMeasure φ := by
      rw [integral_finset_sum _ (fun a _ => (hright a).const_mul (T i a))]
      simp only [integral_const_mul]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with x
      change (T *ᵥ (coordinateHessian φ x *ᵥ coordinateGradient q (coordinateGradient φ x))) i = _
      rw [hchain, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]

end GaussianTilt.Letwin
