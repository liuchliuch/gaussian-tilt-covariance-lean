import GaussianTilt.LetwinGaussianStein

/-! # The exact Stein coupling after independent Gaussian smoothing -/
noncomputable section
open MeasureTheory Matrix Set
open scoped BigOperators ContDiff ENNReal
namespace GaussianTilt.Letwin

def noisyMomentMap {n : ℕ} (φ : CoordinateSpace n → ℝ)
    (T : Matrix (Fin n) (Fin n) ℝ) (r : ℝ)
    (p : CoordinateSpace n × CoordinateSpace n) : CoordinateSpace n :=
  T *ᵥ coordinateGradient φ p.1 + r • p.2

def noisyMomentMeasure {n : ℕ} (φ : CoordinateSpace n → ℝ)
    (T : Matrix (Fin n) (Fin n) ℝ) (r : ℝ) : Measure (CoordinateSpace n) :=
  ((potentialMeasure φ).prod (coordinateGaussian n)).map (noisyMomentMap φ T r)

lemma continuous_noisyMomentMap {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (T : Matrix (Fin n) (Fin n) ℝ) (r : ℝ) :
    Continuous (noisyMomentMap φ T r) :=
  ((continuous_linearMomentMap hφ T).comp continuous_fst).add (continuous_const.smul continuous_snd)

lemma coordinateDerivative_add_right {n : ℕ} {g : CoordinateSpace n → ℝ}
    (hg : Differentiable ℝ g) (a : CoordinateSpace n) (i : Fin n) (x : CoordinateSpace n) :
    coordinateDerivative i (fun y => g (y + a)) x = coordinateDerivative i g (x + a) := by
  simpa only [one_smul, one_mul, add_comm] using coordinateDerivative_affine_scalar hg a 1 i x

set_option maxHeartbeats 1200000 in
/-- The original moment-map Stein matrix acquires exactly r²I after adding
independent genuine Gaussian noise. No conditional expectation or inverse map
is assumed: the identity holds on the explicitly constructed product coupling. -/
theorem noisy_moment_map_stein_identity {n : ℕ} {φ g : CoordinateSpace n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ ∞ φ) (hg : ContDiff ℝ 1 g)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (hgrad : ∀ x, coordinateGradient φ x ∈ K)
    (S : ℝ) (hHb : ∀ x i j, |coordinateHessian φ x i j| ≤ S)
    (C D : ℝ) (hgB : ∀ x, |g x| ≤ C) (hD : ∀ x j, |coordinateDerivative j g x| ≤ D)
    (T : Matrix (Fin n) (Fin n) ℝ) (r : ℝ) (i : Fin n) :
    (∫ p, noisyMomentMap φ T r p i * g (noisyMomentMap φ T r p)
      ∂(potentialMeasure φ).prod (coordinateGaussian n)) =
    ∫ p, ((T * coordinateHessian φ p.1 * Tᵀ + r^2 • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ
      coordinateGradient g (noisyMomentMap φ T r p)) i
      ∂(potentialMeasure φ).prod (coordinateGaussian n) := by
  let ν := potentialMeasure φ
  let γ := coordinateGaussian n
  let Z := noisyMomentMap φ T r
  let τ := fun x => T * coordinateHessian φ x * Tᵀ
  have hφ1 := contDiff_infty.mp hφ 1
  have hZ : Continuous Z := continuous_noisyMomentMap hφ1 T r
  have hgc : Continuous (g ∘ Z) := hg.continuous.comp hZ
  have hDcont (j : Fin n) : Continuous (fun p => coordinateDerivative j g (Z p)) :=
    (contDiff_coordinateDerivative hg (m := 0) (by norm_num) j).continuous.comp hZ
  have hXi : Integrable (fun x => (T *ᵥ coordinateGradient φ x) i) ν :=
    integrable_comp_gradient (g := fun x => (T *ᵥ x) i) hφ1 hK hgrad
      ((continuous_apply i).comp (coordinateMatrixMap T).continuous)
  have hNi : Integrable (fun z : CoordinateSpace n => r * z i) γ :=
    (coordinateGaussian_coordinate_integrable i).const_mul r
  have hτi (j : Fin n) : Integrable (fun x => τ x i j) ν :=
    (memLp_continuous_hessian_function hφ S hHb (F := fun M => (T * M * Tᵀ) i j)
      (by simp only [Matrix.mul_apply, Matrix.transpose_apply]; fun_prop) 1).integrable le_rfl
  have hsource : Integrable
      (fun p : CoordinateSpace n × CoordinateSpace n => (T *ᵥ coordinateGradient φ p.1) i * g (Z p))
      (ν.prod γ) := by
    simpa only [Function.comp_apply, mul_comm] using (hXi.comp_fst γ).bdd_mul hgc.aestronglyMeasurable
      ⟨C, fun p => by simpa only [Real.norm_eq_abs, Function.comp_apply] using hgB (Z p)⟩
  have hnoise : Integrable (fun p : CoordinateSpace n × CoordinateSpace n => r * p.2 i * g (Z p))
      (ν.prod γ) := by
    simpa only [Function.comp_apply, mul_comm] using (hNi.comp_snd ν).bdd_mul hgc.aestronglyMeasurable
      ⟨C, fun p => by simpa only [Real.norm_eq_abs, Function.comp_apply] using hgB (Z p)⟩
  have hRi (j : Fin n) : Integrable
      (fun p : CoordinateSpace n × CoordinateSpace n => τ p.1 i j * coordinateDerivative j g (Z p))
      (ν.prod γ) := by
    simpa only [Function.comp_apply, mul_comm] using ((hτi j).comp_fst γ).bdd_mul (hDcont j).aestronglyMeasurable
      ⟨D, fun p => by simpa only [Real.norm_eq_abs] using hD (Z p) j⟩
  have hR : Integrable (fun p : CoordinateSpace n × CoordinateSpace n =>
      (τ p.1 *ᵥ coordinateGradient g (Z p)) i) (ν.prod γ) := by
    simp only [Matrix.mulVec, dotProduct]
    exact integrable_finset_sum _ (fun j _ => hRi j)
  have hDi : Integrable (fun p => r^2 * coordinateDerivative i g (Z p)) (ν.prod γ) :=
    (Integrable.of_bound (hDcont i).aestronglyMeasurable D
      (Filter.Eventually.of_forall fun p => by simpa only [Real.norm_eq_abs] using hD (Z p) i)).const_mul (r^2)
  have hsource_id : (∫ p, (T *ᵥ coordinateGradient φ p.1) i * g (Z p) ∂ν.prod γ) =
      ∫ p, (τ p.1 *ᵥ coordinateGradient g (Z p)) i ∂ν.prod γ := by
    rw [integral_prod_symm _ hsource, integral_prod_symm _ hR]
    apply integral_congr_ae
    filter_upwards with z
    have hq : ContDiff ℝ 1 (fun y => g (y + r • z)) := hg.comp (contDiff_id.add contDiff_const)
    have hid := moment_map_stein_linear_image hφ hq hK hgrad S hHb T i
    convert hid using 1
    apply integral_congr_ae
    filter_upwards with x
    congr 1
    funext j
    exact (coordinateDerivative_add_right (hg.differentiable le_rfl) _ j _).symm
  have hnoise_id : (∫ p : CoordinateSpace n × CoordinateSpace n, r * p.2 i * g (Z p) ∂ν.prod γ) =
      ∫ p, r^2 * coordinateDerivative i g (Z p) ∂ν.prod γ := by
    rw [integral_prod _ hnoise, integral_prod _ hDi]
    apply integral_congr_ae
    filter_upwards with x
    exact coordinateGaussian_affine_stein hg C D hgB hD (T *ᵥ coordinateGradient φ x) r i
  have heqL : (fun p => Z p i * g (Z p)) =
      (fun p => (T *ᵥ coordinateGradient φ p.1) i * g (Z p) + r * p.2 i * g (Z p)) := by
    funext p
    change ((T *ᵥ coordinateGradient φ p.1) i + r * p.2 i) * g (Z p) = _
    ring
  have heqR : (fun p : CoordinateSpace n × CoordinateSpace n =>
      ((τ p.1 + r^2 • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ coordinateGradient g (Z p)) i) =
      (fun p => (τ p.1 *ᵥ coordinateGradient g (Z p)) i + r^2 * coordinateDerivative i g (Z p)) := by
    funext p
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, coordinateGradient]
  change (∫ p, Z p i * g (Z p) ∂ν.prod γ) = _
  rw [heqL, heqR, integral_add hsource hnoise, integral_add hR hDi, hsource_id, hnoise_id]

end GaussianTilt.Letwin
