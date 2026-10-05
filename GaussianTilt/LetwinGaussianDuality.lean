import GaussianTilt.LetwinGaussianCoupling
import GaussianTilt.LetwinSteinAbstract

/-! # Concrete negative-Sobolev constants after Gaussian smoothing -/
noncomputable section
open MeasureTheory Matrix Set
open scoped BigOperators ContDiff ENNReal
namespace GaussianTilt.Letwin

def noisySteinMatrix {n : ℕ} (φ : CoordinateSpace n → ℝ)
    (T : Matrix (Fin n) (Fin n) ℝ) (r : ℝ) (x : CoordinateSpace n) : Matrix (Fin n) (Fin n) ℝ :=
  T * coordinateHessian φ x * Tᵀ + r^2 • 1

def noisySteinDualConstant {n : ℕ} (φ : CoordinateSpace n → ℝ)
    (T : Matrix (Fin n) (Fin n) ℝ) (r : ℝ) (v : Fin n → ℝ) : ℝ :=
  Real.sqrt (∫ x, ∑ j, ((noisySteinMatrix φ T r x)ᵀ *ᵥ v) j ^ 2 ∂potentialMeasure φ)

lemma noisySteinDualConstant_nonneg {n : ℕ} (φ : CoordinateSpace n → ℝ)
    (T : Matrix (Fin n) (Fin n) ℝ) (r : ℝ) (v : Fin n → ℝ) :
    0 ≤ noisySteinDualConstant φ T r v := Real.sqrt_nonneg _

lemma noisySteinDualConstant_sq {n : ℕ} (φ : CoordinateSpace n → ℝ)
    (T : Matrix (Fin n) (Fin n) ℝ) (r : ℝ) (v : Fin n → ℝ) :
    noisySteinDualConstant φ T r v ^ 2 =
      ∫ x, ∑ j, ((noisySteinMatrix φ T r x)ᵀ *ᵥ v) j ^ 2 ∂potentialMeasure φ :=
  Real.sq_sqrt (integral_nonneg fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)

lemma memLp_noisyMomentMap {n : ℕ} {φ : CoordinateSpace n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)] (hφ : ContDiff ℝ 1 φ)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (hgrad : ∀ x, coordinateGradient φ x ∈ K)
    (T : Matrix (Fin n) (Fin n) ℝ) (r : ℝ) (i : Fin n) :
    MemLp (fun p => noisyMomentMap φ T r p i) 2 ((potentialMeasure φ).prod (coordinateGaussian n)) := by
  have hX : MemLp (fun x => (T *ᵥ coordinateGradient φ x) i) 2 (potentialMeasure φ) :=
    memLp_comp_gradient (g := fun x => (T *ᵥ x) i) hφ hK hgrad
      ((continuous_apply i).comp (coordinateMatrixMap T).continuous) 2
  exact (hX.comp_fst (coordinateGaussian n)).add
    (((coordinateGaussian_coordinate_memLp i).const_mul r).comp_snd (potentialMeasure φ))

lemma memLp_noisySteinMatrix_entry {n : ℕ} {φ : CoordinateSpace n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)] (hφ : ContDiff ℝ ∞ φ)
    (S : ℝ) (hHb : ∀ x i j, |coordinateHessian φ x i j| ≤ S)
    (T : Matrix (Fin n) (Fin n) ℝ) (r : ℝ) (i j : Fin n) :
    MemLp (fun x => noisySteinMatrix φ T r x i j) 2 (potentialMeasure φ) := by
  apply memLp_continuous_hessian_function hφ S hHb
    (F := fun M => (T * M * Tᵀ + r^2 • (1 : Matrix (Fin n) (Fin n) ℝ)) i j) (p := 2)
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.transpose_apply]
  fun_prop

set_option maxHeartbeats 1000000 in
/-- Every linear functional of the genuinely smoothed law has the concrete
compact-test H⁻¹ bound determined by the original Hessian plus r²I. -/
theorem noisyMomentMeasure_compactNegativeSobolevBound {n : ℕ} {φ : CoordinateSpace n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)] (hφ : ContDiff ℝ ∞ φ)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (hgrad : ∀ x, coordinateGradient φ x ∈ K)
    (S : ℝ) (hHb : ∀ x i j, |coordinateHessian φ x i j| ≤ S)
    (T : Matrix (Fin n) (Fin n) ℝ) (r : ℝ) (v : Fin n → ℝ) :
    CompactNegativeSobolevBound (noisyMomentMeasure φ T r) (fun z => v ⬝ᵥ z)
      (noisySteinDualConstant φ T r v) := by
  intro g hg hgc hge
  let ν := potentialMeasure φ
  let γ := coordinateGaussian n
  let Z := noisyMomentMap φ T r
  have hφ1 := contDiff_infty.mp hφ 1
  have hgc1 := contDiff_infty.mp hg 1
  obtain ⟨C,D,hgB,hD⟩ := smooth_compact_uniform_bounds hg hgc
  have hZ : Continuous Z := continuous_noisyMomentMap hφ1 T r
  have hq : MemLp (fun p => g (Z p)) 2 (ν.prod γ) :=
    MemLp.of_bound (hg.continuous.comp hZ).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun p => by simpa only [Real.norm_eq_abs] using hgB (Z p))
  have hDl (i : Fin n) : MemLp (fun p => coordinateGradient g (Z p) i) 2 (ν.prod γ) :=
    MemLp.of_bound ((smooth_coordinateDerivative hg i).continuous.comp hZ).aestronglyMeasurable D
      (Filter.Eventually.of_forall fun p => by simpa only [Real.norm_eq_abs] using hD (Z p) i)
  have hAl (i j : Fin n) : MemLp (fun p : CoordinateSpace n × CoordinateSpace n =>
      noisySteinMatrix φ T r p.1 i j) 2 (ν.prod γ) :=
    (memLp_noisySteinMatrix_entry hφ S hHb T r i j).comp_fst γ
  have hs := stein_coupling_dual_sq (memLp_noisyMomentMap hφ1 hK hgrad T r)
    hAl hDl hq (fun i => noisy_moment_map_stein_identity hφ hgc1 hK hgrad S hHb C D hgB hD T r i) v
  have hEi : Integrable (fun x => ∑ j, ((noisySteinMatrix φ T r x)ᵀ *ᵥ v) j ^ 2) ν := by
    apply integrable_finset_sum
    intro j _
    apply MemLp.integrable_sq
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    exact memLp_finset_sum _ (fun i _ => (memLp_noisySteinMatrix_entry hφ S hHb T r i j).mul_const (v i))
  have henergy : (∫ p : CoordinateSpace n × CoordinateSpace n,
      ∑ j, ((noisySteinMatrix φ T r p.1)ᵀ *ᵥ v) j ^ 2 ∂ν.prod γ) =
      ∫ x, ∑ j, ((noisySteinMatrix φ T r x)ᵀ *ᵥ v) j ^ 2 ∂ν := by
    rw [integral_prod _ (hEi.comp_fst γ)]
    simp only [integral_const, measureReal_univ_eq_one, one_smul]
  have hE : (∫ p, ∑ j, (coordinateDerivative j g (Z p))^2 ∂ν.prod γ) ≤ 1 := by
    rw [noisyMomentMeasure, integral_map hZ.measurable.aemeasurable
      (continuous_gradientSquare hg).aestronglyMeasurable] at hge
    exact hge
  rw [henergy] at hs
  have hEnonneg : 0 ≤ ∫ x, ∑ j, ((noisySteinMatrix φ T r x)ᵀ *ᵥ v) j ^ 2 ∂ν :=
    integral_nonneg fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hs' := hs.trans (mul_le_mul_of_nonneg_left hE hEnonneg)
  rw [mul_one] at hs'
  have hmap : (∫ z, (v ⬝ᵥ z) * g z ∂noisyMomentMeasure φ T r) =
      ∫ p, (v ⬝ᵥ Z p) * g (Z p) ∂ν.prod γ := by
    rw [noisyMomentMeasure, integral_map hZ.measurable.aemeasurable]
    exact ((show Continuous (fun z : CoordinateSpace n => ∑ j, v j * z j) by
      fun_prop).mul hg.continuous).aestronglyMeasurable
  rw [hmap]
  exact Real.abs_le_sqrt hs'

end GaussianTilt.Letwin
