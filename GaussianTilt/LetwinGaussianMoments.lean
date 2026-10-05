import GaussianTilt.LetwinGaussianDuality
import GaussianTilt.MomentMapGaussianApproximation
import GaussianTilt.WhiteningQuadraticApproximation

/-! # Actual fourth moments and quadratic variance continuity of Gaussian smoothing -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix Set Filter
open scoped BigOperators ContDiff ENNReal Topology
namespace GaussianTilt.Letwin

lemma coordinateGaussian_products_memLp {n : ℕ} (i j : Fin n) :
    MemLp (fun x : CoordinateSpace n => x i*x j) 2 (coordinateGaussian n) := by
  apply (memLp_map_measure_iff (show Continuous (fun x : CoordinateSpace n => x i*x j) by fun_prop).aestronglyMeasurable
    (euclideanCoordinates n).continuous.measurable.aemeasurable).mpr
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  apply (MomentMapApproximation.standardGaussian_norm_fourth_integrable n).mono' (by fun_prop)
  filter_upwards with x
  change ‖(x i*x j)^2‖ ≤ ‖x‖^4
  rw [Real.norm_of_nonneg (sq_nonneg _), mul_pow]
  have hi : (x i)^2 ≤ ‖x‖^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (x i)) (PiLp.norm_apply_le x i) 2
  have hj : (x j)^2 ≤ ‖x‖^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (x j)) (PiLp.norm_apply_le x j) 2
  have hm := mul_le_mul hi hj (sq_nonneg _) (sq_nonneg _)
  nlinarith

lemma memLp_independent_product {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    {μ : Measure E} {ν : Measure F} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f : E → ℝ} {g : F → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 ν) :
    MemLp (fun p : E × F => f p.1*g p.2) 2 (μ.prod ν) := by
  apply (memLp_two_iff_integrable_sq ((hf.comp_fst ν).aestronglyMeasurable.mul
    (hg.comp_snd μ).aestronglyMeasurable)).mpr
  simpa only [Pi.mul_apply, mul_pow] using hf.integrable_sq.mul_prod hg.integrable_sq

lemma matrixQuadratic_add_scaled_fromBlocks {ι : Type*} [Fintype ι]
    (B : Matrix ι ι ℝ) (x y : ι → ℝ) (r : ℝ) :
    matrixQuadratic (Matrix.fromBlocks B (r • B) (r • B) (r^2 • B)) (Sum.elim x y) =
      matrixQuadratic B (x+r•y) := by
  simp only [matrixQuadratic, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.mulVec_add, Matrix.mulVec_smul,
    Matrix.smul_mulVec, sumElim_dotProduct_sumElim, dotProduct_add, add_dotProduct, dotProduct_smul,
    smul_dotProduct, smul_eq_mul]
  ring

lemma continuous_quadratic_add_scaled_variance {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X Y : Ω → ι → ℝ}
    (hXX : ∀ i j, MemLp (fun w => X w i*X w j) 2 μ)
    (hXY : ∀ i j, MemLp (fun w => X w i*Y w j) 2 μ)
    (hYY : ∀ i j, MemLp (fun w => Y w i*Y w j) 2 μ)
    (B : Matrix ι ι ℝ) :
    Continuous (fun r : ℝ => variance (fun w => matrixQuadratic B (X w+r•Y w)) μ) := by
  let W := fun w => Sum.elim (X w) (Y w)
  have hW (a b : ι ⊕ ι) : MemLp (fun w => W w a*W w b) 2 μ := by
    cases a with
    | inl i => cases b with
      | inl j => exact hXX i j
      | inr j => exact hXY i j
    | inr i => cases b with
      | inl j => simpa only [mul_comm] using hXY j i
      | inr j => exact hYY i j
  have hA : Continuous (fun r : ℝ => Matrix.fromBlocks B (r • B) (r • B) (r^2 • B)) := by
    apply continuous_pi
    intro a
    apply continuous_pi
    intro b
    cases a <;> cases b <;> simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.smul_apply, smul_eq_mul] <;> fun_prop
  have h := (Whitening.continuous_quadratic_variance hW).comp hA
  simpa only [W, Function.comp_def, matrixQuadratic_add_scaled_fromBlocks] using h

lemma continuous_noisy_quadratic_variance {n : ℕ} {φ : CoordinateSpace n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)] (hφ : ContDiff ℝ 1 φ)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (hgrad : ∀ x, coordinateGradient φ x ∈ K)
    (T B : Matrix (Fin n) (Fin n) ℝ) :
    Continuous (fun r : ℝ => variance (matrixQuadratic B) (noisyMomentMeasure φ T r)) := by
  let X := fun p : CoordinateSpace n × CoordinateSpace n => T*ᵥcoordinateGradient φ p.1
  let Y := fun p : CoordinateSpace n × CoordinateSpace n => p.2
  have hXi (i : Fin n) : MemLp (fun x => (T*ᵥcoordinateGradient φ x) i) 2 (potentialMeasure φ) :=
    memLp_comp_gradient (g := fun x => (T*ᵥx) i) hφ hK hgrad
      ((continuous_apply i).comp (coordinateMatrixMap T).continuous) 2
  have hXX (i j : Fin n) : MemLp (fun p => X p i*X p j) 2
      ((potentialMeasure φ).prod (coordinateGaussian n)) := by
    exact (memLp_comp_gradient (g := fun x => (T*ᵥx) i*(T*ᵥx) j) hφ hK hgrad
      (((continuous_apply i).comp (coordinateMatrixMap T).continuous).mul
        ((continuous_apply j).comp (coordinateMatrixMap T).continuous)) 2).comp_fst _
  have hXY (i j : Fin n) : MemLp (fun p => X p i*Y p j) 2
      ((potentialMeasure φ).prod (coordinateGaussian n)) :=
    memLp_independent_product (hXi i) (coordinateGaussian_coordinate_memLp j)
  have hYY (i j : Fin n) : MemLp (fun p => Y p i*Y p j) 2
      ((potentialMeasure φ).prod (coordinateGaussian n)) :=
    (coordinateGaussian_products_memLp i j).comp_snd _
  have h := continuous_quadratic_add_scaled_variance hXX hXY hYY B
  convert h using 1
  ext r
  rw [noisyMomentMeasure, variance_map (contDiff_matrixQuadratic B).continuous.aemeasurable
    (continuous_noisyMomentMap hφ T r).measurable.aemeasurable]
  rfl

end GaussianTilt.Letwin
