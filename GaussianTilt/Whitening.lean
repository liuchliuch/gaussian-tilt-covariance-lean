import GaussianTilt.WhiteningMatrices
import GaussianTilt.AffineDensityTransport

/-! # Whitening the actual probability law

The measure here is the pushforward of the original law under its own centered
inverse covariance square root. Isotropy is proved from finite second moments
and positive definiteness. No quadratic variance estimate is postulated.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace GaussianTilt.Whitening
variable {n : ℕ}

abbrev coordinates (x : Reference.Space n) : Fin n → ℝ := WithLp.ofLp x

def center (μ : Measure (Reference.Space n)) : Reference.Space n :=
  WithLp.toLp 2 (meanVector μ coordinates)

def covariance (μ : Measure (Reference.Space n)) : Matrix (Fin n) (Fin n) ℝ :=
  covarianceMatrix μ coordinates

def whitenMap (μ : Measure (Reference.Space n)) (x : Reference.Space n) : Reference.Space n :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (inverseRoot (covariance μ)) (x - center μ)

def law (μ : Measure (Reference.Space n)) : Measure (Reference.Space n) := μ.map (whitenMap μ)

lemma continuous_whitenMap (μ : Measure (Reference.Space n)) : Continuous (whitenMap μ) :=
  (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) _).continuous.comp (continuous_id.sub continuous_const)

instance law_probability (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (law μ) :=
  Measure.isProbabilityMeasure_map (continuous_whitenMap μ).measurable.aemeasurable

lemma coordinates_whitenMap (μ : Measure (Reference.Space n)) (x : Reference.Space n) :
    coordinates (whitenMap μ x) =
      inverseRoot (covariance μ) *ᵥ (coordinates x - meanVector μ coordinates) := by
  rw [whitenMap, coordinates, Matrix.ofLp_toEuclideanCLM]
  rfl

lemma meanVector_law (μ : Measure (Reference.Space n)) :
    meanVector (law μ) coordinates =
      meanVector μ (fun x ↦ inverseRoot (covariance μ) *ᵥ
        (coordinates x - meanVector μ coordinates)) := by
  ext i
  rw [meanVector, law, integral_map (continuous_whitenMap μ).measurable.aemeasurable
    (show AEStronglyMeasurable (fun x : Reference.Space n ↦ coordinates x i) _ by fun_prop)]
  simp only [meanVector, ← coordinates_whitenMap]

lemma covariance_law (μ : Measure (Reference.Space n)) :
    covariance (law μ) = covarianceMatrix μ
      (fun x ↦ inverseRoot (covariance μ) *ᵥ (coordinates x - meanVector μ coordinates)) := by
  ext i j
  rw [covariance, covarianceMatrix, law, covariance_map_fun
    (show AEStronglyMeasurable (fun x : Reference.Space n ↦ coordinates x i) _ by fun_prop)
    (show AEStronglyMeasurable (fun x : Reference.Space n ↦ coordinates x j) _ by fun_prop)
    (continuous_whitenMap μ).measurable.aemeasurable]
  simp only [covarianceMatrix, ← coordinates_whitenMap]

variable {μ : Measure (Reference.Space n)} [IsProbabilityMeasure μ]

lemma coordinates_memLp_law (hX : ∀ i : Fin n, MemLp (fun x ↦ x i) 2 μ) (i : Fin n) :
    MemLp (fun x : Reference.Space n ↦ x i) 2 (law μ) := by
  apply (memLp_map_measure_iff
    (PiLp.continuous_apply 2 (fun _ : Fin n ↦ ℝ) i).aestronglyMeasurable
    (continuous_whitenMap μ).measurable.aemeasurable).mpr
  have h := memLp_mulVec (memLp_center (X := coordinates) hX (meanVector μ coordinates))
    (inverseRoot (covariance μ)) i
  simpa only [Function.comp_def, ← coordinates_whitenMap] using h

lemma law_meanVector_zero (hX : ∀ i : Fin n, MemLp (fun x ↦ x i) 2 μ) :
    meanVector (law μ) coordinates = 0 := by
  rw [meanVector_law]
  exact meanVector_whiten hX _

lemma law_covariance_one (hX : ∀ i : Fin n, MemLp (fun x ↦ x i) 2 μ)
    (hC : (covariance μ).PosDef) : covariance (law μ) = 1 := by
  rw [covariance_law, covarianceMatrix_affine (X := coordinates) hX]
  exact inverseRoot_covariance hC

lemma law_secondMoment_one (hX : ∀ i : Fin n, MemLp (fun x ↦ x i) 2 μ)
    (hC : (covariance μ).PosDef) : secondMomentMatrix (law μ) coordinates = 1 := by
  rw [secondMomentMatrix_eq_covariance_add_rankOne (X := coordinates) (coordinates_memLp_law hX),
    law_meanVector_zero hX]
  change covariance (law μ) + vecMulVec 0 0 = 1
  rw [law_covariance_one hX hC]
  simp

lemma integrable_id_of_coordinates (hX : ∀ i : Fin n, Integrable (fun x : Reference.Space n ↦ x i) μ) :
    Integrable (fun x : Reference.Space n ↦ x) μ := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)).integrable_comp_iff.mp
  exact integrable_pi_iff.mpr hX

lemma center_eq_mean (hX : ∀ i : Fin n, Integrable (fun x : Reference.Space n ↦ x i) μ) :
    center μ = Reference.mean μ := by
  ext i
  exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n ↦ ℝ) i).integral_comp_comm
    (integrable_id_of_coordinates hX)

/-- The genuine pushforward law is isotropic in the independent specification. -/
theorem law_isotropic (hX : ∀ i : Fin n, MemLp (fun x ↦ x i) 2 μ)
    (hC : (covariance μ).PosDef) : Reference.isotropic (law μ) := by
  constructor
  · rw [← center_eq_mean (fun i ↦ (coordinates_memLp_law hX i).integrable (by norm_num))]
    simp only [center, law_meanVector_zero hX, WithLp.toLp_zero]
  · rw [Reference.covariance_eq_covarianceMatrix (coordinates_memLp_law hX)]
    exact law_covariance_one hX hC

lemma law_logconcave (hμ : Reference.logconcave μ) (hC : (covariance μ).PosDef) :
    Reference.logconcave (law μ) :=
  Reference.logconcave_map_affine hμ (rootEquiv hC).symm (center μ)

lemma law_compactlySupported (hμ : Reference.compactlySupported μ) :
    Reference.compactlySupported (law μ) :=
  Reference.compactlySupported_map_continuous hμ (continuous_whitenMap μ)

/-- Applying the covariance square root recovers the actual centered sample. -/
lemma root_whitenMap (hC : (covariance μ).PosDef) (x : Reference.Space n) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (root (covariance μ)) (whitenMap μ x) =
      x - center μ := by
  exact (rootEquiv hC).apply_symm_apply (x - center μ)

lemma quadratic_whitenMap (hC : (covariance μ).PosDef)
    (B : Matrix (Fin n) (Fin n) ℝ) (x : Reference.Space n) :
    matrixQuadratic (root (covariance μ) * B * root (covariance μ)) (coordinates (whitenMap μ x)) =
      matrixQuadratic B (coordinates x - meanVector μ coordinates) := by
  rw [coordinates_whitenMap]
  exact quadratic_whitening_identity B hC _

/-- Exact variance transport for the quadratic observable, before any analytic
inequality is supplied. -/
theorem quadratic_variance_transport (hC : (covariance μ).PosDef)
    (B : Matrix (Fin n) (Fin n) ℝ) :
    ProbabilityTheory.variance
      (fun y : Reference.Space n ↦ matrixQuadratic (root (covariance μ) * B * root (covariance μ))
        (coordinates y)) (law μ) =
      ProbabilityTheory.variance (fun x ↦ matrixQuadratic B (coordinates x - meanVector μ coordinates)) μ := by
  rw [law, variance_map
    (show AEMeasurable (fun y : Reference.Space n ↦
      matrixQuadratic (root (covariance μ) * B * root (covariance μ)) (coordinates y)) _ by
      unfold matrixQuadratic Matrix.mulVec dotProduct; fun_prop)
    (continuous_whitenMap μ).measurable.aemeasurable]
  congr 1
  funext x
  exact quadratic_whitenMap hC B x

end GaussianTilt.Whitening
