import GaussianTilt.Whitening

/-! # Coordinate-space interface for the genuine whitened law -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix Set
open scoped BigOperators ENNReal Matrix.Norms.L2Operator
namespace GaussianTilt.Whitening
variable {n : ℕ}

def coordinateEquiv (n : ℕ) : Reference.Space n ≃L[ℝ] (Fin n → ℝ) :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)

def coordinateLaw (μ : Measure (Reference.Space n)) : Measure (Fin n → ℝ) :=
  (law μ).map (coordinateEquiv n)

instance coordinateLaw_probability (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (coordinateLaw μ) :=
  Measure.isProbabilityMeasure_map (coordinateEquiv n).continuous.measurable.aemeasurable

lemma integral_coordinateLaw (μ : Measure (Reference.Space n)) (f : (Fin n → ℝ) → ℝ) :
    ∫ x, f x ∂coordinateLaw μ = ∫ x, f (coordinates x) ∂law μ :=
  (coordinateEquiv n).toHomeomorph.measurableEmbedding.integral_map f

lemma meanVector_coordinateLaw (μ : Measure (Reference.Space n)) :
    meanVector (coordinateLaw μ) id = meanVector (law μ) coordinates := by
  ext i
  exact integral_coordinateLaw μ (fun x ↦ x i)

lemma covarianceMatrix_coordinateLaw (μ : Measure (Reference.Space n)) :
    covarianceMatrix (coordinateLaw μ) id = covariance (law μ) := by
  ext i j
  exact covariance_map_equiv (fun x : Fin n → ℝ ↦ x i) (fun x : Fin n → ℝ ↦ x j)
    (coordinateEquiv n).toHomeomorph.toMeasurableEquiv

lemma secondMomentMatrix_coordinateLaw (μ : Measure (Reference.Space n)) :
    secondMomentMatrix (coordinateLaw μ) id = secondMomentMatrix (law μ) coordinates := by
  ext i j
  exact integral_coordinateLaw μ (fun x ↦ x i * x j)

variable {μ : Measure (Reference.Space n)} [IsProbabilityMeasure μ]

lemma coordinateLaw_mean_zero (hX : ∀ i : Fin n, MemLp (fun x ↦ x i) 2 μ) :
    meanVector (coordinateLaw μ) id = 0 := by
  rw [meanVector_coordinateLaw, law_meanVector_zero hX]

lemma coordinateLaw_covariance_one (hX : ∀ i : Fin n, MemLp (fun x ↦ x i) 2 μ)
    (hC : (covariance μ).PosDef) : covarianceMatrix (coordinateLaw μ) id = 1 := by
  rw [covarianceMatrix_coordinateLaw, law_covariance_one hX hC]

lemma coordinateLaw_secondMoment_one (hX : ∀ i : Fin n, MemLp (fun x ↦ x i) 2 μ)
    (hC : (covariance μ).PosDef) : secondMomentMatrix (coordinateLaw μ) id = 1 := by
  rw [secondMomentMatrix_coordinateLaw, law_secondMoment_one hX hC]

lemma coordinateLaw_memLp (hX : ∀ i : Fin n, MemLp (fun x ↦ x i) 2 μ) (i : Fin n) :
    MemLp (fun x : Fin n → ℝ ↦ x i) 2 (coordinateLaw μ) := by
  exact (memLp_map_measure_iff (continuous_apply i).aestronglyMeasurable
    (coordinateEquiv n).continuous.measurable.aemeasurable).mpr (coordinates_memLp_law hX i)

lemma coordinateLaw_logconcave (hμ : Reference.logconcave μ) (hC : (covariance μ).PosDef) :
    ∃ f : (Fin n → ℝ) → ℝ, LogConcaveMarginal.IsLogConcave f ∧ Measurable f ∧
      coordinateLaw μ = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)) := by
  obtain ⟨f, hf, hμf⟩ := law_logconcave hμ hC
  obtain ⟨c, hc, hl, hm, heq⟩ := LinearImageDensity.exists_density_map_linearEquiv
    (coordinateEquiv n) volume volume ⟨hf.1, hf.2.2⟩ hf.2.1
  refine ⟨_, hl, hm, ?_⟩
  rw [coordinateLaw, hμf, heq]

lemma coordinateLaw_compactlySupported (hμ : Reference.compactlySupported μ) :
    ∃ K : Set (Fin n → ℝ), IsCompact K ∧ coordinateLaw μ Kᶜ = 0 := by
  obtain ⟨K, hK, hμK⟩ := law_compactlySupported hμ
  refine ⟨coordinateEquiv n '' K, hK.image (coordinateEquiv n).continuous, ?_⟩
  rw [coordinateLaw, Measure.map_apply (coordinateEquiv n).continuous.measurable
    (hK.image (coordinateEquiv n).continuous).isClosed.measurableSet.compl]
  simpa only [preimage_compl, (coordinateEquiv n).injective.preimage_image] using hμK

lemma quadratic_variance_coordinateLaw (B : Matrix (Fin n) (Fin n) ℝ) :
    ProbabilityTheory.variance (matrixQuadratic B) (coordinateLaw μ) =
      ProbabilityTheory.variance (fun x ↦ matrixQuadratic B (coordinates x)) (law μ) := by
  rw [coordinateLaw, variance_map (show AEMeasurable (matrixQuadratic B) _ by
    unfold matrixQuadratic Matrix.mulVec dotProduct; fun_prop)
    (coordinateEquiv n).continuous.measurable.aemeasurable]
  rfl

/-- Full centered quadratic transport to the law on ordinary coordinate
space used by the moment-map argument. -/
theorem quadratic_variance_coordinate_transport (hC : (covariance μ).PosDef)
    (B : Matrix (Fin n) (Fin n) ℝ) :
    ProbabilityTheory.variance (matrixQuadratic (root (covariance μ) * B * root (covariance μ)))
      (coordinateLaw μ) =
    ProbabilityTheory.variance (fun x ↦ matrixQuadratic B (coordinates x - meanVector μ coordinates)) μ := by
  rw [quadratic_variance_coordinateLaw, quadratic_variance_transport hC]

end GaussianTilt.Whitening
