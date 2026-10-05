import GaussianTilt.MomentMapRegularityStrongSource
import GaussianTilt.MomentMapStrongApproximationRegular
import GaussianTilt.LetwinStrongApproximation

/-! # The exact last regularity step for the original Letwin theorem

All approximation, transport, covariance, Hessian and variance arguments are
proved here. The remaining C∞ assertion stays explicit until its analytic
construction is complete; no numbered theorem is declared closed from it.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped Topology BigOperators ENNReal NNReal ContDiff Matrix.Norms.L2Operator Gradient
namespace GaussianTilt.Letwin
variable {n : ℕ}

theorem regular_isotropic_target_variance_of_coordinate_source
    {μ : Measure (Reference.Space n)}
    (hμ : MomentMapApproximation.RegularIsotropicTarget μ)
    {D₀ : Set (CoordinateSpace n)}
    (S₀ : RegularMomentSource D₀ (μ.map (Whitening.coordinateEquiv n)))
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) :
    variance (fun x : Reference.Space n ↦ matrixQuadratic B (Whitening.coordinates x)) μ ≤
      8 * Matrix.trace (B ^ 2) := by
  obtain ⟨hp, hc, hi, hl, D, V, hDo, hDc, hDb, hV, hVc, hμV⟩ := hμ
  letI := hp
  let e := Whitening.coordinateEquiv n
  let ν : Measure (CoordinateSpace n) := μ.map e
  letI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map e.continuous.measurable.aemeasurable
  let D' : Set (CoordinateSpace n) := (fun x : Reference.Space n ↦ e (x - 0)) '' D
  have hD'o : IsOpen D' := by
    dsimp only [D']
    rw [AffineDensityTransport.affine_image_eq_inverse_preimage]
    exact hDo.preimage (e.symm.continuous.add continuous_const)
  have hD'c : Convex ℝ D' := AffineDensityTransport.convex_affine_image e 0 hDc
  have hD'b : Bornology.IsBounded D' :=
    (hDb.isCompact_closure.image (e.continuous.comp (continuous_id.sub continuous_const))).isBounded.subset
      (Set.image_mono subset_closure)
  obtain ⟨W, hW, hWc, hWlaw⟩ := AffineDensityTransport.exists_smooth_convex_potential_map_affine_indicator
    e 0 volume volume hV hVc hDc hDo.measurableSet
  have hν : ν = volume.withDensity (fun x ↦ ENNReal.ofReal (D'.indicator (fun y ↦ Real.exp (-W y)) x)) := by
    dsimp only [ν]
    rw [hμV]
    simpa only [D', sub_zero] using hWlaw
  have hX := Reference.isotropic_coordinate_memLp hi
  have hm : meanVector ν id = 0 := by
    ext i
    change (∫ x : CoordinateSpace n, x i ∂μ.map e) = 0
    rw [integral_map e.continuous.measurable.aemeasurable (continuous_apply i).aestronglyMeasurable]
    exact Reference.isotropic_coordinate_integral hi i
  have hcov : covarianceMatrix ν id = 1 := by
    have heq : covarianceMatrix ν id = Whitening.covariance μ := by
      ext i j
      exact covariance_map_equiv (fun x : CoordinateSpace n ↦ x i) (fun x : CoordinateSpace n ↦ x j)
        e.toHomeomorph.toMeasurableEquiv
    rw [heq, Whitening.covariance_eq_reference hX, hi.2]
  let S : RegularMomentSource D' (volume.withDensity
      (fun x ↦ ENNReal.ofReal (D'.indicator (fun y ↦ Real.exp (-W y)) x))) := {
    potential := S₀.potential
    probability := S₀.probability
    smooth := S₀.smooth
    strict_convex := S₀.strict_convex
    hessian_bounded := S₀.hessian_bounded
    transport := S₀.transport.trans hν }
  have hb := regular_target_variance_from_source hD'o hD'c hD'b hW hWc rfl
    (by rw [← hν]; exact hcov) S B hB
  rw [← hν] at hb
  have ht : variance (matrixQuadratic B) ν =
      variance (fun x : Reference.Space n ↦ matrixQuadratic B (Whitening.coordinates x)) μ := by
    change variance (matrixQuadratic B) (μ.map e) = _
    rw [variance_map (show AEMeasurable (matrixQuadratic B) _ by
      unfold matrixQuadratic Matrix.mulVec dotProduct; fun_prop) e.continuous.measurable.aemeasurable]
    rfl
  rwa [ht] at hb


/-- The sole remaining analytic assertion, stated for genuine transported
sources of smooth strongly convex ball targets. This definition is not an axiom. -/
def StrongBallSourceSmoothness : Prop :=
  ∀ (n : ℕ) (V : Reference.Space n → ℝ) (c : Reference.Space n) (R κ : ℝ),
    0 < R → 0 < κ → ContDiff ℝ ∞ V → StrongConvexOn univ κ V →
    ∀ (φ : Reference.Space n → ℝ) (L : ℝ≥0), LipschitzWith L φ → ConvexOn ℝ univ φ →
      IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x)))) →
      (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x)))).map (gradient φ) =
        volume.withDensity (fun x => ENNReal.ofReal
          ((Metric.ball c R).indicator (fun y => Real.exp (-V y)) x)) → ContDiff ℝ ∞ φ

/-- The actual strongly tilted and whitened approximation has a regular
source once the remaining source smoothness theorem is supplied. -/
theorem regular_source_whitened_strongTruncation
    (hsmooth : StrongBallSourceSmoothness)
    (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hc : Reference.compactlySupported μ) (hl : Reference.logconcave μ) (k : ℕ)
    (hC : (Whitening.covariance (MomentMapApproximation.strongTruncation μ k)).PosDef) :
    ∃ D : Set (CoordinateSpace n), Nonempty (RegularMomentSource D
      ((Whitening.law (MomentMapApproximation.strongTruncation μ k)).map
        (Whitening.coordinateEquiv n))) := by
  obtain ⟨V, hV, hVc, hν⟩ :=
    MomentMapApproximation.exists_strong_potential_centeredStrongTruncation μ hc hl k
  let c := -Whitening.center (MomentMapApproximation.strongTruncation μ k)
  let R : ℝ := (k : ℝ) + 1
  let κ := 2 * MomentMapApproximation.tiltScale k
  have hR : 0 < R := by dsimp [R]; positivity
  have hκ : 0 < κ := mul_pos (by norm_num) (MomentMapApproximation.tiltScale_pos k)
  let ν := volume.withDensity (fun x : Reference.Space n => ENNReal.ofReal
    ((Metric.ball c R).indicator (fun y => Real.exp (-V y)) x))
  have hνeq : MomentMapApproximation.centeredStrongTruncation μ k = ν := hν
  letI : IsProbabilityMeasure ν := hνeq ▸ inferInstance
  have hm : (∫ x : Reference.Space n, x ∂ν) = 0 := by
    rw [← hνeq]
    exact MomentMapApproximation.centeredStrongTruncation_mean μ k
  obtain ⟨S⟩ := MomentMapRegularity.regular_strong_ball_source_of_smoothness V c hR hκ
    hV hVc hm (hsmooth n V c R κ hR hκ hV hVc)
  let T := Whitening.inverseRoot (Whitening.covariance (MomentMapApproximation.strongTruncation μ k))
  have hT : T.det ≠ 0 := by
    have h := congrArg Matrix.det (Whitening.inverseRoot_mul_root hC)
    rw [Matrix.det_mul, Matrix.det_one] at h
    intro hzero
    rw [show (Whitening.inverseRoot (Whitening.covariance (MomentMapApproximation.strongTruncation μ k))).det = 0 from hzero, zero_mul] at h
    exact zero_ne_one h
  obtain ⟨S'⟩ := MomentMapRegularity.regular_source_linear_image S T hT
  refine ⟨coordinateMatrixMap T '' ((MomentMapRegularity.coordinateEquiv n) '' Metric.ball c R), ?_⟩
  have heq : ((ν.map (MomentMapRegularity.coordinateEquiv n)).map (coordinateMatrixMap T)) =
      (Whitening.law (MomentMapApproximation.strongTruncation μ k)).map
        (Whitening.coordinateEquiv n) := by
    rw [MomentMapApproximation.law_strongTruncation_eq_linear_centered, hνeq,
      Measure.map_map (Whitening.coordinateEquiv n).continuous.measurable
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) T).continuous.measurable,
      Measure.map_map (coordinateMatrixMap T).continuous.measurable
        (MomentMapRegularity.coordinateEquiv n).continuous.measurable]
    congr 1
  exact ⟨heq ▸ S'⟩

/-- All approximation/model-transfer steps of the original compact Letwin
variance are discharged; only the explicit source smoothness proposition remains. -/
theorem isotropicQuadraticVarianceBound_of_strong_ball_smoothness
    (hsmooth : StrongBallSourceSmoothness) : Reference.IsotropicQuadraticVarianceBound := by
  intro n μ hp hc hi hl B hB
  letI := hp
  have hB' : B.IsSymm := by
    simpa only [Matrix.IsHermitian, Matrix.IsSymm, Matrix.conjTranspose_eq_transpose_of_trivial] using hB
  apply le_of_tendsto (Whitening.variance_whitened_strongTruncation_tendsto μ
    (MomentMapApproximation.compact_norm_fourth_integrable hc) hi B)
  filter_upwards [MomentMapApproximation.eventually_whitened_strongTruncation_regular_targets μ hc hi hl,
    MomentMapApproximation.eventually_strongTruncation_covariance_posDef μ
      (MomentMapApproximation.compact_norm_fourth_integrable hc) hi] with k hk hC
  obtain ⟨D, ⟨S⟩⟩ := regular_source_whitened_strongTruncation hsmooth μ hc hl k hC
  exact regular_isotropic_target_variance_of_coordinate_source hk S B hB'

end GaussianTilt.Letwin
