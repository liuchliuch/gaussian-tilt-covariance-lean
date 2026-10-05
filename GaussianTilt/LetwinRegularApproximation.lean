import GaussianTilt.WhiteningCoordinates
import GaussianTilt.LetwinRegularVariance
import GaussianTilt.LetwinMomentJacobian
import GaussianTilt.LetwinTransportVariance
import GaussianTilt.LetwinMomentSupport
import GaussianTilt.MomentMapIsotropicApproximation
import GaussianTilt.LetwinNoncompactApproximation
import GaussianTilt.ActualUpperFlowVariance
import GaussianTilt.AffineDensityTransportSmooth

/-! # Exact remaining regular-source input and the final Letwin approximation

This file does not assert source regularity. Its explicitly named source
existence proposition records the remaining PDE obligation; all consequences
use the proved regular variance theorem and genuine moment convergence.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped Topology BigOperators ENNReal ContDiff Matrix.Norms.L2Operator

namespace GaussianTilt.Letwin

lemma indicator_density_eq_closure {n : ℕ} {D : Set (CoordinateSpace n)}
    (hDo : IsOpen D) (hDc : Convex ℝ D) (g : CoordinateSpace n → ℝ) :
    volume.withDensity (fun x ↦ ENNReal.ofReal (D.indicator g x)) =
      volume.withDensity (fun x ↦ ENNReal.ofReal ((closure D).indicator g x)) := by
  apply withDensity_congr_ae
  have hb : ∀ᵐ x ∂volume, x ∉ frontier D := by
    apply ae_iff.mpr
    simpa only [not_not] using hDc.addHaar_frontier volume
  filter_upwards [hb] with x hx
  by_cases hxD : x ∈ D
  · simp only [indicator_of_mem hxD, indicator_of_mem (subset_closure hxD)]
  · have hxC : x ∉ closure D := by
      intro h
      apply hx
      rw [frontier, hDo.interior_eq]
      exact ⟨h, hxD⟩
    simp only [indicator_of_notMem hxD, indicator_of_notMem hxC]

/-- Actual regularity data of a moment source, without a variance or a
Monge–Ampère equation field. The PDE equation is derived from transport. -/
structure RegularMomentSource {n : ℕ} (D : Set (CoordinateSpace n))
    (μ : Measure (CoordinateSpace n)) where
  potential : CoordinateSpace n → ℝ
  probability : IsProbabilityMeasure (potentialMeasure potential)
  smooth : ContDiff ℝ ∞ potential
  strict_convex : StrictConvexOn ℝ univ potential
  hessian_bounded : ∃ S : ℝ, ∀ x i j, |coordinateHessian potential x i j| ≤ S
  transport : momentMeasure potential = μ

/-- Precisely the unproved smooth-source regularity/existence input needed
for the actual approximation. This is a proposition definition, not an axiom. -/
def RegularMomentSourceExistence : Prop :=
  ∀ (n : ℕ) (D : Set (CoordinateSpace n)) (V : CoordinateSpace n → ℝ),
    IsOpen D → Convex ℝ D → Bornology.IsBounded D → ContDiff ℝ ∞ V → ConvexOn ℝ univ V →
    let μ := volume.withDensity (fun x ↦ ENNReal.ofReal (D.indicator (fun y ↦ Real.exp (-V y)) x))
    IsProbabilityMeasure μ → meanVector μ id = 0 → Nonempty (RegularMomentSource D μ)

theorem regular_target_variance_from_source {n : ℕ}
    {D : Set (CoordinateSpace n)} {V : CoordinateSpace n → ℝ}
    (hDo : IsOpen D) (hDc : Convex ℝ D) (hDb : Bornology.IsBounded D)
    (hV : ContDiff ℝ ∞ V) (hVc : ConvexOn ℝ univ V)
    {μ : Measure (CoordinateSpace n)}
    (hμ : μ = volume.withDensity (fun x ↦ ENNReal.ofReal (D.indicator (fun y ↦ Real.exp (-V y)) x)))
    (hiso : covarianceMatrix μ id = 1) (S : RegularMomentSource D μ)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) :
    variance (matrixQuadratic B) μ ≤ 8 * Matrix.trace (B ^ 2) := by
  letI := S.probability
  have hμc : μ = volume.withDensity
      (fun x ↦ ENNReal.ofReal ((closure D).indicator (fun y ↦ Real.exp (-V y)) x)) :=
    hμ.trans (indicator_density_eq_closure hDo hDc _)
  obtain ⟨C, hC⟩ := S.hessian_bounded
  exact smooth_moment_source_quadratic_variance S.smooth S.strict_convex
    hDb.isCompact_closure hDc.closure isOpen_univ (subset_univ _)
    (contDiff_infty.mp hV 2).contDiffOn hVc C hC S.transport hiso hμc B hB

end GaussianTilt.Letwin

namespace GaussianTilt.Whitening
variable {n : ℕ}

/-- Actual Gaussian regularization, truncation and whitening preserve the
quadratic variance at the original compact isotropic law. -/
theorem variance_whitened_gaussianTruncation_tendsto
    (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : Reference.Space n ↦ ‖x‖ ^ 4) μ)
    (hi : Reference.isotropic μ) (B : Matrix (Fin n) (Fin n) ℝ) :
    Tendsto (fun k ↦ variance (fun x : Reference.Space n ↦ matrixQuadratic B (coordinates x))
      (law (MomentMapApproximation.perturbedTruncation μ (Paouris.standardGaussian n) k))) atTop
      (𝓝 (variance (fun x : Reference.Space n ↦ matrixQuadratic B (coordinates x)) μ)) := by
  have hc : Continuous (fun x : Reference.Space n ↦ matrixQuadratic B (coordinates x)) := by
    unfold matrixQuadratic Matrix.mulVec dotProduct coordinates
    fun_prop
  have h₁ := integral_whitened_perturbedTruncation_tendsto μ (Paouris.standardGaussian n) hμ
    (MomentMapApproximation.standardGaussian_norm_fourth_integrable n) hi hc (norm_nonneg B) (quadratic_fourth_growth B)
  have h₂ := integral_whitened_perturbedTruncation_tendsto μ (Paouris.standardGaussian n) hμ
    (MomentMapApproximation.standardGaussian_norm_fourth_integrable n) hi (hc.pow 2) (sq_nonneg ‖B‖)
    (quadratic_square_fourth_growth B)
  rw [variance_eq_sub (quadratic_memLp_of_fourth hμ B)]
  apply (h₂.sub (h₁.pow 2)).congr'
  filter_upwards [MomentMapApproximation.eventually_perturbedTruncation_probability μ
    (Paouris.standardGaussian n)] with k hk
  letI := hk
  have hq := Paouris.compact_memLp_continuous
    (law (MomentMapApproximation.perturbedTruncation μ (Paouris.standardGaussian n) k))
    (law_compactlySupported (MomentMapApproximation.perturbedTruncation_compactlySupported μ
      (Paouris.standardGaussian n) k)) hc 2
  exact (variance_eq_sub hq).symm

end GaussianTilt.Whitening

namespace GaussianTilt.Letwin
variable {n : ℕ}

/-- Euclidean regular target laws are transported to the coordinate model
of the regular source theorem with their actual density and moments. -/
theorem regular_isotropic_target_variance
    (hsource : RegularMomentSourceExistence) {μ : Measure (Reference.Space n)}
    (hμ : MomentMapApproximation.RegularIsotropicTarget μ)
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
  obtain ⟨S⟩ := hsource n D' W hD'o hD'c hD'b hW hWc
    (hν ▸ (inferInstance : IsProbabilityMeasure ν)) (by rw [← hν]; exact hm)
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

/-- Every approximation and dimensional-model bridge for the original
compact Letwin proposition is proved; the only input is actual regular
moment-source existence/regularity, explicitly still open. -/
theorem isotropicQuadraticVarianceBound_of_regular_source
    (hsource : RegularMomentSourceExistence) : Reference.IsotropicQuadraticVarianceBound := by
  intro n μ hp hc hi hl B hB
  letI := hp
  have hB' : B.IsSymm := by
    simpa only [Matrix.IsHermitian, Matrix.IsSymm, Matrix.conjTranspose_eq_transpose_of_trivial] using hB
  apply le_of_tendsto (Whitening.variance_whitened_gaussianTruncation_tendsto μ
    (MomentMapApproximation.compact_norm_fourth_integrable hc) hi B)
  filter_upwards [MomentMapApproximation.eventually_whitened_regular_targets μ hc hi hl] with k hk
  exact regular_isotropic_target_variance hsource hk B hB'

end GaussianTilt.Letwin
