import GaussianTilt.LetwinTransportVariance

/-! # Compact gradient image derived from actual target support -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix Set
open scoped ContDiff ENNReal
namespace GaussianTilt.Letwin

/-- Because the source Gibbs density is everywhere positive, a continuous
gradient whose actual law is supported on a closed set takes every point
into that set. An almost-everywhere range condition is not assumed pointwise. -/
theorem coordinateGradient_mem_of_moment_support {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 1 φ) {K : Set (CoordinateSpace n)} (hK : IsClosed K)
    (hs : momentMeasure φ Kᶜ=0) : ∀ x, coordinateGradient φ x∈K := by
  letI : (potentialMeasure φ).IsOpenPosMeasure :=
    (volume_absolutelyContinuous_potentialMeasure hφ.continuous).isOpenPosMeasure
  have hgc := continuous_coordinateGradient hφ
  have hzero : (potentialMeasure φ) (coordinateGradient φ ⁻¹' Kᶜ)=0 := by
    rwa [momentMeasure,Measure.map_apply hgc.measurable hK.measurableSet.compl] at hs
  intro x
  by_contra hx
  have hopen : IsOpen (coordinateGradient φ ⁻¹' Kᶜ) := hK.isOpen_compl.preimage hgc
  have hp := hopen.measure_pos (potentialMeasure φ) ⟨x,hx⟩
  rw [hzero] at hp
  exact lt_irrefl 0 hp

lemma indicatorDensity_compl_zero {n : ℕ} {K : Set (CoordinateSpace n)}
    (hK : MeasurableSet K) (g : CoordinateSpace n → ℝ) :
    (volume.withDensity (fun x => ENNReal.ofReal (K.indicator g x))) Kᶜ=0 := by
  rw [withDensity_apply _ hK.compl]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem hK.compl] with x hx
  simp only [mem_compl_iff] at hx
  simp only [indicator_of_notMem hx,ENNReal.ofReal_zero,Pi.zero_apply]

/-- The full gradient-image inclusion required by the regular calculus is
forced by the actual compact indicator target law. -/
theorem coordinateGradient_mem_of_indicator_transport {n : ℕ} {φ g : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 1 φ) {K : Set (CoordinateSpace n)} (hK : IsClosed K)
    (hmap : momentMeasure φ=volume.withDensity (fun x => ENNReal.ofReal (K.indicator g x))) :
    ∀ x, coordinateGradient φ x∈K := by
  apply coordinateGradient_mem_of_moment_support hφ hK
  rw [hmap]
  exact indicatorDensity_compl_zero hK.measurableSet g

/-- The regular body-target theorem with gradient-image membership,
positive-definite Hessian and Monge–Ampère all derived from genuine transport. -/
theorem smooth_moment_source_quadratic_variance {n : ℕ} {φ V : CoordinateSpace n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ ∞ φ) (hstrict : StrictConvexOn ℝ univ φ)
    {K U : Set (CoordinateSpace n)} (hK : IsCompact K) (hKc : Convex ℝ K)
    (hU : IsOpen U) (hKU : K⊆U)
    (hV : ContDiffOn ℝ 2 V U) (hVc : ConvexOn ℝ U V)
    (S : ℝ) (hHb : ∀ x i j, |coordinateHessian φ x i j|≤S)
    {μ : Measure (CoordinateSpace n)} (hmap : momentMeasure φ=μ) (hiso : covarianceMatrix μ id=1)
    (hμ : μ=volume.withDensity (fun z => ENNReal.ofReal (K.indicator (fun z => Real.exp (-V z)) z)))
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) :
    variance (matrixQuadratic B) μ≤8*Matrix.trace (B^2) := by
  have hgrad := coordinateGradient_mem_of_indicator_transport (contDiff_infty.mp hφ 1)
    hK.isClosed (hmap.trans hμ)
  exact regular_indicator_transport_quadratic_variance hφ hstrict hK hKc hU hKU hgrad
    hV hVc S hHb hmap hiso hμ B hB

end GaussianTilt.Letwin
