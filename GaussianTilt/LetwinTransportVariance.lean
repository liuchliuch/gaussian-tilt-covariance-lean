import GaussianTilt.LetwinRegularVariance
import GaussianTilt.LetwinMomentJacobianInjective

/-! # Regular variance from actual moment transport, with no assumed PDE

Positive definiteness and the Monge–Ampère equation are derived from the
actual pushforward density. Only source smoothness, strict convexity and the
uniform Hessian estimate remain as source regularity inputs.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix Set
open scoped BigOperators ContDiff ENNReal
namespace GaussianTilt.Letwin

/-- A locally continuous target potential gives a measurable density on a
measurable target body even when its values away from that body are arbitrary. -/
lemma measurable_indicator_exp_neg_of_continuousOn {n : ℕ} {V : CoordinateSpace n → ℝ}
    {K : Set (CoordinateSpace n)} (hK : MeasurableSet K) (hV : ContinuousOn V K) :
    Measurable (K.indicator (fun z => Real.exp (-V z))) := by
  classical
  have h := hV.neg.rexp.measurable_piecewise
    (show ContinuousOn (0 : CoordinateSpace n → ℝ) Kᶜ from continuous_const.continuousOn) hK
  simpa only [Set.piecewise_eq_indicator] using h

set_option maxHeartbeats 1200000 in
/-- The actual regular target variance estimate with both positive Hessian
and the pointwise MA equation proved from transport, rather than supplied. -/
theorem regular_transport_quadratic_variance {n : ℕ} {φ V : CoordinateSpace n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ ∞ φ) (hstrict : StrictConvexOn ℝ univ φ)
    {K U : Set (CoordinateSpace n)} (hK : IsCompact K) (hU : IsOpen U) (hKU : K⊆U)
    (hgrad : ∀ x, coordinateGradient φ x∈K)
    (hV : ContDiffOn ℝ 2 V U) (hVc : ConvexOn ℝ U V)
    (S : ℝ) (hHb : ∀ x i j, |coordinateHessian φ x i j|≤S)
    {μ : Measure (CoordinateSpace n)} (hmap : momentMeasure φ=μ) (hiso : covarianceMatrix μ id=1)
    {f : CoordinateSpace n → ℝ} (hf : LogConcaveMarginal.IsLogConcave f) (hfm : Measurable f)
    (hμ : μ=volume.withDensity (fun z => ENNReal.ofReal (f z)))
    (hvalue : ∀ x, f (coordinateGradient φ x)=Real.exp (-V (coordinateGradient φ x)))
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) :
    variance (matrixQuadratic B) μ≤8*Matrix.trace (B^2) := by
  have hφ2 := contDiff_infty.mp hφ 2
  have hgc := continuous_coordinateGradient (contDiff_infty.mp hφ 1)
  have hcomp : Continuous (fun x => V (coordinateGradient φ x)) :=
    hV.continuousOn.comp_continuous hgc (fun x => hKU (hgrad x))
  have hfc : Continuous (fun x => f (coordinateGradient φ x)) := by
    have heq : (fun x => f (coordinateGradient φ x)) =
        (fun x => Real.exp (-V (coordinateGradient φ x))) := funext hvalue
    rw [heq]
    exact Real.continuous_exp.comp hcomp.neg
  have hinj := coordinateGradient_injective_of_strictConvex (hφ2.differentiable (by norm_num)) hstrict
  have hH := hessian_posDef_of_injective_moment_transport hφ2 hstrict.convexOn hinj hfm hf.1 hfc (hmap.trans hμ)
  have hMA := mongeAmpere_of_moment_transport hφ2 hH hfm hf.1 hcomp hvalue (hmap.trans hμ)
  exact regular_target_quadratic_variance hφ hstrict.convexOn hH hK hU hKU hgrad hV hVc hMA
    S hHb hmap hiso hf hfm hμ B hB

/-- Indicator target potentials automatically agree with their positive
exponential density at every gradient point. This is the regular body form
used in the paper's approximation theorem. -/
theorem regular_indicator_transport_quadratic_variance {n : ℕ} {φ V : CoordinateSpace n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ ∞ φ) (hstrict : StrictConvexOn ℝ univ φ)
    {K U : Set (CoordinateSpace n)} (hK : IsCompact K) (hKc : Convex ℝ K) (hU : IsOpen U) (hKU : K⊆U)
    (hgrad : ∀ x, coordinateGradient φ x∈K)
    (hV : ContDiffOn ℝ 2 V U) (hVc : ConvexOn ℝ U V)
    (S : ℝ) (hHb : ∀ x i j, |coordinateHessian φ x i j|≤S)
    {μ : Measure (CoordinateSpace n)} (hmap : momentMeasure φ=μ) (hiso : covarianceMatrix μ id=1)
    (hμ : μ=volume.withDensity (fun z => ENNReal.ofReal (K.indicator (fun z => Real.exp (-V z)) z)))
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) :
    variance (matrixQuadratic B) μ≤8*Matrix.trace (B^2) := by
  exact regular_transport_quadratic_variance hφ hstrict hK hU hKU hgrad hV hVc S hHb hmap hiso
    (FunctionalBrascampLieb.logconcave_exp_neg_indicator (hVc.subset hKU hKc))
    (measurable_indicator_exp_neg_of_continuousOn hK.isClosed.measurableSet (hV.continuousOn.mono hKU))
    hμ (fun x => indicator_of_mem (hgrad x) _) B hB

end GaussianTilt.Letwin
