import GaussianTilt.MomentMapRegularTargetGeometry
import GaussianTilt.MomentMapTransport

/-! # Constructed moment-source existence for the regular target class

From a centered probability density that is continuous and strictly positive
on a bounded open convex support, this file constructs a globally finite
convex Lipschitz potential whose normalized exponential measure has the
specified gradient pushforward. The inner-ball geometry, variational direct
method, convex a.e. differentiation, dual attainment, Euler--Lagrange
calculus, and measure identification are all proved in the imported chain.

Smoothness, positive-definite Hessian, and the classical Monge--Ampère
equation are subsequent regularity conclusions, not claims made here.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal
namespace GaussianTilt.MomentMapCoercivity
variable {n : ℕ}

/-- Actual moment-source existence for the regular target class, with no
moment-potential, variational, or transport existence premise. -/
theorem exists_moment_source_of_regular_density {K : Set (E n)} {q : E n → ℝ}
    (hKo : IsOpen K) (hKc : Convex ℝ K) (hKb : Bornology.IsBounded K)
    (hqm : Measurable q) (hqc : ContinuousOn q K) (hqp : ∀ y ∈ K, 0 < q y)
    (hqs : ∀ y ∉ K, q y = 0)
    [IsProbabilityMeasure (volume.withDensity (fun y => ENNReal.ofReal (q y)))]
    (hmean : (∫ y : E n, y ∂volume.withDensity (fun y => ENNReal.ofReal (q y))) = 0) :
    ∃ φ : E n → ℝ, ∃ L : ℝ≥0, LipschitzWith L φ ∧ ConvexOn ℝ univ φ ∧
      IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x)))) ∧
      (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x)))).map (gradient φ) =
        volume.withDensity (fun y => ENNReal.ofReal (q y)) := by
  have hq0 (y : E n) : 0 ≤ q y := by
    by_cases hy : y ∈ K
    · exact (hqp y hy).le
    · rw [hqs y hy]
  have hqmass := MomentMapApproximation.integral_density_eq_one hq0 hqm
  have hqi := integrable_of_integral_eq_one hqmass
  obtain ⟨R, r, c, hr, hc, hclosed, hR, hball, hlower⟩ :=
    regular_target_variational_constants hKo hKc hKb hqm hqc hqp hqs hmean
  have hqoutside : ∀ y ∉ closure K, q y = 0 := fun y hy => hqs y (fun hyK => hy (subset_closure hyK))
  obtain ⟨φ, hLip, hconv, hprob, hmap⟩ := exists_normalized_moment_source
    hclosed hR hball hq0 hqm hqi hqmass hqoutside hc hr hlower hmean
  exact ⟨φ, R.toNNReal, hLip, hconv, hprob, hmap⟩

/-- The literal exponential-on-open-convex-support formulation used by
Letwin's regularity reduction. Continuity of `V` is enough for existence;
its higher smoothness is reserved for the regularity theorem. -/
theorem exists_moment_source_for_regular_target {K : Set (E n)} {V : E n → ℝ}
    (hKo : IsOpen K) (hKc : Convex ℝ K) (hKb : Bornology.IsBounded K) (hV : ContinuousOn V K)
    [IsProbabilityMeasure (volume.withDensity (fun y => ENNReal.ofReal (regularTargetDensity K V y)))]
    (hmean : (∫ y : E n, y ∂volume.withDensity (fun y => ENNReal.ofReal (regularTargetDensity K V y))) = 0) :
    ∃ φ : E n → ℝ, ∃ L : ℝ≥0, LipschitzWith L φ ∧ ConvexOn ℝ univ φ ∧
      IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x)))) ∧
      (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x)))).map (gradient φ) =
        volume.withDensity (fun y => ENNReal.ofReal (regularTargetDensity K V y)) :=
  exists_moment_source_of_regular_density hKo hKc hKb
    (regularTargetDensity_measurable hKo.measurableSet hV)
    (regularTargetDensity_continuousOn hV)
    (fun y hy => regularTargetDensity_positive V hy)
    (fun y hy => regularTargetDensity_zero_off V hy) hmean

end GaussianTilt.MomentMapCoercivity
