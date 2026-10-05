import GaussianTilt.MomentMapPerturbedPotential
import GaussianTilt.MomentMapPartitionDerivative
import GaussianTilt.MomentMapVariationalComparison

/-! # Euler--Lagrange identity of the constructed source potential

Actual bounded target perturbations, extended Danskin differentiation, and
the proved feasible-pair variational comparison identify the gradient
pushforward. All integrations refer to the constructed source density.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators InnerProductSpace
namespace GaussianTilt.MomentMapCoercivity
variable {n : ℕ} {K : Set (E n)} {q : E n → ℝ} {R r c : ℝ}

lemma measurable_actual_gradient (ψ : E n → ℝ) : Measurable (gradient ψ) :=
  (InnerProductSpace.toDual ℝ (E n)).symm.continuous.measurable.comp (measurable_fderiv ℝ ψ)

lemma density_ae_mem_target (hKc : IsCompact K) (hqs : ∀ y ∉ K, q y = 0) :
    ∀ᵐ y ∂volume.withDensity (fun y => ENNReal.ofReal (q y)), y ∈ K := by
  apply ae_iff.mpr
  change (volume.withDensity (fun y => ENNReal.ofReal (q y))) Kᶜ = 0
  rw [withDensity_apply _ hKc.measurableSet.compl]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem hKc.measurableSet.compl] with y hy
  simp only [hqs y hy, ENNReal.ofReal_zero, Pi.zero_apply]

theorem perturbedSource_ae_hasDerivAt
    (W : VariationalWitness K q R) (hKc : IsCompact K)
    {b : E n → ℝ} (hb : Continuous b) :
    ∀ᵐ x ∂volume, HasDerivAt (fun t => perturbedSource K W.potential b t x)
      (-b (gradient W.potential x)) 0 := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  filter_upwards [W.ae_gradient_maximizer] with x hx
  exact hasDerivAt_extendedCompactEnvelope
    ((momentPayoff_upperSemicontinuous W.nonneg x).comp_continuous continuous_subtype_val)
    (hb.comp continuous_subtype_val) (y₀ := ⟨gradient W.potential x, hx.1⟩) hx.2.1
    (fun y : K => momentPayoff_le W.nonneg x y)
    (fun y hy => Subtype.ext (hx.2.2 y y.property hy))

theorem moment_source_euler_identity
    (W : VariationalWitness K q R) (hKc : IsCompact K) (hKn : K.Nonempty)
    (hK : ∀ y ∈ K, ‖y‖ ≤ R) (hball : Metric.closedBall (0 : E n) r ⊆ K)
    (hq0 : ∀ y, 0 ≤ q y) (hqm : Measurable q) (hqi : Integrable q)
    (hqs : ∀ y ∉ K, q y = 0) (hc : 0 < c) (hr : 0 < r)
    (hqlower : ∀ y ∈ Metric.ball (0 : E n) (3 * r), c ≤ q y)
    [IsProbabilityMeasure (volume.withDensity (fun y => ENNReal.ofReal (q y)))]
    (hmean : (∫ y : E n, y ∂volume.withDensity (fun y => ENNReal.ofReal (q y))) = 0)
    {b : E n → ℝ} (hb : Continuous b) {M : ℝ≥0} (hM : ∀ y ∈ K, |b y| ≤ M) :
    (∫ x, b (gradient W.potential x) * Real.exp (-W.potential x)) /
        (∫ x, Real.exp (-W.potential x)) =
      ∫ y, b y ∂volume.withDensity (fun y => ENNReal.ofReal (q y)) := by
  let μ := volume.withDensity (fun y => ENNReal.ofReal (q y))
  let B := ∫ y, b y ∂μ
  let I := ∫ y, (extendedDual W.potential y).toReal ∂μ
  let Z := ∫ x, Real.exp (-W.potential x)
  let Φ := perturbedSource K W.potential b
  have hZ : 0 < Z := integral_exp_pos W.source_integrable
  have hμK : ∀ᵐ y ∂μ, y ∈ K := density_ae_mem_target hKc hqs
  have hbi : Integrable b μ := by
    apply Integrable.of_bound hb.aestronglyMeasurable (M : ℝ)
    filter_upwards [hμK] with y hy
    simpa only [Real.norm_eq_abs] using hM y hy
  have hw (t : ℝ) : Integrable (fun y => (extendedDual W.potential y).toReal + t * b y) μ :=
    W.dual_integrable.add (hbi.const_mul t)
  have hYoung (t : ℝ) : ∀ᵐ y ∂μ, ∀ x,
      ⟪x, y⟫_ℝ ≤ Φ t x + ((extendedDual W.potential y).toReal + t * b y) := by
    filter_upwards [hμK, W.dual_ae_finite] with y hy hfin
    intro x
    have h := finite_payoff_le_perturbedSource W hKc hKn hK hM t x hy hfin.ne
    dsimp [Φ]
    linarith
  have hmax (t : ℝ) : Real.log (∫ x, Real.exp (-Φ t x)) - t * B ≤ Real.log Z := by
    have h := feasible_pair_le_dual_supremum hK hball hq0 hqm hqi hqs hc hr hqlower hmean
      (perturbedSource_lipschitz W hKc hKn hK hM t).continuous
      (perturbedSource_convex W hKc hKn hK hM t)
      (perturbedSource_exp_integrable W hKc hKn hK hM t) (hw t) (hYoung t)
    rw [integral_add W.dual_integrable (hbi.const_mul t), integral_const_mul] at h
    have hW := W.objective_eq_sup
    change Real.log Z - I = sSup (dualValues K q) at hW
    change Real.log (∫ x, Real.exp (-Φ t x)) - (I + t * B) ≤ sSup (dualValues K q) at h
    linarith
  have hΦ0 : Φ 0 = W.potential := funext (perturbedSource_zero W hKc hKn hK hM)
  have hΦmeas (t : ℝ) : AEStronglyMeasurable (Φ t) volume :=
    (perturbedSource_lipschitz W hKc hKn hK hM t).continuous.aestronglyMeasurable
  have hi0 : Integrable (fun x => Real.exp (-Φ 0 x)) := by rw [hΦ0]; exact W.source_integrable
  have hZ0 : 0 < ∫ x, Real.exp (-Φ 0 x) := by rw [hΦ0]; exact hZ
  have hdmeas : AEStronglyMeasurable (fun x => -b (gradient W.potential x)) volume :=
    (hb.measurable.comp (measurable_actual_gradient W.potential)).neg.aestronglyMeasurable
  have hD := logPartition_hasDerivAt_of_lipschitz volume (M := M) hΦmeas hi0 hZ0 hdmeas
    (ae_of_all _ (perturbedSource_parameter_lipschitz W hKc hKn hK hM))
    (perturbedSource_ae_hasDerivAt W hKc hb)
  simp only [neg_neg, hΦ0] at hD
  have hF := hD.sub ((hasDerivAt_id (0 : ℝ)).mul_const B)
  have hlocal : IsLocalMax (fun t => Real.log (∫ x, Real.exp (-Φ t x)) - t * B) 0 := by
    apply Filter.Eventually.of_forall
    intro t
    simpa only [zero_mul, sub_zero, hΦ0] using hmax t
  have hz := hlocal.hasDerivAt_eq_zero hF
  simp only [one_mul] at hz
  change (∫ x, b (gradient W.potential x) * Real.exp (-W.potential x)) / Z - B = 0 at hz
  change (∫ x, b (gradient W.potential x) * Real.exp (-W.potential x)) / Z = B
  linarith

end GaussianTilt.MomentMapCoercivity
