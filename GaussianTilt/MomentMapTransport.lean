import GaussianTilt.MomentMapEulerLagrange

/-! # Actual normalized moment-source transport

The constructed variational potential is normalized by its true partition.
The Euler identity then identifies the gradient pushforward as a measure,
using equality of all bounded continuous test integrals.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

namespace GaussianTilt.MomentMapCoercivity
variable {n : ℕ} {K : Set (E n)} {q : E n → ℝ} {R : ℝ}

def normalizedSourcePotential (W : VariationalWitness K q R) (x : E n) : ℝ :=
  W.potential x + Real.log (∫ y, Real.exp (-W.potential y))

def normalizedSourceMeasure (W : VariationalWitness K q R) : Measure (E n) :=
  volume.withDensity (fun x ↦ ENNReal.ofReal (Real.exp (-normalizedSourcePotential W x)))

lemma normalizedSource_continuous (W : VariationalWitness K q R) :
    Continuous (normalizedSourcePotential W) := W.lipschitz.continuous.add continuous_const

lemma normalizedSource_convex (W : VariationalWitness K q R) :
    ConvexOn ℝ univ (normalizedSourcePotential W) := W.convex.add_const _

lemma normalizedSource_lipschitz (W : VariationalWitness K q R) :
    LipschitzWith R.toNNReal (normalizedSourcePotential W) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [normalizedSourcePotential, dist_add_right] using W.lipschitz.dist_le_mul x y

instance normalizedSource_probability (W : VariationalWitness K q R) :
    IsProbabilityMeasure (normalizedSourceMeasure W) :=
  (probability_normalized_convex_potential W.lipschitz.continuous W.convex W.source_integrable).2.2

lemma gradient_normalizedSource (W : VariationalWitness K q R) :
    gradient (normalizedSourcePotential W) = gradient W.potential := by
  funext x
  simp only [gradient]
  congr 1
  change fderiv ℝ (fun y ↦ W.potential y + Real.log (∫ z, Real.exp (-W.potential z))) x = _
  exact fderiv_add_const _

lemma normalizedSource_density (W : VariationalWitness K q R) (x : E n) :
    Real.exp (-normalizedSourcePotential W x) =
      Real.exp (-W.potential x) / (∫ y, Real.exp (-W.potential y)) := by
  unfold normalizedSourcePotential
  rw [show -(W.potential x + Real.log (∫ y, Real.exp (-W.potential y))) =
    -W.potential x - Real.log (∫ y, Real.exp (-W.potential y)) by ring,
    Real.exp_sub, Real.exp_log (integral_exp_pos W.source_integrable)]

lemma integral_normalizedSource (W : VariationalWitness K q R) (g : E n → ℝ) :
    (∫ x, g x ∂normalizedSourceMeasure W) =
      (∫ x, g x * Real.exp (-W.potential x)) / (∫ y, Real.exp (-W.potential y)) := by
  have hm : Measurable (fun x ↦ ENNReal.ofReal (Real.exp (-normalizedSourcePotential W x))) :=
    ((Real.continuous_exp.comp (normalizedSource_continuous W).neg).measurable.ennreal_ofReal)
  rw [normalizedSourceMeasure, integral_withDensity_eq_integral_toReal_smul
    (μ := volume) (f := fun x ↦ ENNReal.ofReal (Real.exp (-normalizedSourcePotential W x))) hm
    (ae_of_all _ (fun _ ↦ ENNReal.ofReal_lt_top)) g]
  simp only [ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul]
  simp_rw [normalizedSource_density W, div_mul_eq_mul_div]
  rw [integral_div]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ (fun x ↦ mul_comm _ _)

theorem normalizedSource_gradient_transport
    (W : VariationalWitness K q R) (hKc : IsCompact K) (hKn : K.Nonempty)
    {r c : ℝ} (hK : ∀ y ∈ K, ‖y‖ ≤ R) (hball : Metric.closedBall (0 : E n) r ⊆ K)
    (hq0 : ∀ y, 0 ≤ q y) (hqm : Measurable q) (hqi : Integrable q)
    (hqs : ∀ y ∉ K, q y = 0) (hc : 0 < c) (hr : 0 < r)
    (hqlower : ∀ y ∈ Metric.ball (0 : E n) (3 * r), c ≤ q y)
    [IsProbabilityMeasure (volume.withDensity (fun y ↦ ENNReal.ofReal (q y)))]
    (hmean : (∫ y : E n, y ∂volume.withDensity (fun y ↦ ENNReal.ofReal (q y))) = 0) :
    (normalizedSourceMeasure W).map (gradient (normalizedSourcePotential W)) =
      volume.withDensity (fun y ↦ ENNReal.ofReal (q y)) := by
  rw [gradient_normalizedSource]
  letI : IsProbabilityMeasure ((normalizedSourceMeasure W).map (gradient W.potential)) :=
    Measure.isProbabilityMeasure_map (measurable_actual_gradient W.potential).aemeasurable
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro b
  rw [integral_map (measurable_actual_gradient W.potential).aemeasurable b.continuous.aestronglyMeasurable,
    integral_normalizedSource]
  exact moment_source_euler_identity W hKc hKn hK hball hq0 hqm hqi hqs hc hr hqlower hmean
    b.continuous (M := ‖b‖₊) (fun y _ ↦ by simpa only [Real.norm_eq_abs] using b.norm_coe_le_norm y)

/-- Genuine weak moment-map existence from the regular target's natural
density hypotheses. Smooth source regularity is a separate proved/PDE task. -/
theorem exists_normalized_moment_source
    {r c : ℝ} (hKc : IsCompact K) (hK : ∀ y ∈ K, ‖y‖ ≤ R)
    (hball : Metric.closedBall (0 : E n) r ⊆ K)
    (hq0 : ∀ y, 0 ≤ q y) (hqm : Measurable q) (hqi : Integrable q)
    (hqmass : (∫ y, q y) = 1) (hqs : ∀ y ∉ K, q y = 0) (hc : 0 < c) (hr : 0 < r)
    (hqlower : ∀ y ∈ Metric.ball (0 : E n) (3 * r), c ≤ q y)
    [IsProbabilityMeasure (volume.withDensity (fun y ↦ ENNReal.ofReal (q y)))]
    (hmean : (∫ y : E n, y ∂volume.withDensity (fun y ↦ ENNReal.ofReal (q y))) = 0) :
    ∃ φ : E n → ℝ, LipschitzWith R.toNNReal φ ∧ ConvexOn ℝ univ φ ∧
      IsProbabilityMeasure (volume.withDensity (fun x ↦ ENNReal.ofReal (Real.exp (-φ x)))) ∧
      (volume.withDensity (fun x ↦ ENNReal.ofReal (Real.exp (-φ x)))).map (gradient φ) =
        volume.withDensity (fun y ↦ ENNReal.ofReal (q y)) := by
  obtain ⟨W⟩ := exists_variationalWitness hKc hK hball hq0 hqm hqi hqmass hqs hc hr hqlower
  refine ⟨normalizedSourcePotential W, normalizedSource_lipschitz W,
    normalizedSource_convex W, normalizedSource_probability W, ?_⟩
  exact normalizedSource_gradient_transport W hKc
    ⟨0, hball (Metric.mem_closedBall_self hr.le)⟩ hK hball hq0 hqm hqi hqs hc hr hqlower hmean

end GaussianTilt.MomentMapCoercivity
