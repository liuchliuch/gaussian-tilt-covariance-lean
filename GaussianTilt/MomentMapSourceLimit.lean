import GaussianTilt.MomentMapMaximizingSequence

/-! # Partition convergence for constructed source limits

The proved budget bound gives one integrable Laplace majorant for the entire
maximizing sequence. Dominated convergence proves convergence of the actual
source densities and partitions, and the limiting convex potential can be
normalized to an actual probability density.

Identification of its gradient pushforward with the target remains the
Euler--Lagrange step; this file does not assume or claim that identification.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators
namespace GaussianTilt.MomentMapCoercivity
variable {n : ℕ}

theorem source_partition_tendsto_of_bounded_budget
    {K : Set (E n)} {q : E n → ℝ} {u : ℕ → E n → ℝ} {ψ : E n → ℝ} {R r c M : ℝ}
    (hK : ∀ y ∈ K, ‖y‖ ≤ R) (hball : Metric.closedBall (0 : E n) r ⊆ K)
    (hq0 : ∀ y, 0 ≤ q y) (hc : 0 < c) (hr : 0 < r) (hM : 0 ≤ M)
    (hqlower : ∀ y ∈ Metric.ball (0 : E n) (3 * r), c ≤ q y)
    (hu : ∀ k, DualAdmissible q (u k)) (hbudget : ∀ k, dualBudget q (u k) ≤ M)
    (hψ : Continuous ψ)
    (hpoint : ∀ x, Tendsto (fun k => fenchel K (u k) x) atTop (𝓝 (ψ x))) :
    Integrable (fun x => Real.exp (-ψ x)) ∧
      0 < (∫ x, Real.exp (-ψ x)) ∧
      Tendsto (fun k => dualPartition K (u k)) atTop (𝓝 (∫ x, Real.exp (-ψ x))) := by
  let v := (volume (Metric.ball (0 : E n) r)).toReal
  let B := M / (c * v)
  have hv : 0 < v := ENNReal.toReal_pos
    (Metric.isOpen_ball.measure_pos volume ⟨0, Metric.mem_ball_self hr⟩).ne'
    (ne_top_of_le_ne_top (isCompact_closedBall (0 : E n) r).measure_ne_top
      (measure_mono Metric.ball_subset_closedBall))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hub (k : ℕ) : ∀ y ∈ Metric.closedBall (0 : E n) r, u k y ≤ B := by
    intro y hy
    exact (le_abs_self _).trans (convex_inner_ball_bound (hu k).1 (hu k).2.1 (hu k).2.2.1
      hq0 (hu k).2.2.2.2 hc hr hqlower (hbudget k) y
      (Metric.closedBall_subset_ball (by linarith : r < 2 * r) hy))
  let a := r / ((B + 1) * ((n : ℝ) + 1))
  let g : E n → ℝ := fun x => Real.exp 1 * laplaceProduct a x
  have ha : 0 < a := by dsimp [a]; positivity
  have hgi : Integrable g := (integrable_laplaceProduct ha).const_mul _
  have hbound (k : ℕ) (x : E n) : Real.exp (-fenchel K (u k) x) ≤ g x :=
    fenchel_density_laplace_bound hK (fun y _ => (hu k).2.2.1 y) hr hB hball (hu k).2.2.2.1 (hub k) x
  have hlim (x : E n) : Tendsto (fun k => Real.exp (-fenchel K (u k) x)) atTop (𝓝 (Real.exp (-ψ x))) :=
    Real.continuous_exp.continuousAt.tendsto.comp (hpoint x).neg
  have hboundψ (x : E n) : Real.exp (-ψ x) ≤ g x := le_of_tendsto (hlim x)
    (Filter.Eventually.of_forall (fun k => hbound k x))
  have hi : Integrable (fun x => Real.exp (-ψ x)) := hgi.mono'
    (Real.continuous_exp.comp hψ.neg).aestronglyMeasurable (ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hboundψ x))
  refine ⟨hi, integral_exp_pos hi, ?_⟩
  apply tendsto_integral_of_dominated_convergence g
  · intro k
    exact (Real.continuous_exp.comp (fenchel_lipschitz
      ⟨0, hball (Metric.mem_closedBall_self hr.le)⟩ hK (fun y _ => (hu k).2.2.1 y)).continuous.neg).aestronglyMeasurable
  · exact hgi
  · intro k
    exact ae_of_all _ (fun x => by rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hbound k x)
  · exact ae_of_all _ hlim

theorem probability_normalized_convex_potential {ψ : E n → ℝ}
    (hψ : Continuous ψ) (hc : ConvexOn ℝ univ ψ)
    (hi : Integrable (fun x => Real.exp (-ψ x))) :
    let φ := fun x => ψ x + Real.log (∫ y, Real.exp (-ψ y))
    Continuous φ ∧ ConvexOn ℝ univ φ ∧
      IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x)))) := by
  dsimp only
  have hp := integral_exp_pos hi
  have heq : (fun x => Real.exp (-(ψ x + Real.log (∫ y, Real.exp (-ψ y))))) =
      fun x => Real.exp (-ψ x) / (∫ y, Real.exp (-ψ y)) := by
    funext x
    rw [show -(ψ x + Real.log (∫ y, Real.exp (-ψ y))) =
      -ψ x - Real.log (∫ y, Real.exp (-ψ y)) by ring, Real.exp_sub, Real.exp_log hp]
  refine ⟨hψ.add continuous_const, hc.add_const _, ?_⟩
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  simp_rw [funext_iff.mp heq]
  rw [← ofReal_integral_eq_lintegral_ofReal (hi.div_const _)
      (ae_of_all _ (fun x => div_nonneg (Real.exp_nonneg _) hp.le)), integral_div, div_self hp.ne']
  simp

/-- The direct-method construction produces a normalized, finite convex
source candidate and a maximizing sequence whose source partitions really
converge to its unnormalized partition. -/
theorem exists_normalized_source_candidate
    {K : Set (E n)} {q : E n → ℝ} {R r c : ℝ}
    (hK : ∀ y ∈ K, ‖y‖ ≤ R) (hball : Metric.closedBall (0 : E n) r ⊆ K)
    (hq0 : ∀ y, 0 ≤ q y) (hc : 0 < c) (hr : 0 < r)
    (hqlower : ∀ y ∈ Metric.ball (0 : E n) (3 * r), c ≤ q y) :
    ∃ u : ℕ → E n → ℝ, ∃ ψ : E n → ℝ,
      (∀ k, DualAdmissible q (u k)) ∧
      Tendsto (fun k => dualObjective K q (u k)) atTop (𝓝 (sSup (dualValues K q))) ∧
      ConvexOn ℝ univ ψ ∧ Continuous ψ ∧ ψ 0 = 0 ∧
      Integrable (fun x => Real.exp (-ψ x)) ∧
      Tendsto (fun k => dualPartition K (u k)) atTop (𝓝 (∫ x, Real.exp (-ψ x))) ∧
      IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal
        (Real.exp (-(ψ x + Real.log (∫ y, Real.exp (-ψ y))))))) := by
  obtain ⟨u, ψ, M, hM, hu, hbudget, hobj, hψ, hψ0, hψc, hloc, hpoint⟩ :=
    exists_maximizing_sequence_with_source_limit hK hball hq0 hc hr hqlower
  obtain ⟨hi, hp, hZ⟩ := source_partition_tendsto_of_bounded_budget
    hK hball hq0 hc hr hM hqlower hu hbudget hψ.continuous hpoint
  exact ⟨u, ψ, hu, hobj, hψc, hψ.continuous, hψ0, hi, hZ,
    (probability_normalized_convex_potential hψ.continuous hψc hi).2.2⟩

end GaussianTilt.MomentMapCoercivity
