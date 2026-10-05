import GaussianTilt.MomentMapMomentDuality

/-! # The constructed variational witness for regular target measures

This packages only proved conclusions of the direct method: normalized
convex source candidate, actual target-integrable extended conjugate,
attainment of the dual supremum, pointwise Fenchel recovery, and a.e. unique
gradient maximizers. The gradient-pushforward identity is the remaining
Euler--Lagrange conclusion and is deliberately not a field of this witness.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators
namespace GaussianTilt.MomentMapCoercivity
variable {n : ℕ}

structure VariationalWitness (K : Set (E n)) (q : E n → ℝ) (R : ℝ) where
  potential : E n → ℝ
  lipschitz : LipschitzWith R.toNNReal potential
  convex : ConvexOn ℝ univ potential
  zero_at_origin : potential 0 = 0
  nonneg : ∀ x, 0 ≤ potential x
  source_integrable : Integrable (fun x => Real.exp (-potential x))
  dual_integrable : Integrable (fun y => (extendedDual potential y).toReal)
    (volume.withDensity (fun y => ENNReal.ofReal (q y)))
  dual_ae_finite : ∀ᵐ y ∂volume.withDensity (fun y => ENNReal.ofReal (q y)), extendedDual potential y < ⊤
  objective_eq_sup : Real.log (∫ x, Real.exp (-potential x)) -
    (∫ y, (extendedDual potential y).toReal ∂volume.withDensity (fun y => ENNReal.ofReal (q y))) =
    sSup (dualValues K q)
  recovered_lower : ∀ k x, potential x ≤ fenchel K (recoveredDual potential k) x
  ae_gradient_maximizer : ∀ᵐ x ∂volume, gradient potential x ∈ K ∧
    momentPayoff potential x (gradient potential x) = (potential x : EReal) ∧
    ∀ y ∈ K, momentPayoff potential x y = (potential x : EReal) → y = gradient potential x

/-- All variational, compactness, conjugate-integral, and unique-gradient
data are constructed from the regular target's natural density hypotheses. -/
theorem exists_variationalWitness
    {K : Set (E n)} {q : E n → ℝ} {R r c : ℝ}
    (hKc : IsCompact K) (hK : ∀ y ∈ K, ‖y‖ ≤ R)
    (hball : Metric.closedBall (0 : E n) r ⊆ K)
    (hq0 : ∀ y, 0 ≤ q y) (hqm : Measurable q) (hqi : Integrable q) (hqmass : (∫ y, q y) = 1)
    (hqs : ∀ y ∉ K, q y = 0) (hc : 0 < c) (hr : 0 < r)
    (hqlower : ∀ y ∈ Metric.ball (0 : E n) (3 * r), c ≤ q y) :
    Nonempty (VariationalWitness K q R) := by
  have hKn : K.Nonempty := ⟨0, hball (Metric.mem_closedBall_self hr.le)⟩
  obtain ⟨u, ψ, M, hM, hu, hbudget, hobj, hψ, hψ0, hψc, hloc, hpoint⟩ :=
    exists_maximizing_sequence_with_source_limit hK hball hq0 hc hr hqlower
  obtain ⟨hi, hp, hZ⟩ := source_partition_tendsto_of_bounded_budget
    hK hball hq0 hc hr hM hqlower hu hbudget hψ.continuous hpoint
  have hψnonneg (x : E n) : 0 ≤ ψ x := ge_of_tendsto' (hpoint x)
    (fun k => fenchel_nonneg hK (fun y _ => (hu k).2.2.1 y)
      (hball (Metric.mem_closedBall_self hr.le)) (hu k).2.2.2.1 x)
  have hrecbud := recoveredDual_budget_tendsto hK hball hq0 hqi hqmass hqs hc hr hqlower
    hu hψ0 hψnonneg hi hloc hZ hobj
  obtain ⟨hdi, hdeq⟩ := extendedDual_integral_eq_budget_limit hq0 hqm hqi hK hqs hψ0 hψnonneg hrecbud
  have hpart := recoveredDual_partition_le_limit hK hball hq0 hqi hqmass hqs hc hr hqlower
    hu hψ0 hψnonneg hloc hZ hp hobj
  have hφi (k : ℕ) : Integrable (fun x => Real.exp (-fenchel K (recoveredDual ψ k) x)) := by
    have hv := recoveredDual_admissible hq0 hqi hK hqs hψ0 hψnonneg k
    have hpos := (dualPartition_polynomial_bound hK hball hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.1
      hq0 hv.2.2.2.2 hc hr hqlower).1
    by_contra hn
    rw [dualPartition, integral_undef hn] at hpos
    exact lt_irrefl _ hpos
  have hrecovery := recovered_source_ge_source_of_partition_bound
    hKn hK hψ0 hψnonneg hψ.continuous hi hφi hpart
  refine ⟨⟨ψ, hψ, hψc, hψ0, hψnonneg, hi, hdi,
    extendedDual_ae_finite_of_budget_limit hq0 hqm hqi hK hqs hψ0 hψnonneg hrecbud, ?_, hrecovery,
    ae_gradient_is_unique_momentPayoff_maximizer hKc hKn hK hψ0 hψnonneg hψc hrecovery⟩⟩
  rw [hdeq]
  ring

end GaussianTilt.MomentMapCoercivity
