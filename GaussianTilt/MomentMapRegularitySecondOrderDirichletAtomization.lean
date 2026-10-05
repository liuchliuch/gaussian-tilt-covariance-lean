import GaussianTilt.MomentMapRegularitySecondOrderDirichletLimit
import Mathlib.MeasureTheory.Function.SimpleFuncDense

/-!
# Actual finite interior atomizations

Nearest-point simple functions give finite atomic measures supported in any
chosen nonempty set whose closure carries the original finite measure.
The total mass is preserved exactly, and bounded-test dominated convergence
proves genuine weak convergence. Zero-weight atoms are removed explicitly.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators Gradient NNReal ENNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

/-- The pushforward by a genuine simple function is its explicit finite
sum of Dirac masses, with weights equal to the masses of its fibers. -/
theorem map_simpleFunc_eq_sum_dirac (μ : Measure (E n)) (q : SimpleFunc (E n) (E n)) :
    μ.map q = ∑ p ∈ q.range, μ (q ⁻¹' {p}) • Measure.dirac p := by
  classical
  ext A hA
  rw [Measure.map_apply q.measurable hA, Measure.finset_sum_apply]
  have he : q ⁻¹' A = q ⁻¹' (↑(q.range.filter (fun p => p ∈ A)) : Set (E n)) := by
    ext x
    simp only [mem_preimage, Finset.mem_coe, Finset.mem_filter, q.mem_range_self, true_and]
  rw [he, ← q.sum_measure_preimage_singleton, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hpA : p ∈ A <;> simp [Measure.smul_apply, Measure.dirac_apply, hpA]

/-- Removing zero fibers gives distinct interior atoms with strictly
positive ordinary-real weights, exactly representing the pushforward. -/
theorem simpleFunc_pushforward_positive_atoms (μ : FiniteMeasure (E n))
    (hμ : (μ : Measure (E n)) univ ≠ 0) (q : SimpleFunc (E n) (E n))
    {T : Set (E n)} (hqT : ∀ x, q x ∈ T) :
    ∃ F : Finset (E n), ∃ m : E n → ℝ,
      F.Nonempty ∧ (∀ p ∈ F, p ∈ T ∧ 0 < m p) ∧
      (μ.map q : Measure (E n)) = ∑ p ∈ F, ENNReal.ofReal (m p) • Measure.dirac p := by
  classical
  let F := q.range.filter (fun p => (μ : Measure (E n)) (q ⁻¹' {p}) ≠ 0)
  let m := fun p => ((μ : Measure (E n)) (q ⁻¹' {p})).toReal
  have hsum : (∑ p ∈ q.range, (μ : Measure (E n)) (q ⁻¹' {p})) ≠ 0 := by
    rw [q.sum_range_measure_preimage_singleton]
    exact hμ
  obtain ⟨p, hp, hmp⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  refine ⟨F, m, ⟨p, Finset.mem_filter.mpr ⟨hp, hmp⟩⟩, ?_, ?_⟩
  · intro p hp
    obtain ⟨hpr, hpm⟩ := Finset.mem_filter.mp hp
    obtain ⟨x, rfl⟩ := SimpleFunc.mem_range.mp hpr
    exact ⟨hqT x, ENNReal.toReal_pos hpm (measure_ne_top _ _)⟩
  · rw [FiniteMeasure.toMeasure_map, map_simpleFunc_eq_sum_dirac]
    dsimp [F, m]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
    by_cases hp : (μ : Measure (E n)) (q ⁻¹' {p}) = 0 <;> simp [hp]

/-- Pointwise convergence of measurable maps on a finite measure gives
weak convergence of their pushforwards to that measure when the pointwise
limit is the identity. -/
theorem finiteMeasure_map_tendsto_of_ae_tendsto_id
    (μ : FiniteMeasure (E n)) {q : ℕ → E n → E n}
    (hqm : ∀ k, Measurable (q k))
    (hqt : ∀ᵐ x ∂(μ : Measure (E n)), Tendsto (fun k => q k x) atTop (𝓝 x)) :
    Tendsto (fun k => μ.map (q k)) atTop (𝓝 μ) := by
  apply FiniteMeasure.tendsto_iff_forall_lintegral_tendsto.mpr
  intro F
  have hFm : Measurable (fun x => (F x : ℝ≥0∞)) :=
    (ENNReal.continuous_coe.comp F.continuous).measurable
  simp_rw [FiniteMeasure.toMeasure_map, lintegral_map hFm (hqm _)]
  apply tendsto_lintegral_of_dominated_convergence (fun _ => (nndist F 0 : ℝ≥0∞))
  · exact fun k => hFm.comp (hqm k)
  · intro k
    exact Eventually.of_forall (fun x => by
      apply ENNReal.coe_le_coe.mpr
      exact BoundedContinuousFunction.NNReal.upper_bound F (q k x))
  · rw [lintegral_const]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top _ _)
  · filter_upwards [hqt] with x hx
    exact (ENNReal.continuous_coe.comp F.continuous).continuousAt.tendsto.comp hx

/-- Actual finite simple-function atomizations with values in the chosen
set, exact mass preservation, and weak convergence to the original measure. -/
theorem exists_interior_atomizing_maps (μ : FiniteMeasure (E n))
    {T : Set (E n)} (hT : T.Nonempty)
    (hμT : ∀ᵐ x ∂(μ : Measure (E n)), x ∈ closure T) :
    ∃ q : ℕ → SimpleFunc (E n) (E n),
      (∀ k x, q k x ∈ T) ∧
      Tendsto (fun k => μ.map (q k)) atTop (𝓝 μ) ∧
      (∀ k, (μ.map (q k) : Measure (E n)) univ = (μ : Measure (E n)) univ) := by
  obtain ⟨p, hp⟩ := hT
  let q : ℕ → SimpleFunc (E n) (E n) := SimpleFunc.approxOn id measurable_id T p hp
  have hqT (k : ℕ) (x : E n) : q k x ∈ T := SimpleFunc.approxOn_mem measurable_id hp k x
  refine ⟨q, hqT, ?_, ?_⟩
  · apply finiteMeasure_map_tendsto_of_ae_tendsto_id μ (fun k => (q k).measurable)
    filter_upwards [hμT] with x hx
    exact SimpleFunc.tendsto_approxOn measurable_id hp hx
  · intro k
    rw [FiniteMeasure.toMeasure_map, Measure.map_apply (q k).measurable MeasurableSet.univ]
    simp only [preimage_univ]

/-- Every nonzero finite measure supported on the closure of `T` is the
weak limit of explicit finite sums of positive atoms in `T`, with exactly
the same total mass. -/
theorem exists_positive_atomizations (μ : FiniteMeasure (E n))
    (hμ : (μ : Measure (E n)) univ ≠ 0) {T : Set (E n)} (hT : T.Nonempty)
    (hμT : ∀ᵐ x ∂(μ : Measure (E n)), x ∈ closure T) :
    ∃ ms : ℕ → FiniteMeasure (E n),
      Tendsto ms atTop (𝓝 μ) ∧
      (∀ k, (ms k : Measure (E n)) univ = (μ : Measure (E n)) univ) ∧
      ∀ k, ∃ F : Finset (E n), ∃ m : E n → ℝ,
        F.Nonempty ∧ (∀ p ∈ F, p ∈ T ∧ 0 < m p) ∧
        (ms k : Measure (E n)) = ∑ p ∈ F, ENNReal.ofReal (m p) • Measure.dirac p := by
  obtain ⟨q, hqT, hqt, hqm⟩ := exists_interior_atomizing_maps μ hT hμT
  refine ⟨fun k => μ.map (q k), hqt, hqm, ?_⟩
  intro k
  exact simpleFunc_pushforward_positive_atoms μ hμ (q k) (hqT k)

/-- Unit Lebesgue density on a compact domain, packaged as an actual finite
measure so its weak topology and exact mass can be used directly. -/
def compactDomainVolume (S : Set (E n)) (hS : IsCompact S) : FiniteMeasure (E n) :=
  ⟨volume.restrict S, isFiniteMeasure_restrict.mpr hS.measure_ne_top⟩

/-- The unit-density Dirichlet target admits a sequence of finite positive
interior atomizations with exactly the original volume. -/
theorem exists_unit_density_interior_atomizations {S : Set (E n)}
    (hS : IsCompact S) (hc : Convex ℝ S) (hi : (interior S).Nonempty) :
    ∃ ms : ℕ → FiniteMeasure (E n),
      Tendsto ms atTop (𝓝 (compactDomainVolume S hS)) ∧
      (∀ k, (ms k : Measure (E n)) univ = volume S) ∧
      ∀ k, ∃ F : Finset (E n), ∃ m : E n → ℝ,
        F.Nonempty ∧ (∀ p ∈ F, p ∈ interior S ∧ 0 < m p) ∧
        (ms k : Measure (E n)) = ∑ p ∈ F, ENNReal.ofReal (m p) • Measure.dirac p := by
  have hmass : (compactDomainVolume S hS : Measure (E n)) univ = volume S :=
    Measure.restrict_apply_univ S
  have hpos : volume S ≠ 0 :=
    ((isOpen_interior.measure_pos volume hi).trans_le (measure_mono interior_subset)).ne'
  have hsupport : ∀ᵐ x ∂(compactDomainVolume S hS : Measure (E n)), x ∈ closure (interior S) := by
    filter_upwards [ae_restrict_mem hS.measurableSet] with x hx
    rw [hc.closure_interior_eq_closure_of_nonempty_interior hi, hS.isClosed.closure_eq]
    exact hx
  simpa only [hmass] using exists_positive_atomizations (compactDomainVolume S hS)
    (by rwa [hmass]) hi hsupport

end GaussianTilt.MomentMapRegularity
