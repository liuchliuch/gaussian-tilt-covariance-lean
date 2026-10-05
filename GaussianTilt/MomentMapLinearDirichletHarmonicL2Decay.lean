import GaussianTilt.MomentMapLinearDirichletHarmonicL2Scaling

/-! # Genuine full-ball harmonic mean-square excess decay -/
noncomputable section
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 1000
open MeasureTheory Set Filter
open scoped Topology ContDiff BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma euclidean_norm_sub_sq (H q : KernelSpace n) : ‖H-q‖^2=∑ i, (H i-q i)^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs,sq_abs,PiLp.sub_apply]

lemma integrableOn_euclidean_excess_of_coordinate_memLp {H : KernelSpace n → KernelSpace n}
    (hH : ∀ i, MemLp (fun x => H x i) 2 volume) (q a : KernelSpace n) (r : ℝ) :
    IntegrableOn (fun x => ‖H x-q‖^2) (Metric.ball a r) volume := by
  letI : Fact (volume (Metric.ball a r) < (⊤:ℝ≥0∞)) := ⟨measure_ball_lt_top⟩
  have hi (i : Fin n) : IntegrableOn (fun x => (H x i-q i)^2) (Metric.ball a r) volume :=
    (((hH i).mono_measure Measure.restrict_le_self).sub (memLp_const (q i))).integrable_sq
  simp_rw [euclidean_norm_sub_sq]
  exact integrable_finset_sum _ (fun i _ => hi i)

lemma integral_euclidean_excess_eq_sum {H : KernelSpace n → KernelSpace n}
    (hH : ∀ i, MemLp (fun x => H x i) 2 volume) (q a : KernelSpace n) (r : ℝ) :
    (∫ x in Metric.ball a r, ‖H x-q‖^2)=∑ i, ∫ x in Metric.ball a r, (H x i-q i)^2 := by
  letI : Fact (volume (Metric.ball a r) < (⊤:ℝ≥0∞)) := ⟨measure_ball_lt_top⟩
  simp_rw [euclidean_norm_sub_sq]
  exact integral_finset_sum _ (fun i _ =>
    (((hH i).mono_measure Measure.restrict_le_self).sub (memLp_const (q i))).integrable_sq)

/-- Each actual harmonic component is controlled by the proved scalar
kernel estimate. Integration and exact ball volume yield the exponent
n+2, uniformly for every subtracted constant vector. -/
theorem exists_harmonic_vector_L2_excess_decay [NeZero n] :
    ∃ C : ℝ, 0 < C ∧ ∀ H : KernelSpace n → KernelSpace n,
      (∀ i, MemLp (fun x => H x i) 2 volume) →
      ∀ a : KernelSpace n, ∀ R : ℝ, 0 < R →
      (∀ i x, x ∈ Metric.ball a R → ContDiffAt ℝ ∞ (fun y => H y i) x) →
      (∀ i x, x ∈ Metric.ball a R → kernelLaplacian (fun y => H y i) x=0) →
      ∀ q : KernelSpace n, ∀ r : ℝ, 0 < r → r ≤ R/2 →
        (∫ x in Metric.ball a r, ‖H x-H a‖^2) ≤
          C*(r/R)^(n+2)*(∫ x in Metric.ball a R, ‖H x-q‖^2) := by
  obtain ⟨K,hK,hOsc⟩ := exists_harmonic_L2_oscillation_bound_scaled (n := n)
  let V := volume.real (Metric.ball (0:KernelSpace n) 1)
  have hV : 0 < V := ENNReal.toReal_pos (Metric.measure_ball_pos volume _ zero_lt_one).ne' measure_ball_lt_top.ne
  refine ⟨K*V,mul_pos hK hV,?_⟩
  intro H hH a R hR hs hhar q r hr hrR
  let E := ∫ x in Metric.ball a R, ‖H x-q‖^2
  have hE : 0 ≤ E := integral_nonneg (fun _ => sq_nonneg _)
  have hpt (x : KernelSpace n) (hx : x ∈ Metric.ball a r) :
      ‖H x-H a‖^2 ≤ K*(R^(n+2))⁻¹*E*r^2 := by
    rw [euclidean_norm_sub_sq]
    have hxR := Metric.ball_subset_ball hrR hx
    have haR : a ∈ Metric.ball a (R/2) := Metric.mem_ball_self (half_pos hR)
    have hh (i : Fin n) := hOsc (fun z => H z i) (hH i) a R hR (hs i) (hhar i) (q i) x hxR a haR
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hh i)
    have he : (∑ i : Fin n, K*(R^(n+2))⁻¹*(∫ z in Metric.ball a R, (H z i-q i)^2)*‖x-a‖^2)=
        K*(R^(n+2))⁻¹*E*‖x-a‖^2 := by
      rw [← Finset.sum_mul,← Finset.mul_sum,← integral_euclidean_excess_eq_sum hH q a R]
    have hxr : ‖x-a‖ < r := hx
    rw [he] at hsum
    exact hsum.trans (mul_le_mul_of_nonneg_left (by nlinarith [norm_nonneg (x-a)]) (by positivity))
  have hInt := integrableOn_euclidean_excess_of_coordinate_memLp hH (H a) a r
  have hb := setIntegral_mono_on hInt (integrableOn_const measure_ball_lt_top.ne)
    Metric.isOpen_ball.measurableSet hpt
  simp only [integral_const,measureReal_restrict_apply_univ,smul_eq_mul] at hb
  rw [real_volume_euclidean_ball a hr.le] at hb
  convert hb using 1
  dsimp only [V,E]
  rw [div_pow,pow_add]
  ring

end GaussianTilt.MomentMapLinearDirichlet
