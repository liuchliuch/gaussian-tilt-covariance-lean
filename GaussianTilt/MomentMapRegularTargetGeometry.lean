import GaussianTilt.MomentMapEulerLagrange

/-! # Deriving the variational geometry from regular centered targets

The target's barycenter belongs to its open convex support. Positivity and
continuity of its actual density then construct the positive inner ball and
density lower bound required by the direct method.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators
namespace GaussianTilt.MomentMapCoercivity
variable {n : ℕ}

lemma density_ae_mem_of_zero_off {q : E n → ℝ} {K : Set (E n)}
    (hK : MeasurableSet K) (hqs : ∀ y ∉ K, q y = 0) :
    ∀ᵐ y ∂volume.withDensity (fun y => ENNReal.ofReal (q y)), y ∈ K := by
  apply ae_iff.mpr
  change (volume.withDensity (fun y => ENNReal.ofReal (q y))) Kᶜ = 0
  rw [withDensity_apply _ hK.compl]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem hK.compl] with y hy
  simp only [hqs y hy, ENNReal.ofReal_zero, Pi.zero_apply]

lemma density_set_pos_of_positive_on {q : E n → ℝ} (hqm : Measurable q)
    {S : Set (E n)} (hSpos : 0 < volume S) (hqp : ∀ y ∈ S, 0 < q y) :
    0 < (volume.withDensity (fun y => ENNReal.ofReal (q y))) S := by
  apply pos_iff_ne_zero.mpr
  intro hz
  have h := (withDensity_apply_eq_zero hqm.ennreal_ofReal).mp hz
  have hsub : S ⊆ {x | ENNReal.ofReal (q x) ≠ 0} ∩ S :=
    fun x hx => ⟨(ENNReal.ofReal_pos.mpr (hqp x hx)).ne', hx⟩
  exact hSpos.ne' (measure_mono_null hsub h)

theorem zero_mem_open_convex_target {q : E n → ℝ} {K : Set (E n)}
    (hKo : IsOpen K) (hKc : Convex ℝ K) (hKb : Bornology.IsBounded K)
    (hqm : Measurable q) (hqp : ∀ y ∈ K, 0 < q y) (hqs : ∀ y ∉ K, q y = 0)
    [IsProbabilityMeasure (volume.withDensity (fun y => ENNReal.ofReal (q y)))]
    (hmean : (∫ y : E n, y ∂volume.withDensity (fun y => ENNReal.ofReal (q y))) = 0) :
    (0 : E n) ∈ K := by
  let μ := volume.withDensity (fun y => ENNReal.ofReal (q y))
  have hμK : ∀ᵐ y ∂μ, y ∈ K := density_ae_mem_of_zero_off hKo.measurableSet hqs
  obtain ⟨R, hR⟩ := hKb.exists_norm_le
  have hi : Integrable (fun y : E n => y) μ := by
    apply Integrable.of_bound measurable_id.aestronglyMeasurable R
    exact hμK.mono (fun y hy => hR y hy)
  obtain ⟨x, hx⟩ := hμK.exists
  obtain ⟨d, hd, hball⟩ := Metric.isOpen_iff.mp hKo x hx
  let B := Metric.closedBall x (d / 2)
  have hBK : B ⊆ K := (Metric.closedBall_subset_ball (by linarith : d / 2 < d)).trans hball
  have hBpos : 0 < volume B :=
    (Metric.isOpen_ball.measure_pos volume ⟨x, Metric.mem_ball_self (by positivity : 0 < d / 2)⟩).trans_le
      (measure_mono Metric.ball_subset_closedBall)
  have hμB : 0 < μ B := density_set_pos_of_positive_on hqm hBpos (fun y hy => hqp y (hBK hy))
  have haverage : (⨍ y in B, y ∂μ) ∈ B :=
    (convex_closedBall x (d / 2)).set_average_mem Metric.isClosed_closedBall hμB.ne'
      (measure_ne_top _ _) (ae_restrict_mem Metric.isClosed_closedBall.measurableSet) hi.integrableOn
  have hglobal := hKc.average_mem_interior_of_set hμB.ne' hμK hi
    (show (⨍ y in B, y ∂μ) ∈ interior K by rw [hKo.interior_eq]; exact hBK haverage)
  rw [average_eq_integral, hmean, hKo.interior_eq] at hglobal
  exact hglobal

/-- The regular-target assumptions construct all geometric constants used
by the moment-map existence proof. -/
theorem regular_target_variational_constants {q : E n → ℝ} {K : Set (E n)}
    (hKo : IsOpen K) (hKc : Convex ℝ K) (hKb : Bornology.IsBounded K)
    (hqm : Measurable q) (hqc : ContinuousOn q K) (hqp : ∀ y ∈ K, 0 < q y)
    (hqs : ∀ y ∉ K, q y = 0)
    [IsProbabilityMeasure (volume.withDensity (fun y => ENNReal.ofReal (q y)))]
    (hmean : (∫ y : E n, y ∂volume.withDensity (fun y => ENNReal.ofReal (q y))) = 0) :
    ∃ R r c : ℝ, 0 < r ∧ 0 < c ∧ IsCompact (closure K) ∧
      (∀ y ∈ closure K, ‖y‖ ≤ R) ∧ Metric.closedBall (0 : E n) r ⊆ closure K ∧
      (∀ y ∈ Metric.ball (0 : E n) (3 * r), c ≤ q y) := by
  have h0 := zero_mem_open_convex_target hKo hKc hKb hqm hqp hqs hmean
  obtain ⟨d, hd, hball⟩ := Metric.isOpen_iff.mp hKo 0 h0
  let r := d / 6
  have hr : 0 < r := by dsimp [r]; positivity
  have hbig : Metric.closedBall (0 : E n) (3 * r) ⊆ K :=
    (Metric.closedBall_subset_ball (by dsimp [r]; linarith : 3 * r < d)).trans hball
  have hcomp : IsCompact (closure K) := hKb.isCompact_closure
  obtain ⟨R, hR⟩ := hcomp.exists_bound_of_continuousOn (continuous_id : Continuous (fun y : E n => y)).continuousOn
  obtain ⟨z, hz, hmin⟩ := (isCompact_closedBall (0 : E n) (3 * r)).exists_isMinOn
    ⟨0, Metric.mem_closedBall_self (by positivity)⟩ (hqc.mono hbig)
  refine ⟨R, r, q z, hr, hqp z (hbig hz), hcomp, hR, ?_, ?_⟩
  · exact ((Metric.closedBall_subset_closedBall (by linarith : r ≤ 3 * r)).trans hbig).trans subset_closure
  · intro y hy
    exact hmin (Metric.ball_subset_closedBall hy)

def regularTargetDensity (K : Set (E n)) (V : E n → ℝ) : E n → ℝ :=
  K.indicator (fun x => Real.exp (-V x))

lemma regularTargetDensity_nonneg (K : Set (E n)) (V : E n → ℝ) (x : E n) :
    0 ≤ regularTargetDensity K V x := by
  by_cases hx : x ∈ K <;> simp [regularTargetDensity, hx, Real.exp_nonneg]

lemma regularTargetDensity_positive {K : Set (E n)} (V : E n → ℝ) {x : E n} (hx : x ∈ K) :
    0 < regularTargetDensity K V x := by simp [regularTargetDensity, hx, Real.exp_pos]

lemma regularTargetDensity_zero_off {K : Set (E n)} (V : E n → ℝ) {x : E n} (hx : x ∉ K) :
    regularTargetDensity K V x = 0 := by simp [regularTargetDensity, hx]

lemma regularTargetDensity_measurable {K : Set (E n)} {V : E n → ℝ}
    (hK : MeasurableSet K) (hV : ContinuousOn V K) : Measurable (regularTargetDensity K V) := by
  classical
  have hc : ContinuousOn (fun x => Real.exp (-V x)) K :=
    Real.continuous_exp.comp_continuousOn hV.neg
  change Measurable (K.piecewise (fun x => Real.exp (-V x)) (fun _ => 0))
  exact hc.measurable_piecewise continuousOn_const hK

lemma regularTargetDensity_continuousOn {K : Set (E n)} {V : E n → ℝ}
    (hV : ContinuousOn V K) : ContinuousOn (regularTargetDensity K V) K := by
  apply (Real.continuous_exp.comp_continuousOn hV.neg).congr
  intro x hx
  simp [regularTargetDensity, hx]

/-- For the paper's regular target class, all witness hypotheses and the
witness itself are constructed from bounded convex support, continuous
finite target potential, normalization and centering. Smoothness and target
convexity are stronger than required for this existence stage. -/
theorem exists_regular_target_variational_data {K : Set (E n)} {V : E n → ℝ}
    (hKo : IsOpen K) (hKc : Convex ℝ K) (hKb : Bornology.IsBounded K) (hV : ContinuousOn V K)
    [IsProbabilityMeasure (volume.withDensity (fun y => ENNReal.ofReal (regularTargetDensity K V y)))]
    (hmean : (∫ y : E n, y ∂volume.withDensity (fun y => ENNReal.ofReal (regularTargetDensity K V y))) = 0) :
    ∃ R r c : ℝ, 0 < r ∧ 0 < c ∧
      (∀ y ∈ closure K, ‖y‖ ≤ R) ∧ Metric.closedBall (0 : E n) r ⊆ closure K ∧
      (∀ y ∈ Metric.ball (0 : E n) (3 * r), c ≤ regularTargetDensity K V y) ∧
      Nonempty (VariationalWitness (closure K) (regularTargetDensity K V) R) := by
  let q := regularTargetDensity K V
  have hq0 := regularTargetDensity_nonneg K V
  have hqm := regularTargetDensity_measurable hKo.measurableSet hV
  have hqc := regularTargetDensity_continuousOn hV
  have hqp : ∀ y ∈ K, 0 < q y := fun y hy => regularTargetDensity_positive V hy
  have hqs : ∀ y ∉ K, q y = 0 := fun y hy => regularTargetDensity_zero_off V hy
  obtain ⟨R, r, c, hr, hc, hclosed, hR, hball, hlower⟩ :=
    regular_target_variational_constants hKo hKc hKb hqm hqc hqp hqs hmean
  have hqmass := MomentMapApproximation.integral_density_eq_one hq0 hqm
  have hqi := integrable_of_integral_eq_one hqmass
  have hqoutside : ∀ y ∉ closure K, q y = 0 := fun y hy => hqs y (fun hyK => hy (subset_closure hyK))
  exact ⟨R, r, c, hr, hc, hR, hball, hlower,
    exists_variationalWitness hclosed hR hball hq0 hqm hqi hqmass hqoutside hc hr hlower⟩

end GaussianTilt.MomentMapCoercivity
