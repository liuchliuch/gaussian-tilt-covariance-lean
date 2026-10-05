import GaussianTilt.MomentMapDualLimit

/-! # Finite conjugate recovery from a variational source limit

The finite source-ball conjugates are actual admissible dual potentials.
Their target budgets are controlled by the limit budget and their source
partitions cannot exceed the limiting partition. This is the compact
conjugate-recovery step in the direct method.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators InnerProductSpace
namespace GaussianTilt.MomentMapCoercivity
variable {n : ℕ}

def sourceBall (k : ℕ) : Set (E n) := Metric.closedBall 0 ((k : ℝ) + 1)
def recoveredDual (ψ : E n → ℝ) (k : ℕ) : E n → ℝ := fenchel (sourceBall k) ψ

lemma zero_mem_sourceBall (k : ℕ) : (0 : E n) ∈ sourceBall k := Metric.mem_closedBall_self (by positivity)
lemma sourceBall_norm_bound (k : ℕ) : ∀ x ∈ sourceBall (n := n) k, ‖x‖ ≤ (k : ℝ) + 1 :=
  fun x hx => by simpa [sourceBall] using hx

theorem recoveredDual_admissible {q ψ : E n → ℝ} {K : Set (E n)} {R : ℝ}
    (hq0 : ∀ y, 0 ≤ q y) (hqi : Integrable q) (hK : ∀ y ∈ K, ‖y‖ ≤ R)
    (hqs : ∀ y ∉ K, q y = 0) (hψ0 : ψ 0 = 0) (hψ : ∀ x, 0 ≤ ψ x) (k : ℕ) :
    DualAdmissible q (recoveredDual ψ k) := by
  have h0 := zero_mem_sourceBall (n := n) k
  have hb := sourceBall_norm_bound (n := n) k
  exact ⟨(fenchel_lipschitz ⟨0, h0⟩ hb (fun x _ => hψ x)).continuous,
    fenchel_convex ⟨0, h0⟩ hb (fun x _ => hψ x),
    fenchel_nonneg hb (fun x _ => hψ x) h0 hψ0,
    fenchel_zero hb (fun x _ => hψ x) h0 hψ0,
    weighted_fenchel_ball_integrable hq0 hqi hK hqs hψ0 hψ (by positivity)⟩

theorem recoveredDual_monotone {ψ : E n → ℝ} (hψ : ∀ x, 0 ≤ ψ x) (y : E n) :
    Monotone (fun k => recoveredDual ψ k y) := by
  intro i j hij
  apply csSup_le (fenchelValues_nonempty ⟨0, zero_mem_sourceBall i⟩ _ _)
  rintro a ⟨x, hx, rfl⟩
  apply fenchel_young (sourceBall_norm_bound j) (fun x _ => hψ x) y
  apply Metric.closedBall_subset_closedBall _ hx
  exact_mod_cast Nat.add_le_add_right hij 1

theorem fenchel_recoveredDual_le_source {K : Set (E n)} (hKn : K.Nonempty)
    {ψ : E n → ℝ} (hψ : ∀ x, 0 ≤ ψ x) (k : ℕ) {x : E n} (hx : x ∈ sourceBall k) :
    fenchel K (recoveredDual ψ k) x ≤ ψ x := by
  apply csSup_le (fenchelValues_nonempty hKn _ _)
  rintro a ⟨y, hy, rfl⟩
  have h := fenchel_young (sourceBall_norm_bound k) (fun x _ => hψ x) y hx
  change ⟪y, x⟫_ℝ - ψ x ≤ recoveredDual ψ k y at h
  change ⟪x, y⟫_ℝ - recoveredDual ψ k y ≤ ψ x
  rw [real_inner_comm]
  linarith

theorem recoveredDual_partition_le_limit
    {K : Set (E n)} {q : E n → ℝ} {u : ℕ → E n → ℝ} {ψ : E n → ℝ} {R r c Z : ℝ}
    (hK : ∀ y ∈ K, ‖y‖ ≤ R) (hball : Metric.closedBall (0 : E n) r ⊆ K)
    (hq0 : ∀ y, 0 ≤ q y) (hqi : Integrable q) (hqmass : (∫ y, q y) = 1)
    (hqs : ∀ y ∉ K, q y = 0) (hc : 0 < c) (hr : 0 < r)
    (hqlower : ∀ y ∈ Metric.ball (0 : E n) (3 * r), c ≤ q y)
    (hu : ∀ k, DualAdmissible q (u k)) (hψ0 : ψ 0 = 0) (hψ : ∀ x, 0 ≤ ψ x)
    (hlocal : TendstoLocallyUniformly (fun k => fenchel K (u k)) ψ atTop)
    (hZ : Tendsto (fun k => dualPartition K (u k)) atTop (𝓝 Z)) (hZ0 : 0 < Z)
    (hobj : Tendsto (fun k => dualObjective K q (u k)) atTop (𝓝 (sSup (dualValues K q))))
    (k : ℕ) : dualPartition K (recoveredDual ψ k) ≤ Z := by
  have hv := recoveredDual_admissible hq0 hqi hK hqs hψ0 hψ k
  have hb := truncated_dualBudget_le_limit hK hu hq0 hqi hqmass hqs hψ0 hψ hlocal
    (dualBudget_tendsto_of_partitions_and_objectives hZ hZ0 hobj) (by positivity : 0 ≤ (k : ℝ) + 1)
  have hbound := le_csSup (dualValues_bddAbove hK hball hq0 hc hr hqlower)
    (show dualObjective K q (recoveredDual ψ k) ∈ dualValues K q from ⟨_, hv, rfl⟩)
  have hp := (dualPartition_polynomial_bound hK hball hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.1
    hq0 hv.2.2.2.2 hc hr hqlower).1
  apply (Real.log_le_log_iff hp hZ0).mp
  change dualBudget q (recoveredDual ψ k) ≤ Real.log Z - sSup (dualValues K q) at hb
  dsimp [dualObjective] at hbound
  linarith

lemma sourceBall_monotone : Monotone (sourceBall (n := n)) := by
  intro i j hij
  apply Metric.closedBall_subset_closedBall
  exact_mod_cast Nat.add_le_add_right hij 1

lemma iUnion_sourceBall : (⋃ k : ℕ, sourceBall (n := n) k) = univ := by
  apply eq_univ_iff_forall.mpr
  intro x
  obtain ⟨k, hk⟩ := exists_nat_gt ‖x‖
  apply mem_iUnion.mpr
  refine ⟨k, ?_⟩
  simp only [sourceBall, Metric.mem_closedBall, dist_zero_right]
  linarith

theorem recoveredDual_partition_tendsto
    {K : Set (E n)} {q : E n → ℝ} {u : ℕ → E n → ℝ} {ψ : E n → ℝ} {R r c : ℝ}
    (hK : ∀ y ∈ K, ‖y‖ ≤ R) (hball : Metric.closedBall (0 : E n) r ⊆ K)
    (hq0 : ∀ y, 0 ≤ q y) (hqi : Integrable q) (hqmass : (∫ y, q y) = 1)
    (hqs : ∀ y ∉ K, q y = 0) (hc : 0 < c) (hr : 0 < r)
    (hqlower : ∀ y ∈ Metric.ball (0 : E n) (3 * r), c ≤ q y)
    (hu : ∀ k, DualAdmissible q (u k)) (hψ0 : ψ 0 = 0) (hψ : ∀ x, 0 ≤ ψ x)
    (hψi : Integrable (fun x => Real.exp (-ψ x)))
    (hlocal : TendstoLocallyUniformly (fun k => fenchel K (u k)) ψ atTop)
    (hZ : Tendsto (fun k => dualPartition K (u k)) atTop (𝓝 (∫ x, Real.exp (-ψ x))))
    (hobj : Tendsto (fun k => dualObjective K q (u k)) atTop (𝓝 (sSup (dualValues K q)))) :
    Tendsto (fun k => dualPartition K (recoveredDual ψ k)) atTop (𝓝 (∫ x, Real.exp (-ψ x))) := by
  have hKn : K.Nonempty := ⟨0, hball (Metric.mem_closedBall_self hr.le)⟩
  have hZ0 := integral_exp_pos hψi
  have hup := recoveredDual_partition_le_limit hK hball hq0 hqi hqmass hqs hc hr hqlower hu hψ0 hψ
    hlocal hZ hZ0 hobj
  have hlo (k : ℕ) : (∫ x in sourceBall k, Real.exp (-ψ x)) ≤ dualPartition K (recoveredDual ψ k) := by
    have hv := recoveredDual_admissible hq0 hqi hK hqs hψ0 hψ k
    have hp := (dualPartition_polynomial_bound hK hball hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.1
      hq0 hv.2.2.2.2 hc hr hqlower).1
    have hiφ : Integrable (fun x => Real.exp (-fenchel K (recoveredDual ψ k) x)) := by
      by_contra hn
      rw [dualPartition, integral_undef hn] at hp
      exact lt_irrefl _ hp
    have hSmeas : MeasurableSet (sourceBall (n := n) k) := Metric.isClosed_closedBall.measurableSet
    rw [← integral_indicator hSmeas]
    apply integral_mono (hψi.indicator hSmeas) hiφ
    intro x
    by_cases hx : x ∈ sourceBall k
    · rw [indicator_of_mem hx]
      exact Real.exp_le_exp.mpr (neg_le_neg (fenchel_recoveredDual_le_source hKn hψ k hx))
    · rw [indicator_of_notMem hx]
      exact (Real.exp_pos _).le
  have hlowlim := tendsto_setIntegral_of_monotone
    (fun k => (show MeasurableSet (sourceBall (n := n) k) from Metric.isClosed_closedBall.measurableSet))
    sourceBall_monotone hψi.integrableOn
  simp only [iUnion_sourceBall, Measure.restrict_univ] at hlowlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlowlim tendsto_const_nhds hlo hup

theorem recoveredDual_budget_tendsto
    {K : Set (E n)} {q : E n → ℝ} {u : ℕ → E n → ℝ} {ψ : E n → ℝ} {R r c : ℝ}
    (hK : ∀ y ∈ K, ‖y‖ ≤ R) (hball : Metric.closedBall (0 : E n) r ⊆ K)
    (hq0 : ∀ y, 0 ≤ q y) (hqi : Integrable q) (hqmass : (∫ y, q y) = 1)
    (hqs : ∀ y ∉ K, q y = 0) (hc : 0 < c) (hr : 0 < r)
    (hqlower : ∀ y ∈ Metric.ball (0 : E n) (3 * r), c ≤ q y)
    (hu : ∀ k, DualAdmissible q (u k)) (hψ0 : ψ 0 = 0) (hψ : ∀ x, 0 ≤ ψ x)
    (hψi : Integrable (fun x => Real.exp (-ψ x)))
    (hlocal : TendstoLocallyUniformly (fun k => fenchel K (u k)) ψ atTop)
    (hZ : Tendsto (fun k => dualPartition K (u k)) atTop (𝓝 (∫ x, Real.exp (-ψ x))))
    (hobj : Tendsto (fun k => dualObjective K q (u k)) atTop (𝓝 (sSup (dualValues K q)))) :
    Tendsto (fun k => dualBudget q (recoveredDual ψ k)) atTop
      (𝓝 (Real.log (∫ x, Real.exp (-ψ x)) - sSup (dualValues K q))) := by
  have hZ0 := integral_exp_pos hψi
  have hZ' := recoveredDual_partition_tendsto hK hball hq0 hqi hqmass hqs hc hr hqlower
    hu hψ0 hψ hψi hlocal hZ hobj
  have hbud := dualBudget_tendsto_of_partitions_and_objectives hZ hZ0 hobj
  have hup (k : ℕ) := truncated_dualBudget_le_limit hK hu hq0 hqi hqmass hqs hψ0 hψ hlocal hbud
    (by positivity : 0 ≤ (k : ℝ) + 1)
  have hlo (k : ℕ) : Real.log (dualPartition K (recoveredDual ψ k)) - sSup (dualValues K q) ≤
      dualBudget q (recoveredDual ψ k) := by
    have hv := recoveredDual_admissible hq0 hqi hK hqs hψ0 hψ k
    have h := le_csSup (dualValues_bddAbove hK hball hq0 hc hr hqlower)
      (show dualObjective K q (recoveredDual ψ k) ∈ dualValues K q from ⟨_, hv, rfl⟩)
    dsimp [dualObjective] at h
    linarith
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    ((hZ'.log hZ0.ne').sub_const _) tendsto_const_nhds hlo hup

end GaussianTilt.MomentMapCoercivity
