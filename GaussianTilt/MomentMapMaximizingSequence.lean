import GaussianTilt.MomentMapSourceCompactness

/-! # Actual maximizing sequences for the moment-measure functional

Coercivity proves boundedness of the objective and of the dual budgets. The
sequence and its locally uniformly converging Fenchel-source subsequence are
constructed from supremum approximation and compactness.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators
namespace GaussianTilt.MomentMapCoercivity
variable {n : ℕ}

def DualAdmissible (q u : E n → ℝ) : Prop :=
  Continuous u ∧ ConvexOn ℝ univ u ∧ (∀ y, 0 ≤ u y) ∧ u 0 = 0 ∧
    Integrable (fun y => q y * u y)

def dualValues (K : Set (E n)) (q : E n → ℝ) : Set ℝ :=
  dualObjective K q '' {u | DualAdmissible q u}

lemma dualAdmissible_zero (q : E n → ℝ) : DualAdmissible q (fun _ => 0) := by
  refine ⟨continuous_const, ⟨convex_univ, ?_⟩, fun _ => le_rfl, rfl, ?_⟩
  · intros
    simp
  · simp

lemma dualValues_nonempty (K : Set (E n)) (q : E n → ℝ) : (dualValues K q).Nonempty :=
  ⟨dualObjective K q (fun _ => 0), ⟨_, dualAdmissible_zero q, rfl⟩⟩

theorem dualValues_bddAbove {K : Set (E n)} {q : E n → ℝ} {R r c : ℝ}
    (hK : ∀ y ∈ K, ‖y‖ ≤ R) (hball : Metric.closedBall (0 : E n) r ⊆ K)
    (hq0 : ∀ y, 0 ≤ q y) (hc : 0 < c) (hr : 0 < r)
    (hqlower : ∀ y ∈ Metric.ball (0 : E n) (3 * r), c ≤ q y) : BddAbove (dualValues K q) := by
  obtain ⟨A, hA⟩ := dualObjective_coercive hK hball hq0 hc hr hqlower
  refine ⟨A, ?_⟩
  rintro b ⟨u, hu, rfl⟩
  have h := hA u hu.1 hu.2.1 hu.2.2.1 hu.2.2.2.1 hu.2.2.2.2
  have hs : 0 ≤ dualBudget q u := integral_nonneg (fun y => mul_nonneg (hq0 y) (hu.2.2.1 y))
  linarith

theorem exists_maximizing_dual_sequence {K : Set (E n)} {q : E n → ℝ} {R r c : ℝ}
    (hK : ∀ y ∈ K, ‖y‖ ≤ R) (hball : Metric.closedBall (0 : E n) r ⊆ K)
    (hq0 : ∀ y, 0 ≤ q y) (hc : 0 < c) (hr : 0 < r)
    (hqlower : ∀ y ∈ Metric.ball (0 : E n) (3 * r), c ≤ q y) :
    ∃ u : ℕ → E n → ℝ, ∃ M : ℝ, 0 ≤ M ∧
      (∀ k, DualAdmissible q (u k)) ∧ (∀ k, dualBudget q (u k) ≤ M) ∧
      Tendsto (fun k => dualObjective K q (u k)) atTop (𝓝 (sSup (dualValues K q))) := by
  have hne := dualValues_nonempty K q
  have hbd := dualValues_bddAbove hK hball hq0 hc hr hqlower
  let s := sSup (dualValues K q)
  have hchoose (k : ℕ) : ∃ u : E n → ℝ, DualAdmissible q u ∧
      s - ((k : ℝ) + 1)⁻¹ < dualObjective K q u := by
    obtain ⟨a, ⟨u, hu, rfl⟩, ha⟩ := exists_lt_of_lt_csSup hne
      (sub_lt_self s (by positivity : 0 < ((k : ℝ) + 1)⁻¹))
    exact ⟨u, hu, ha⟩
  choose u hu hlo using hchoose
  have hupper (k : ℕ) : dualObjective K q (u k) ≤ s := le_csSup hbd ⟨u k, hu k, rfl⟩
  have hseq : Tendsto (fun k => dualObjective K q (u k)) atTop (𝓝 s) := by
    have hinv : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
    have hlowlim : Tendsto (fun k : ℕ => s - ((k : ℝ) + 1)⁻¹) atTop (𝓝 s) := by
      simpa using tendsto_const_nhds.sub hinv
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlowlim tendsto_const_nhds
      (fun k => (hlo k).le) hupper
  obtain ⟨A, hA⟩ := dualObjective_coercive hK hball hq0 hc hr hqlower
  let M := 2 * (A - s + 1)
  have hbudget (k : ℕ) : dualBudget q (u k) ≤ M := by
    have h := hA (u k) (hu k).1 (hu k).2.1 (hu k).2.2.1 (hu k).2.2.2.1 (hu k).2.2.2.2
    have hi : ((k : ℝ) + 1)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).mpr (by
      linarith [Nat.cast_nonneg (α := ℝ) k])
    have hl := hlo k
    dsimp [M]
    linarith
  have hM : 0 ≤ M := (integral_nonneg (fun y => mul_nonneg (hq0 y) ((hu 0).2.2.1 y))).trans (hbudget 0)
  exact ⟨u, M, hM, hu, hbudget, hseq⟩

/-- The bounded-budget maximizing sequence has an actual globally defined,
convex, normalized, locally uniform source limit. -/
theorem exists_maximizing_sequence_with_source_limit
    {K : Set (E n)} {q : E n → ℝ} {R r c : ℝ}
    (hK : ∀ y ∈ K, ‖y‖ ≤ R) (hball : Metric.closedBall (0 : E n) r ⊆ K)
    (hq0 : ∀ y, 0 ≤ q y) (hc : 0 < c) (hr : 0 < r)
    (hqlower : ∀ y ∈ Metric.ball (0 : E n) (3 * r), c ≤ q y) :
    ∃ u : ℕ → E n → ℝ, ∃ ψ : E n → ℝ, ∃ M : ℝ, 0 ≤ M ∧
      (∀ k, DualAdmissible q (u k)) ∧ (∀ k, dualBudget q (u k) ≤ M) ∧
      Tendsto (fun k => dualObjective K q (u k)) atTop (𝓝 (sSup (dualValues K q))) ∧
      LipschitzWith R.toNNReal ψ ∧ ψ 0 = 0 ∧ ConvexOn ℝ univ ψ ∧
      TendstoLocallyUniformly (fun k => fenchel K (u k)) ψ atTop ∧
      ∀ x, Tendsto (fun k => fenchel K (u k) x) atTop (𝓝 (ψ x)) := by
  obtain ⟨u, M, hM, hu, hbudget, hobj⟩ := exists_maximizing_dual_sequence hK hball hq0 hc hr hqlower
  obtain ⟨ψ, σ, hσ, hψ, hψ0, hψc, hloc, hpoint⟩ := exists_locally_uniform_fenchel_limit hK
    (fun k y _ => (hu k).2.2.1 y) (hball (Metric.mem_closedBall_self hr.le))
    (fun k => (hu k).2.2.2.1)
  exact ⟨fun k => u (σ k), ψ, M, hM, fun k => hu (σ k), fun k => hbudget (σ k),
    hobj.comp hσ.tendsto_atTop, hψ, hψ0, hψc, hloc, hpoint⟩

end GaussianTilt.MomentMapCoercivity
