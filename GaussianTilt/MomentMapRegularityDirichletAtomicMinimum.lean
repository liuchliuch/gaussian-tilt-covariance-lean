import GaussianTilt.MomentMapRegularityDirichletAtomic

/-! # Coercivity and attainment of the finite atomic Dirichlet energy -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators ENNReal NNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}
variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

lemma exists_ball_volume_gt [NeZero n] (M : ℝ) :
    ∃ L : ℝ, 0 < L ∧ M < (volume (Metric.ball (0 : E n) L)).toReal := by
  let v := (volume (Metric.ball (0 : E n) 1)).toReal
  have vp : 0 < v := ENNReal.toReal_pos
    (Metric.isOpen_ball.measure_pos volume ⟨0, Metric.mem_ball_self (by norm_num)⟩).ne'
    (ne_top_of_le_ne_top (isCompact_closedBall (0 : E n) 1).measure_ne_top
      (measure_mono Metric.ball_subset_closedBall))
  let L := max 1 ((M + 1) / v)
  have hL1 : 1 ≤ L := le_max_left _ _
  have hL : 0 < L := zero_lt_one.trans_le hL1
  refine ⟨L, hL, ?_⟩
  rw [volume.addHaar_ball_of_pos (0 : E n) hL, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hL.le _)]
  have hdim : Module.finrank ℝ (E n) = n := by simp [E, Reference.Space]
  rw [hdim]
  have hl : M + 1 ≤ L * v := (div_le_iff₀ vp).mp (le_max_right _ _)
  have hp := mul_le_mul_of_nonneg_right (le_self_pow₀ hL1 (NeZero.ne n)) vp.le
  change M < L^n * v
  linarith

lemma atomicExcess_ge_height_sub_norm {S : Set (E n)} (hSn : S.Nonempty)
    {X : ι → E n} (hX : ∀ i, X i ∈ S) {R : ℝ} (hR : 0 ≤ R)
    (hbound : ∀ x ∈ S, ‖x‖ ≤ R) (h : ι → ℝ) (p : E n) (i : ι) :
    h i - 2 * R * ‖p‖ ≤ atomicExcess S X h p := by
  have hsup := boundarySupport_le_norm hSn hbound p
  have hi := abs_real_inner_le_norm p (X i)
  have hXi := mul_le_mul_of_nonneg_left (hbound _ (hX i)) (norm_nonneg p)
  have hneg := neg_abs_le (inner ℝ p (X i))
  have hatom := atomicExcess_ge_atom S X h p i
  nlinarith

lemma atomic_integral_lower_bound {S : Set (E n)} (hS : IsCompact S)
    {X : ι → E n} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hb : ∀ i, Metric.closedBall (X i) r ⊆ S) (hbound : ∀ x ∈ S, ‖x‖ ≤ R)
    (h : ι → ℝ) {L : ℝ} (hL : 0 < L) (i : ι) :
    (volume (Metric.ball (0 : E n) L)).toReal * (h i - 2 * R * L) ≤
      ∫ p, atomicExcess S X h p := by
  have hX (i : ι) : X i ∈ S := hb i (Metric.mem_closedBall_self hr.le)
  have hSn : S.Nonempty := ⟨X (Classical.arbitrary ι), hX _⟩
  have hBfin : volume (Metric.ball (0 : E n) L) ≠ ⊤ :=
    ne_top_of_le_ne_top (isCompact_closedBall (0 : E n) L).measure_ne_top
      (measure_mono Metric.ball_subset_closedBall)
  have hi := atomicExcess_integrable hS hr hb h
  have hset : (∫ p in Metric.ball (0 : E n) L, (h i - 2 * R * L)) ≤
      ∫ p in Metric.ball (0 : E n) L, atomicExcess S X h p := by
    have hci : IntegrableOn (fun _ : E n => h i - 2 * R * L) (Metric.ball 0 L) :=
      integrableOn_const hBfin
    apply integral_mono_ae hci hi.integrableOn
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with p hp
    have hpn : ‖p‖ < L := by simpa using hp
    exact (by nlinarith : h i - 2 * R * L ≤ h i - 2 * R * ‖p‖).trans
      (atomicExcess_ge_height_sub_norm hSn hX hR hbound h p i)
  rw [integral_const, smul_eq_mul, measureReal_restrict_apply_univ, measureReal_def] at hset
  exact hset.trans (setIntegral_le_integral hi (ae_of_all _ (atomicExcess_nonneg S X h)))

lemma atomicDirichletEnergy_coercive_bound {S : Set (E n)} (hS : IsCompact S)
    {X : ι → E n} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hb : ∀ i, Metric.closedBall (X i) r ⊆ S) (hbound : ∀ x ∈ S, ‖x‖ ≤ R)
    (mass : ι → ℝ) (hmass : ∀ i, 0 ≤ mass i) (h : ι → ℝ) {L : ℝ} (hL : 0 < L) :
    ((volume (Metric.ball (0 : E n) L)).toReal - ∑ i, mass i) *
      Finset.univ.sup' Finset.univ_nonempty h -
      2 * R * L * (volume (Metric.ball (0 : E n) L)).toReal ≤ atomicDirichletEnergy S X mass h := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty h
  have hint := atomic_integral_lower_bound hS hr hR hb hbound h hL i
  have hmass' : (∑ j, mass j * h j) ≤ (∑ j, mass j) * Finset.univ.sup' Finset.univ_nonempty h := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_left (Finset.le_sup' h (Finset.mem_univ j)) (hmass j)
  rw [← hi] at hint
  dsimp [atomicDirichletEnergy]
  nlinarith

/-- The variational cell heights have an actual minimizer in the positive
orthant. Coercivity is proved by integration on one sufficiently large slope
ball, rather than assumed or encoded in a compactness premise. -/
theorem exists_atomicDirichletEnergy_minimizer [NeZero n] {S : Set (E n)} (hS : IsCompact S)
    {X : ι → E n} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hb : ∀ i, Metric.closedBall (X i) r ⊆ S) (hbound : ∀ x ∈ S, ‖x‖ ≤ R)
    (mass : ι → ℝ) (hmass : ∀ i, 0 ≤ mass i) :
    ∃ h : ι → ℝ, (∀ i, 0 ≤ h i) ∧
      ∀ k : ι → ℝ, (∀ i, 0 ≤ k i) → atomicDirichletEnergy S X mass h ≤ atomicDirichletEnergy S X mass k := by
  obtain ⟨L, hL, hvol⟩ := exists_ball_volume_gt (n := n) (∑ i, mass i)
  let V := (volume (Metric.ball (0 : E n) L)).toReal
  let δ := V - ∑ i, mass i
  have hδ : 0 < δ := sub_pos.mpr hvol
  let F := atomicDirichletEnergy S X mass
  have hFc : Continuous F := atomicDirichletEnergy_continuous hS hr hb mass
  let A := {h : ι → ℝ | (∀ i, 0 ≤ h i) ∧ F h ≤ F 0}
  have hAc : IsClosed A := by
    change IsClosed ({h : ι → ℝ | ∀ i, 0 ≤ h i} ∩ {h | F h ≤ F 0})
    apply IsClosed.inter
    · simp only [setOf_forall]
      exact isClosed_iInter (fun i => isClosed_le continuous_const (continuous_apply i))
    · exact isClosed_le hFc continuous_const
  have hAb : Bornology.IsBounded A := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨max ((F 0 + 2 * R * L * V) / δ) 0, ?_⟩
    intro h hh
    have hc := atomicDirichletEnergy_coercive_bound hS hr hR hb hbound mass hmass h hL
    change δ * Finset.univ.sup' Finset.univ_nonempty h - 2 * R * L * V ≤ F h at hc
    have hmax : Finset.univ.sup' Finset.univ_nonempty h ≤ (F 0 + 2 * R * L * V) / δ := by
      apply (le_div_iff₀ hδ).mpr
      nlinarith [hh.2]
    apply (pi_norm_le_iff_of_nonneg (le_max_right _ _)).mpr
    intro i
    rw [Real.norm_eq_abs, abs_of_nonneg (hh.1 i)]
    exact ((Finset.le_sup' h (Finset.mem_univ i)).trans hmax).trans (le_max_left _ _)
  have hAk : IsCompact A := Metric.isCompact_of_isClosed_isBounded hAc hAb
  obtain ⟨h, hh, hmin⟩ := hAk.exists_isMinOn ⟨0, (fun _ => le_rfl), le_rfl⟩ hFc.continuousOn
  refine ⟨h, hh.1, fun k hk => ?_⟩
  by_cases hkF : F k ≤ F 0
  · exact hmin ⟨hk, hkF⟩
  · exact hh.2.trans (le_of_not_ge hkF)

end GaussianTilt.MomentMapRegularity
