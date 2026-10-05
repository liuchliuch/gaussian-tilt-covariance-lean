import GaussianTilt.MomentMapSourceLimit

/-! # Recovering the dual budget from a source limit

Every compactly truncated conjugate of the source limit has target budget at
most the limit of the maximizing sequence's budgets. Uniform convergence on
the source ball supplies a global Young-inequality comparison on the target;
the integral inequality is then proved directly.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators InnerProductSpace
namespace GaussianTilt.MomentMapCoercivity
variable {n : ℕ}

theorem dualBudget_tendsto_of_partitions_and_objectives
    {K : Set (E n)} {q : E n → ℝ} {u : ℕ → E n → ℝ} {Z s : ℝ}
    (hZ : Tendsto (fun k => dualPartition K (u k)) atTop (𝓝 Z)) (hZ0 : 0 < Z)
    (hobj : Tendsto (fun k => dualObjective K q (u k)) atTop (𝓝 s)) :
    Tendsto (fun k => dualBudget q (u k)) atTop (𝓝 (Real.log Z - s)) := by
  have h := (hZ.log hZ0.ne').sub hobj
  simpa only [dualObjective, sub_sub_cancel] using h

lemma fenchel_le_of_uniform_source_error
    {K L : Set (E n)} {u ψ : E n → ℝ} {R ε : ℝ}
    (hK : ∀ y ∈ K, ‖y‖ ≤ R) (hu : ∀ y ∈ K, 0 ≤ u y) (hL : L.Nonempty)
    (herr : ∀ x ∈ L, |ψ x - fenchel K u x| ≤ ε)
    {y : E n} (hy : y ∈ K) : fenchel L ψ y ≤ u y + ε := by
  apply csSup_le (fenchelValues_nonempty hL _ _)
  rintro a ⟨x, hx, rfl⟩
  have h := fenchel_young hK hu x hy
  have he := (abs_le.mp (herr x hx)).1
  change ⟪y, x⟫_ℝ - ψ x ≤ u y + ε
  rw [real_inner_comm]
  linarith

lemma fenchel_upper_bound {K : Set (E n)} {u : E n → ℝ} {R : ℝ}
    (hKn : K.Nonempty) (hK : ∀ y ∈ K, ‖y‖ ≤ R) (hu : ∀ y ∈ K, 0 ≤ u y)
    (x : E n) : fenchel K u x ≤ ‖x‖ * R := by
  apply csSup_le (fenchelValues_nonempty hKn _ _)
  rintro a ⟨y, hy, rfl⟩
  have hi := real_inner_le_norm x y
  have hn := mul_le_mul_of_nonneg_left (hK y hy) (norm_nonneg x)
  linarith [hu y hy]

theorem weighted_fenchel_ball_integrable {q ψ : E n → ℝ} {K : Set (E n)} {R b : ℝ}
    (hq0 : ∀ y, 0 ≤ q y) (hqi : Integrable q) (hK : ∀ y ∈ K, ‖y‖ ≤ R)
    (hqs : ∀ y ∉ K, q y = 0) (hψ0 : ψ 0 = 0) (hψ : ∀ x, 0 ≤ ψ x) (hb : 0 ≤ b) :
    Integrable (fun y => q y * fenchel (Metric.closedBall (0 : E n) b) ψ y) := by
  let L := Metric.closedBall (0 : E n) b
  have h0 : (0 : E n) ∈ L := Metric.mem_closedBall_self hb
  have hLb : ∀ x ∈ L, ‖x‖ ≤ b := fun x hx => by simpa [L] using hx
  have hcont := (fenchel_lipschitz ⟨0, h0⟩ hLb (fun x _ => hψ x)).continuous
  apply (hqi.const_mul (R * b)).mono' (hqi.aestronglyMeasurable.mul hcont.aestronglyMeasurable)
  apply ae_of_all
  intro y
  simp only [Pi.mul_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hq0 y) (fenchel_nonneg hLb (fun x _ => hψ x) h0 hψ0 y))]
  by_cases hy : y ∈ K
  · have hu := (fenchel_upper_bound ⟨0, h0⟩ hLb (fun x _ => hψ x) y).trans
      (mul_le_mul_of_nonneg_right (hK y hy) hb)
    have h := mul_le_mul_of_nonneg_left hu (hq0 y)
    simpa only [mul_comm, mul_left_comm, mul_assoc] using h
  · simp [hqs y hy]

theorem truncated_dualBudget_le_limit
    {K : Set (E n)} {q : E n → ℝ} {u : ℕ → E n → ℝ} {ψ : E n → ℝ} {R b I : ℝ}
    (hK : ∀ y ∈ K, ‖y‖ ≤ R) (hu : ∀ k, DualAdmissible q (u k))
    (hq0 : ∀ y, 0 ≤ q y) (hqi : Integrable q) (hqmass : (∫ y, q y) = 1)
    (hqs : ∀ y ∉ K, q y = 0) (hψ0 : ψ 0 = 0) (hψ : ∀ x, 0 ≤ ψ x)
    (hlocal : TendstoLocallyUniformly (fun k => fenchel K (u k)) ψ atTop)
    (hbud : Tendsto (fun k => dualBudget q (u k)) atTop (𝓝 I)) (hb : 0 ≤ b) :
    dualBudget q (fenchel (Metric.closedBall (0 : E n) b) ψ) ≤ I := by
  let L := Metric.closedBall (0 : E n) b
  have h0 : (0 : E n) ∈ L := Metric.mem_closedBall_self hb
  have hd := weighted_fenchel_ball_integrable hq0 hqi hK hqs hψ0 hψ hb
  have hunif : TendstoUniformlyOn (fun k => fenchel K (u k)) ψ atTop L :=
    (tendstoLocallyUniformly_iff_forall_isCompact.mp hlocal) L (isCompact_closedBall _ _)
  apply le_of_forall_pos_le_add
  intro ε hε
  have hevent := Metric.tendstoUniformlyOn_iff.mp hunif ε hε
  have hineq : ∀ᶠ k in atTop,
      dualBudget q (fenchel L ψ) ≤ dualBudget q (u k) + ε := by
    filter_upwards [hevent] with k hk
    have hpoint (y : E n) : q y * fenchel L ψ y ≤ q y * u k y + ε * q y := by
      by_cases hy : y ∈ K
      · have h := fenchel_le_of_uniform_source_error hK (fun y _ => (hu k).2.2.1 y)
          ⟨0, h0⟩ (fun x hx => by simpa only [Real.dist_eq] using (hk x hx).le) hy
        have hm := mul_le_mul_of_nonneg_left h (hq0 y)
        nlinarith
      · simp [hqs y hy]
    have h := integral_mono hd ((hu k).2.2.2.2.add (hqi.const_mul ε)) hpoint
    simp only [Pi.add_apply] at h
    rw [integral_add (hu k).2.2.2.2 (hqi.const_mul ε), integral_const_mul, hqmass, mul_one] at h
    exact h
  exact ge_of_tendsto (hbud.add_const ε) hineq

end GaussianTilt.MomentMapCoercivity
