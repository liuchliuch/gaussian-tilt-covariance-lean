import GaussianTilt.MomentMapHolderSpace

/-! # Actual compactness of uniformly bounded Hölder functions

The compactness is in the uniform norm. The limiting function retains the
full Hölder bound; no false compactness of a fixed Hölder norm is asserted.
-/
noncomputable section
open Set Filter
open scoped Topology BoundedContinuousFunction
namespace GaussianTilt.HolderSpace
variable (X F : Type*) [MetricSpace X] [NormedAddCommGroup F] [NormedSpace ℝ F]

def boundedHolderSet (α C : ℝ) : Set (X →ᵇ F) :=
  {f | ‖f‖ ≤ C ∧ ∀ x y, ‖f x - f y‖ ≤ C * dist x y ^ α}

lemma isClosed_boundedHolderSet (α C : ℝ) : IsClosed (boundedHolderSet X F α C) := by
  have he : boundedHolderSet X F α C = {f : X →ᵇ F | ‖f‖ ≤ C} ∩
      ⋂ x : X, ⋂ y : X, {f : X →ᵇ F | ‖f x - f y‖ ≤ C * dist x y ^ α} := by
    ext f
    simp only [boundedHolderSet, mem_setOf_eq, mem_inter_iff, mem_iInter]
  rw [he]
  refine (isClosed_le continuous_norm continuous_const).inter (isClosed_iInter fun x => isClosed_iInter fun y => ?_)
  exact isClosed_le (((BoundedContinuousFunction.evalCLM ℝ x).continuous.sub
    (BoundedContinuousFunction.evalCLM ℝ y).continuous).norm) continuous_const

lemma equicontinuous_boundedHolderSet {α : ℝ} (hα : 0 < α) (C : ℝ) :
    Equicontinuous (fun f : boundedHolderSet X F α C => (f.1 : X → F)) := by
  intro x
  apply Metric.equicontinuousAt_of_continuity_modulus (fun y : X => C * dist x y ^ α)
  · have hc : ContinuousAt (fun y : X => C * dist x y ^ α) x :=
      continuousAt_const.mul ((continuous_const.dist continuous_id).continuousAt.rpow_const (Or.inr hα.le))
    simpa only [dist_self, Real.zero_rpow hα.ne', mul_zero] using hc.tendsto
  · exact Filter.Eventually.of_forall fun y f => by
      simpa only [dist_eq_norm] using f.2.2 x y

theorem isCompact_boundedHolderSet [CompactSpace X] [ProperSpace F]
    {α : ℝ} (hα : 0 < α) (C : ℝ) : IsCompact (boundedHolderSet X F α C) := by
  apply BoundedContinuousFunction.arzela_ascoli₂ (Metric.closedBall (0 : F) C)
    (isCompact_closedBall 0 C) _ (isClosed_boundedHolderSet X F α C)
  · intro f x hf
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact (f.norm_coe_le_norm x).trans hf.1
  · exact equicontinuous_boundedHolderSet X F hα C

/-- A norm-bounded sequence in the genuine Hölder space has a uniformly
convergent subsequence whose limit is still a Hölder element with the same bound. -/
theorem exists_uniformly_convergent_subseq [CompactSpace X] [ProperSpace F]
    {α C : ℝ} (hα : 0 < α) (hC : 0 ≤ C) (f : ℕ → Space X F α)
    (hf : ∀ k, ‖f k‖ ≤ C) :
    ∃ g : Space X F α, ‖g‖ ≤ C ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k => value X F α (f (φ k))) atTop (𝓝 (value X F α g)) := by
  have hmem : ∀ k, value X F α (f k) ∈ boundedHolderSet X F α C := by
    intro k
    exact ⟨(norm_value_le X F α (f k)).trans (hf k), fun x y =>
      (norm_value_sub_le X F α (f k) x y).trans
        (mul_le_mul_of_nonneg_right (hf k) (Real.rpow_nonneg dist_nonneg _))⟩
  obtain ⟨g, hg, φ, hφ, ht⟩ := (isCompact_boundedHolderSet X F hα C).tendsto_subseq hmem
  refine ⟨ofBounded X F α g C hg.2, ?_, φ, hφ, ht⟩
  exact (norm_ofBounded_le X F α g hC hg.2).trans (max_le hg.1 le_rfl)

end GaussianTilt.HolderSpace
