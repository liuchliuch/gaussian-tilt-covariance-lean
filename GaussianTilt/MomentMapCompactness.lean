import GaussianTilt.MomentMapCoercivity

/-! # Constructed local compactness of dual-potential sequences

The target-weighted integral bound supplies both boundedness and a common
Lipschitz constant. Arzelà--Ascoli then produces an actual subsequence and a
continuous uniform limit on every fixed inner compact ball.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
namespace GaussianTilt.MomentMapCoercivity
variable {n : ℕ}

theorem exists_uniform_limit_on_inner_ball {u : ℕ → E n → ℝ} {q : E n → ℝ}
    (hu : ∀ k, Continuous (u k)) (hc : ∀ k, ConvexOn ℝ univ (u k))
    (hu0 : ∀ k y, 0 ≤ u k y) (hq0 : ∀ y, 0 ≤ q y)
    (hi : ∀ k, Integrable (fun y => q y * u k y))
    {r c M : ℝ} (hc0 : 0 < c) (hr : 0 < r)
    (hqlower : ∀ y ∈ Metric.ball (0 : E n) (3 * r), c ≤ q y)
    (hM : ∀ k, (∫ y, q y * u k y) ≤ M) :
    ∃ g : C(Metric.closedBall (0 : E n) (r / 2), ℝ), ∃ σ : ℕ → ℕ,
      StrictMono σ ∧ TendstoUniformly
        (fun k x => u (σ k) x.val) g atTop := by
  let S := Metric.closedBall (0 : E n) (r / 2)
  letI : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : E n) (r / 2))
  let B := M / (c * (volume (Metric.ball (0 : E n) r)).toReal)
  let L := (2 * B / r).toNNReal
  let F : ℕ → BoundedContinuousFunction S ℝ := fun k =>
    BoundedContinuousFunction.mkOfCompact ⟨fun x => u k x.val, (hu k).comp continuous_subtype_val⟩
  have hsub : S ⊆ Metric.ball (0 : E n) r := Metric.closedBall_subset_ball (by linarith)
  have hsub' : S ⊆ Metric.ball (0 : E n) (2 * r) := Metric.closedBall_subset_ball (by linarith)
  have hLip (k : ℕ) : LipschitzWith L (F k) := by
    have h := convex_inner_ball_lipschitz (hu k) (hc k) (hu0 k) hq0 (hi k) hc0 hr hqlower (hM k)
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact h.dist_le_mul x.val (hsub x.property) y.val (hsub y.property)
  have hBound (k : ℕ) (x : S) : F k x ∈ Icc (0 : ℝ) B := by
    refine ⟨hu0 k x.val, ?_⟩
    exact (le_abs_self _).trans
      (convex_inner_ball_bound (hu k) (hc k) (hu0 k) hq0 (hi k) hc0 hr hqlower (hM k)
        x.val (hsub' x.property))
  have hRange : ∀ (f : BoundedContinuousFunction S ℝ) (x : S), f ∈ range F → f x ∈ Icc (0 : ℝ) B := by
    rintro f x ⟨k, rfl⟩
    exact hBound k x
  have hEqui : Equicontinuous (fun f : range F => (f.val : S → ℝ)) := by
    apply (LipschitzWith.uniformEquicontinuous _ L ?_).equicontinuous
    intro f
    obtain ⟨k, hk⟩ := f.property
    rw [← hk]
    exact hLip k
  have hCompact := BoundedContinuousFunction.arzela_ascoli (Icc (0 : ℝ) B)
    isCompact_Icc (range F) hRange hEqui
  obtain ⟨g, hg, σ, hσ, hlim⟩ := hCompact.tendsto_subseq
    (fun k => subset_closure (mem_range_self k))
  refine ⟨g.toContinuousMap, σ, hσ, ?_⟩
  exact BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hlim

end GaussianTilt.MomentMapCoercivity
