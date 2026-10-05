import GaussianTilt.MomentMapVariational

/-! # Global compactness of normalized bounded-target source candidates

All bounded-target Fenchel candidates have one common Lipschitz constant.
Fixing their value at the origin makes this family compact in the compact-open
topology. The subsequence obtained below converges locally uniformly on the
whole Euclidean space, not merely on one fixed ball.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators
namespace GaussianTilt.MomentMapCoercivity
variable {n : ℕ}

def normalizedLipschitzFamily (R : ℝ≥0) : Set C(E n, ℝ) :=
  {f | LipschitzWith R f ∧ f 0 = 0}

theorem normalizedLipschitzFamily_isCompact (R : ℝ≥0) :
    IsCompact (normalizedLipschitzFamily (n := n) R) := by
  let T : Set (E n → ℝ) := {f | LipschitzWith R f ∧ f 0 = 0}
  have hclosed : IsClosed T :=
    (isClosed_setOf_lipschitzWith R).inter (isClosed_eq (continuous_apply 0) continuous_const)
  have hpoint : T ⊆ {f : E n → ℝ | ∀ x, f x ∈ Icc (-((R : ℝ) * ‖x‖)) ((R : ℝ) * ‖x‖)} := by
    intro f hf x
    have h := hf.1.dist_le_mul x 0
    rw [hf.2, dist_zero_right, Real.norm_eq_abs, dist_zero_right] at h
    exact abs_le.mp h
  have hcompact : IsCompact T :=
    (isCompact_pi_infinite (fun x : E n => isCompact_Icc)).of_isClosed_subset hclosed hpoint
  have himage : ContinuousMap.toFun '' normalizedLipschitzFamily (n := n) R = T := by
    ext f
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact hg
    · intro hf
      exact ⟨⟨f, hf.1.continuous⟩, hf, rfl⟩
  apply ArzelaAscoli.isCompact_of_equicontinuous
  · rw [himage]
    exact hcompact
  · exact (LipschitzWith.uniformEquicontinuous
      (fun f : normalizedLipschitzFamily (n := n) R => (f.val : E n → ℝ)) R
      (fun f => f.property.1)).equicontinuous

theorem exists_locally_uniform_limit_of_lipschitz
    {φ : ℕ → E n → ℝ} {R : ℝ≥0}
    (hφ : ∀ k, LipschitzWith R (φ k)) (h0 : ∀ k, φ k 0 = 0) :
    ∃ ψ : E n → ℝ, ∃ σ : ℕ → ℕ, StrictMono σ ∧ LipschitzWith R ψ ∧ ψ 0 = 0 ∧
      TendstoLocallyUniformly (fun k => φ (σ k)) ψ atTop ∧
      ∀ x, Tendsto (fun k => φ (σ k) x) atTop (𝓝 (ψ x)) := by
  let F : ℕ → C(E n, ℝ) := fun k => ⟨φ k, (hφ k).continuous⟩
  have hF : ∀ k, F k ∈ normalizedLipschitzFamily R := fun k => ⟨hφ k, h0 k⟩
  obtain ⟨ψ, hψ, σ, hσ, hlim⟩ := (normalizedLipschitzFamily_isCompact R).tendsto_subseq hF
  refine ⟨ψ, σ, hσ, hψ.1, hψ.2, ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hlim, ?_⟩
  intro x
  exact (continuous_eval_const x).continuousAt.tendsto.comp hlim

lemma convexOn_limit {φ : ℕ → E n → ℝ} {ψ : E n → ℝ}
    (hφ : ∀ k, ConvexOn ℝ univ (φ k))
    (hlim : ∀ x, Tendsto (fun k => φ k x) atTop (𝓝 (ψ x))) : ConvexOn ℝ univ ψ := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  apply le_of_tendsto_of_tendsto (hlim (a • x + b • y))
    ((tendsto_const_nhds.mul (hlim x)).add (tendsto_const_nhds.mul (hlim y)))
  exact Filter.Eventually.of_forall (fun k => (hφ k).2 (mem_univ x) (mem_univ y) ha hb hab)

lemma fenchel_zero {K : Set (E n)} {u : E n → ℝ} {R : ℝ}
    (hK : ∀ y ∈ K, ‖y‖ ≤ R) (hu : ∀ y ∈ K, 0 ≤ u y)
    (h0 : (0 : E n) ∈ K) (hu0 : u 0 = 0) : fenchel K u 0 = 0 := by
  apply le_antisymm _ (fenchel_nonneg hK hu h0 hu0 0)
  apply csSup_le (fenchelValues_nonempty ⟨0, h0⟩ _ _)
  rintro v ⟨y, hy, rfl⟩
  simpa using neg_nonpos.mpr (hu y hy)

/-- An actual subsequential convex source candidate exists for every
normalized dual sequence on a bounded target. -/
theorem exists_locally_uniform_fenchel_limit {K : Set (E n)} {u : ℕ → E n → ℝ} {R : ℝ}
    (hK : ∀ y ∈ K, ‖y‖ ≤ R) (hu : ∀ k y, y ∈ K → 0 ≤ u k y)
    (h0 : (0 : E n) ∈ K) (hu0 : ∀ k, u k 0 = 0) :
    ∃ ψ : E n → ℝ, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      LipschitzWith R.toNNReal ψ ∧ ψ 0 = 0 ∧ ConvexOn ℝ univ ψ ∧
      TendstoLocallyUniformly (fun k => fenchel K (u (σ k))) ψ atTop ∧
      ∀ x, Tendsto (fun k => fenchel K (u (σ k)) x) atTop (𝓝 (ψ x)) := by
  obtain ⟨ψ, σ, hσ, hψ, hψ0, hloc, hpoint⟩ := exists_locally_uniform_limit_of_lipschitz
    (fun k => fenchel_lipschitz ⟨0, h0⟩ hK (hu k))
    (fun k => fenchel_zero hK (hu k) h0 (hu0 k))
  exact ⟨ψ, σ, hσ, hψ, hψ0,
    convexOn_limit (fun k => fenchel_convex ⟨0, h0⟩ hK (hu (σ k))) hpoint, hloc, hpoint⟩

end GaussianTilt.MomentMapCoercivity
