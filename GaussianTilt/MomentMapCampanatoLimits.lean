import GaussianTilt.MomentMapCampanatoJets

/-! # Actual convergence and quantitative tails of quadratic jets -/
noncomputable section
open Set Filter
open scoped Topology Gradient NNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

lemma exists_limit_geometric_increments {F : Type*} [NormedAddCommGroup F] [CompleteSpace F]
    (u : ℕ → F) {C q : ℝ} (hq : q < 1)
    (hu : ∀ k, ‖u k - u (k + 1)‖ ≤ C * q ^ k) :
    ∃ a : F, Tendsto u atTop (𝓝 a) ∧ ∀ k, ‖u k - a‖ ≤ C * q ^ k / (1 - q) := by
  have hc := SeminormedAddCommGroup.cauchySeq_of_le_geometric hq hu
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨a, ha, ?_⟩
  intro k
  simpa only [dist_eq_norm] using dist_le_of_le_geometric_of_tendsto q C hq
    (fun k => by simpa only [dist_eq_norm] using hu k) ha k

lemma quadraticJet_abs_le (a : ℝ) (p h : E n) (H : E n →L[ℝ] E n) :
    |quadraticJet a p 0 H h| ≤ |a| + ‖p‖ * ‖h‖ + (1 / 2 : ℝ) * ‖H‖ * ‖h‖ ^ 2 := by
  have hi : |inner ℝ p h| ≤ ‖p‖ * ‖h‖ := abs_real_inner_le_norm _ _
  have hH : |inner ℝ (H h) h| ≤ ‖H‖ * ‖h‖ ^ 2 := by
    have hi := abs_real_inner_le_norm (H h) h
    have hm := mul_le_mul_of_nonneg_right (H.le_opNorm h) (norm_nonneg h)
    nlinarith
  unfold quadraticJet
  simp only [sub_zero]
  calc
    |a + inner ℝ p h + (1 / 2 : ℝ) * inner ℝ (H h) h| ≤
        |a + inner ℝ p h| + |(1 / 2 : ℝ) * inner ℝ (H h) h| := abs_add_le _ _
    _ ≤ (|a| + |inner ℝ p h|) + |(1 / 2 : ℝ) * inner ℝ (H h) h| :=
      add_le_add_right (abs_add_le _ _) _
    _ ≤ _ := by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; linarith

lemma symmetric_operator_limit (H : ℕ → E n →L[ℝ] E n) (A : E n →L[ℝ] E n)
    (hH : Tendsto H atTop (𝓝 A))
    (hs : ∀ k v w, inner ℝ (H k v) w = inner ℝ v (H k w)) :
    ∀ v w, inner ℝ (A v) w = inner ℝ v (A w) := by
  intro v w
  have h₁ : Tendsto (fun k => inner ℝ (H k v) w) atTop (𝓝 (inner ℝ (A v) w)) :=
    ((ContinuousLinearMap.apply ℝ (E n) v).continuous.tendsto A |>.comp hH).inner tendsto_const_nhds
  have h₂ : Tendsto (fun k => inner ℝ v (H k w)) atTop (𝓝 (inner ℝ v (A w))) :=
    tendsto_const_nhds.inner ((ContinuousLinearMap.apply ℝ (E n) w).continuous.tendsto A |>.comp hH)
  exact tendsto_nhds_unique h₁ (h₂.congr (fun k => (hs k v w).symm))

/-- Geometric coefficient coherence has actual limits and explicit tails.
No limit jet is postulated. -/
theorem exists_quadratic_jet_limit
    (a : ℕ → ℝ) (p : ℕ → E n) (H : ℕ → E n →L[ℝ] E n)
    {ρ q Ca Cp CH : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) (hq : 0 < q) (hq1 : q < 1)
    (ha : ∀ k, |a k - a (k + 1)| ≤ Ca * (ρ ^ 2 * q) ^ k)
    (hp : ∀ k, ‖p k - p (k + 1)‖ ≤ Cp * (ρ * q) ^ k)
    (hH : ∀ k, ‖H k - H (k + 1)‖ ≤ CH * q ^ k)
    (hs : ∀ k v w, inner ℝ (H k v) w = inner ℝ v (H k w)) :
    ∃ a₀ : ℝ, ∃ p₀ : E n, ∃ H₀ : E n →L[ℝ] E n,
      Tendsto a atTop (𝓝 a₀) ∧ Tendsto p atTop (𝓝 p₀) ∧ Tendsto H atTop (𝓝 H₀) ∧
      (∀ v w, inner ℝ (H₀ v) w = inner ℝ v (H₀ w)) ∧
      (∀ k, |a k - a₀| ≤ Ca * (ρ ^ 2 * q) ^ k / (1 - ρ ^ 2 * q)) ∧
      (∀ k, ‖p k - p₀‖ ≤ Cp * (ρ * q) ^ k / (1 - ρ * q)) ∧
      (∀ k, ‖H k - H₀‖ ≤ CH * q ^ k / (1 - q)) := by
  have hρq : ρ * q < 1 := by nlinarith
  have hρ2 : ρ ^ 2 < 1 := by nlinarith
  have hρ2q : ρ ^ 2 * q < 1 := by nlinarith
  obtain ⟨a₀, hat, hab⟩ := exists_limit_geometric_increments a hρ2q
    (fun k => by simpa only [Real.norm_eq_abs] using ha k)
  obtain ⟨p₀, hpt, hpb⟩ := exists_limit_geometric_increments p hρq hp
  obtain ⟨H₀, hHt, hHb⟩ := exists_limit_geometric_increments H hq1 hH
  refine ⟨a₀, p₀, H₀, hat, hpt, hHt, symmetric_operator_limit H H₀ hHt hs, ?_, hpb, hHb⟩
  intro k
  simpa only [Real.norm_eq_abs] using hab k

end GaussianTilt.MomentMapRegularity
