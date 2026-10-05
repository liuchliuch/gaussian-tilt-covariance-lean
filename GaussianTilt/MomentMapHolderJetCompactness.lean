import GaussianTilt.MomentMapHolderCompactness
import GaussianTilt.MomentMapHolderJetEmbedding
import GaussianTilt.MomentMapHolderUniformSegments

/-! # Compactness of genuine C² Hölder jets and preservation of their FTC laws -/
noncomputable section
open Set Filter
open scoped Topology BoundedContinuousFunction
namespace GaussianTilt.HolderSpace
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def ofFields {S : Set E} (hS : Convex ℝ S) (α : ℝ)
    (u : Space S F α) (D : Space S (E →L[ℝ] F) α) (H : Space S (E →L[ℝ] E →L[ℝ] F) α)
    (h₀ : ∀ x y, value S F α u y - value S F α u x = segmentIntegral hS α x y D)
    (h₁ : ∀ x y, value S (E →L[ℝ] F) α D y - value S (E →L[ℝ] F) α D x = segmentIntegral hS α x y H) :
    Jet E F hS α :=
  ⟨(u, D, H), by
    simp only [jetGraph, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]
    constructor
    · intro p
      change value S F α u p.2 - value S F α u p.1 - segmentIntegral hS α p.1 p.2 D = 0
      rw [h₀, sub_self]
    · intro p
      change value S (E →L[ℝ] F) α D p.2 - value S (E →L[ℝ] F) α D p.1 - segmentIntegral hS α p.1 p.2 H = 0
      rw [h₁, sub_self]⟩

lemma ftc_of_uniform_limits {S : Set E} (hS : Convex ℝ S) (α : ℝ)
    (u : ℕ → Space S F α) (D : ℕ → Space S (E →L[ℝ] F) α)
    (v : Space S F α) (G : Space S (E →L[ℝ] F) α)
    (hu : Tendsto (fun k => value S F α (u k)) atTop (𝓝 (value S F α v)))
    (hD : Tendsto (fun k => value S (E →L[ℝ] F) α (D k)) atTop (𝓝 (value S (E →L[ℝ] F) α G)))
    (hftc : ∀ k x y, value S F α (u k) y - value S F α (u k) x = segmentIntegral hS α x y (D k)) :
    ∀ x y, value S F α v y - value S F α v x = segmentIntegral hS α x y G := by
  intro x y
  have hleft := (((BoundedContinuousFunction.evalCLM ℝ y).continuous.tendsto _).comp hu).sub
    (((BoundedContinuousFunction.evalCLM ℝ x).continuous.tendsto _).comp hu)
  have hright := ((segmentValueIntegral hS x y).continuous.tendsto _).comp hD
  have he : (fun k => value S F α (u k) y - value S F α (u k) x) =
      (fun k => segmentValueIntegral hS x y (value S (E →L[ℝ] F) α (D k))) := by
    funext k
    exact hftc k x y
  change Tendsto (fun k => value S F α (u k) y - value S F α (u k) x) atTop
    (𝓝 (value S F α v y - value S F α v x)) at hleft
  rw [he] at hleft
  exact tendsto_nhds_unique hleft hright

/-- Uniform C² compactness, including the actual derivative compatibility,
follows from the constructed Hölder bounds rather than an assumed compact embedding. -/
theorem exists_jet_uniform_subseq [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {S : Set E} (hS : Convex ℝ S) (hSc : IsCompact S)
    {α C : ℝ} (hα : 0 < α) (hC : 0 ≤ C) (j : ℕ → Jet E F hS α)
    (hj : ∀ k, ‖j k‖ ≤ C) :
    ∃ g : Jet E F hS α, ‖g‖ ≤ C ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k => value S F α (jetValue E F hS α (j (φ k)))) atTop
        (𝓝 (value S F α (jetValue E F hS α g))) ∧
      Tendsto (fun k => value S (E →L[ℝ] F) α (jetFirst E F hS α (j (φ k)))) atTop
        (𝓝 (value S (E →L[ℝ] F) α (jetFirst E F hS α g))) ∧
      Tendsto (fun k => value S (E →L[ℝ] E →L[ℝ] F) α (jetSecond E F hS α (j (φ k)))) atTop
        (𝓝 (value S (E →L[ℝ] E →L[ℝ] F) α (jetSecond E F hS α g))) := by
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hSc
  obtain ⟨u, hu, φ₀, hφ₀, ht₀⟩ := exists_uniformly_convergent_subseq S F hα hC
    (fun k => jetValue E F hS α (j k)) (fun k => (norm_jetValue_le hS α (j k)).trans (hj k))
  obtain ⟨D, hD, φ₁, hφ₁, ht₁⟩ := exists_uniformly_convergent_subseq S (E →L[ℝ] F) hα hC
    (fun k => jetFirst E F hS α (j (φ₀ k)))
    (fun k => (norm_jetFirst_le hS α _).trans (hj _))
  obtain ⟨H, hH, φ₂, hφ₂, ht₂⟩ := exists_uniformly_convergent_subseq S (E →L[ℝ] E →L[ℝ] F) hα hC
    (fun k => jetSecond E F hS α (j (φ₀ (φ₁ k))))
    (fun k => (norm_jetSecond_le hS α _).trans (hj _))
  let φ : ℕ → ℕ := φ₀ ∘ φ₁ ∘ φ₂
  have htu : Tendsto (fun k => value S F α (jetValue E F hS α (j (φ k)))) atTop (𝓝 (value S F α u)) :=
    ht₀.comp ((hφ₁.comp hφ₂).tendsto_atTop)
  have htD : Tendsto (fun k => value S (E →L[ℝ] F) α (jetFirst E F hS α (j (φ k)))) atTop
      (𝓝 (value S (E →L[ℝ] F) α D)) := ht₁.comp hφ₂.tendsto_atTop
  have hf₀ := ftc_of_uniform_limits hS α _ _ u D htu htD
    (fun k x y => (jet_ftc E F hS α (j (φ k)) x y).1)
  have hf₁ := ftc_of_uniform_limits hS α _ _ D H htD ht₂
    (fun k x y => (jet_ftc E F hS α (j (φ k)) x y).2)
  refine ⟨ofFields hS α u D H hf₀ hf₁, ?_, φ, hφ₀.comp (hφ₁.comp hφ₂), htu, htD, ht₂⟩
  exact max_le hu (max_le hD hH)

end GaussianTilt.HolderSpace
