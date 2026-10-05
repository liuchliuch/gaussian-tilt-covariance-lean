import GaussianTilt.MomentMapHolderSmoothEmbedding

/-! # Actual supremum/modulus bounds control the complete Hölder jet norm -/
noncomputable section
open Set
open scoped Topology BoundedContinuousFunction ContDiff
namespace GaussianTilt.HolderSpace
variable {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MetricSpace X]

lemma norm_le_of_value_bounds {α C : ℝ} (hC : 0 ≤ C) (f : Space X F α)
    (hb : ∀ x, ‖value X F α f x‖ ≤ C)
    (hh : ∀ x y, ‖value X F α f x - value X F α f y‖ ≤ C * dist x y ^ α) : ‖f‖ ≤ C := by
  let g := ofBounded X F α (value X F α f) C hh
  have he : f = g := value_injective X F α rfl
  have hn := norm_ofBounded_le X F α (value X F α f) hC hh
  rw [he]
  exact hn.trans (max_le ((BoundedContinuousFunction.norm_le hC).mpr hb) le_rfl)

lemma norm_jet_le_of_field_norms {S : Set E} (hS : Convex ℝ S) {α C : ℝ}
    (j : Jet E F hS α)
    (hu : ‖jetValue E F hS α j‖ ≤ C)
    (hD : ‖jetFirst E F hS α j‖ ≤ C)
    (hH : ‖jetSecond E F hS α j‖ ≤ C) : ‖j‖ ≤ C :=
  max_le hu (max_le hD hH)

end GaussianTilt.HolderSpace
