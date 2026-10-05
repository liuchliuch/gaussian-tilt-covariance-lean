import GaussianTilt.MomentMapHolderSpace

/-! # Actual bounded linear operations on Hölder functions -/
noncomputable section
open Set
open scoped Topology BoundedContinuousFunction
namespace GaussianTilt.HolderSpace
variable (X F G : Type*) [MetricSpace X]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Postcomposition by a continuous linear map acts on both the actual
value and its normalized difference quotient. -/
def map (α : ℝ) (L : F →L[ℝ] G) : Space X F α →L[ℝ] Space X G α :=
  ((((L.compLeftContinuousBounded X).prodMap
      (L.compLeftContinuousBounded (DistinctPairs X))).comp (graph X F α).subtypeL).codRestrict
    (graph X G α) (by
      intro f
      apply (mem_graph_iff X G α _).mpr
      intro p
      change L (f.1.2 p) = (dist p.1.1 p.1.2 ^ α)⁻¹ • (L (f.1.1 p.1.1) - L (f.1.1 p.1.2))
      rw [(mem_graph_iff X F α f.1).mp f.2 p, map_smul, map_sub]))

@[simp] lemma value_map (α : ℝ) (L : F →L[ℝ] G) (f : Space X F α) (x : X) :
    value X G α (map X F G α L f) x = L (value X F α f x) := rfl

/-- Point evaluation is continuous in the true Hölder Banach norm. -/
def eval (α : ℝ) (x : X) : Space X F α →L[ℝ] F :=
  (BoundedContinuousFunction.evalCLM ℝ x).comp (value X F α)

@[simp] lemma eval_apply (α : ℝ) (x : X) (f : Space X F α) :
    eval X F α x f = value X F α f x := rfl

lemma norm_map_le (α : ℝ) (L : F →L[ℝ] G) (f : Space X F α) :
    ‖map X F G α L f‖ ≤ ‖L‖ * ‖f‖ := by
  change max ‖L.compLeftContinuousBounded X f.1.1‖
      ‖L.compLeftContinuousBounded (DistinctPairs X) f.1.2‖ ≤ ‖L‖ * ‖f‖
  apply max_le
  · apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    intro x
    exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      ((f.1.1.norm_coe_le_norm x).trans (le_max_left _ _)) (norm_nonneg L))
  · apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    intro p
    exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      ((f.1.2.norm_coe_le_norm p).trans (le_max_right _ _)) (norm_nonneg L))

end GaussianTilt.HolderSpace
