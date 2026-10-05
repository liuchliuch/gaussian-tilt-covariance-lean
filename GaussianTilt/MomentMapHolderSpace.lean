import Mathlib

/-! # A genuine Hölder Banach space as a closed difference-quotient graph

The ambient product consists of bounded continuous functions and bounded
continuous off-diagonal difference quotients. Its closed linear graph is
complete, and the inherited norm controls both the supremum and the actual
Hölder modulus. No completeness or Hölder-space axiom is used.
-/
noncomputable section
open Set Filter
open scoped Topology BoundedContinuousFunction
namespace GaussianTilt.HolderSpace
variable (X F : Type*) [MetricSpace X] [NormedAddCommGroup F] [NormedSpace ℝ F]

abbrev DistinctPairs := {p : X × X // p.1 ≠ p.2}
abbrev Ambient := (X →ᵇ F) × (DistinctPairs X →ᵇ F)

def defect (α : ℝ) (p : DistinctPairs X) : Ambient X F →L[ℝ] F :=
  (BoundedContinuousFunction.evalCLM ℝ p).comp (ContinuousLinearMap.snd ℝ _ _) -
    (dist p.1.1 p.1.2 ^ α)⁻¹ •
      (((BoundedContinuousFunction.evalCLM ℝ p.1.1).comp (ContinuousLinearMap.fst ℝ _ _)) -
        ((BoundedContinuousFunction.evalCLM ℝ p.1.2).comp (ContinuousLinearMap.fst ℝ _ _)))

def graph (α : ℝ) : Submodule ℝ (Ambient X F) :=
  ⨅ p : DistinctPairs X, LinearMap.ker (defect X F α p).toLinearMap

lemma mem_graph_iff (α : ℝ) (z : Ambient X F) : z ∈ graph X F α ↔
    ∀ p : DistinctPairs X, z.2 p = (dist p.1.1 p.1.2 ^ α)⁻¹ • (z.1 p.1.1 - z.1 p.1.2) := by
  simp only [graph, Submodule.mem_iInf, LinearMap.mem_ker]
  change (∀ p : DistinctPairs X,
    z.2 p - (dist p.1.1 p.1.2 ^ α)⁻¹ • (z.1 p.1.1 - z.1 p.1.2) = 0) ↔ _
  simp only [sub_eq_zero]

lemma isClosed_graph (α : ℝ) : IsClosed (graph X F α : Set (Ambient X F)) := by
  have he : (graph X F α : Set (Ambient X F)) =
      ⋂ p : DistinctPairs X, {z | defect X F α p z = 0} := by
    ext z
    simp only [mem_iInter, mem_setOf_eq]
    change (z ∈ graph X F α) ↔ ∀ p : DistinctPairs X, defect X F α p z = 0
    simp only [graph, Submodule.mem_iInf, LinearMap.mem_ker]
    rfl
  rw [he]
  exact isClosed_iInter (fun p => isClosed_eq (defect X F α p).continuous continuous_const)

def Space (α : ℝ) := ↥(graph X F α)

instance instNormedAddCommGroupSpace (α : ℝ) : NormedAddCommGroup (Space X F α) :=
  inferInstanceAs (NormedAddCommGroup ↥(graph X F α))

instance instNormedSpaceSpace (α : ℝ) : NormedSpace ℝ (Space X F α) :=
  inferInstanceAs (NormedSpace ℝ ↥(graph X F α))

instance completeSpace (α : ℝ) [CompleteSpace F] : CompleteSpace (Space X F α) :=
  (isClosed_graph X F α).completeSpace_coe

/-- The actual bounded function underlying a Hölder graph element. -/
def value (α : ℝ) : Space X F α →L[ℝ] (X →ᵇ F) :=
  (ContinuousLinearMap.fst ℝ _ _).comp (graph X F α).subtypeL

lemma value_injective (α : ℝ) : Function.Injective (value X F α) := by
  intro f g hfg
  apply Subtype.ext
  apply Prod.ext
  · exact hfg
  · apply BoundedContinuousFunction.ext
    intro p
    rw [(mem_graph_iff X F α f.1).mp f.2 p, (mem_graph_iff X F α g.1).mp g.2 p]
    have he : f.1.1 = g.1.1 := hfg
    rw [he]

lemma norm_value_le (α : ℝ) (f : Space X F α) : ‖value X F α f‖ ≤ ‖f‖ :=
  le_max_left _ _

lemma norm_value_apply_le (α : ℝ) (f : Space X F α) (x : X) : ‖value X F α f x‖ ≤ ‖f‖ :=
  (value X F α f).norm_coe_le_norm x |>.trans (norm_value_le X F α f)

/-- The inherited Banach norm controls the literal Hölder quotient. -/
theorem norm_value_sub_le (α : ℝ) (f : Space X F α) (x y : X) :
    ‖value X F α f x - value X F α f y‖ ≤ ‖f‖ * dist x y ^ α := by
  by_cases hxy : x = y
  · subst y
    simp only [sub_self, norm_zero]
    exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (dist_nonneg) _)
  let p : DistinctPairs X := ⟨(x, y), hxy⟩
  have hd : 0 < dist x y ^ α := Real.rpow_pos_of_pos (dist_pos.mpr hxy) _
  have he := (mem_graph_iff X F α f.1).mp f.2 p
  have hq : ‖f.1.2 p‖ ≤ ‖f‖ := (f.1.2.norm_coe_le_norm p).trans (le_max_right _ _)
  have hn := congrArg norm he
  change ‖f.1.2 p‖ = ‖(dist x y ^ α)⁻¹ • (f.1.1 x - f.1.1 y)‖ at hn
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd)] at hn
  change ‖f.1.1 x - f.1.1 y‖ ≤ ‖f‖ * dist x y ^ α
  rw [hn] at hq
  have hh := mul_le_mul_of_nonneg_right hq hd.le
  field_simp at hh
  simpa only [mul_comm] using hh

def increment (α : ℝ) (f : X →ᵇ F) (p : DistinctPairs X) : F :=
  (dist p.1.1 p.1.2 ^ α)⁻¹ • (f p.1.1 - f p.1.2)

lemma continuous_increment (α : ℝ) (f : X →ᵇ F) : Continuous (increment X F α f) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have hd : Continuous (fun q : DistinctPairs X => dist q.1.1 q.1.2) := by fun_prop
  have hdn : dist p.1.1 p.1.2 ≠ 0 := (dist_pos.mpr p.2).ne'
  have hrn : dist p.1.1 p.1.2 ^ α ≠ 0 := (Real.rpow_pos_of_pos (dist_pos.mpr p.2) _).ne'
  exact ((hd.continuousAt.rpow_const (Or.inl hdn)).inv₀ hrn).smul
    (((f.continuous.comp (continuous_fst.comp continuous_subtype_val)).sub
      (f.continuous.comp (continuous_snd.comp continuous_subtype_val))).continuousAt)

lemma increment_norm_le (α : ℝ) (f : X →ᵇ F) {C : ℝ}
    (hf : ∀ x y : X, ‖f x - f y‖ ≤ C * dist x y ^ α) (p : DistinctPairs X) :
    ‖increment X F α f p‖ ≤ C := by
  have hd : 0 < dist p.1.1 p.1.2 ^ α := Real.rpow_pos_of_pos (dist_pos.mpr p.2) _
  have hh := mul_le_mul_of_nonneg_left (hf p.1.1 p.1.2) (inv_nonneg.mpr hd.le)
  unfold increment
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd)]
  convert hh using 1
  field_simp

/-- Every actual bounded Hölder function gives an element of the complete
closed graph; the representation adds no hidden regularity assumption. -/
def ofBounded (α : ℝ) (f : X →ᵇ F) (C : ℝ)
    (hf : ∀ x y : X, ‖f x - f y‖ ≤ C * dist x y ^ α) : Space X F α :=
  ⟨(f, BoundedContinuousFunction.ofNormedAddCommGroup (increment X F α f)
    (continuous_increment X F α f) C (increment_norm_le X F α f hf)),
    (mem_graph_iff X F α _).mpr (fun _ => rfl)⟩

@[simp] lemma value_ofBounded (α : ℝ) (f : X →ᵇ F) (C : ℝ)
    (hf : ∀ x y : X, ‖f x - f y‖ ≤ C * dist x y ^ α) :
    value X F α (ofBounded X F α f C hf) = f := rfl

lemma norm_ofBounded_le (α : ℝ) (f : X →ᵇ F) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ x y : X, ‖f x - f y‖ ≤ C * dist x y ^ α) :
    ‖ofBounded X F α f C hf‖ ≤ max ‖f‖ C := by
  change max ‖f‖ ‖BoundedContinuousFunction.ofNormedAddCommGroup (increment X F α f)
    (continuous_increment X F α f) C (increment_norm_le X F α f hf)‖ ≤ max ‖f‖ C
  exact max_le_max le_rfl (BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ hC _)

end GaussianTilt.HolderSpace
