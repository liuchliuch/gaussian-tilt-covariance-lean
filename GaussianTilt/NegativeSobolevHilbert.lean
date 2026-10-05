import GaussianTilt.NegativeSobolevDuality
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Actual smooth cores in weighted L²

This file constructs the smooth compactly supported core as a linear space,
embeds it into the actual measure-theoretic L² Hilbert space, and proves its
density using separation by compact smooth test functions.  No density
statement is included among the hypotheses.
-/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ContDiff Topology ENNReal InnerProductSpace
namespace GaussianTilt.Letwin

/-- Smooth compactly supported real functions on coordinate space. -/
def smoothCompactCore (n : ℕ) : Submodule ℝ (CoordinateSpace n → ℝ) where
  carrier := {f | ContDiff ℝ ∞ f ∧ HasCompactSupport f}
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero⟩
  add_mem' := fun hf hg => ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  smul_mem' := fun c f hf => ⟨hf.1.const_smul c, by simpa using hf.2.smul_left (f := fun _ => c)⟩

/-- The actual L² equivalence class of a compact smooth function. -/
def smoothCompactToL2 {n : ℕ} (μ : Measure (CoordinateSpace n)) [IsFiniteMeasureOnCompacts μ] :
    smoothCompactCore n →ₗ[ℝ] Lp ℝ 2 μ where
  toFun f := (smooth_compact_memLp f.2.1 f.2.2).toLp f.1
  map_add' f g := rfl
  map_smul' c f := rfl

lemma smoothCompactToL2_ae {n : ℕ} (μ : Measure (CoordinateSpace n)) [IsFiniteMeasureOnCompacts μ]
    (f : smoothCompactCore n) : smoothCompactToL2 μ f =ᵐ[μ] f.1 :=
  (smooth_compact_memLp f.2.1 f.2.2).coeFn_toLp

/-- Smooth compactly supported functions are genuinely dense in weighted L²
for every Borel measure finite on compact sets. -/
theorem smoothCompactToL2_dense {n : ℕ} (μ : Measure (CoordinateSpace n)) [IsFiniteMeasureOnCompacts μ] :
    DenseRange (smoothCompactToL2 μ) := by
  let K := LinearMap.range (smoothCompactToL2 μ)
  have horth : Kᗮ = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro f hf
    change f = 0
    have hzero : ∀ᵐ x ∂μ, f x = 0 := by
      apply ae_eq_zero_of_integral_contDiff_smul_eq_zero
        ((Lp.memLp f).locallyIntegrable (by norm_num))
      intro g hg hgc
      let t : smoothCompactCore n := ⟨g, hg, hgc⟩
      have hp : inner ℝ (smoothCompactToL2 μ t) f = 0 :=
        (K.mem_orthogonal f).mp hf _ ⟨t, rfl⟩
      rw [L2.inner_def] at hp
      have he : (∫ x, g x • f x ∂μ) = ∫ x, inner ℝ (smoothCompactToL2 μ t x) (f x) ∂μ := by
        apply integral_congr_ae
        filter_upwards [smoothCompactToL2_ae μ t] with x hx
        simp only [hx, t, RCLike.inner_apply, conj_trivial, smul_eq_mul]
        ring
      exact he.trans hp
    apply Lp.ext
    filter_upwards [hzero, Lp.coeFn_zero (E := ℝ) (p := 2) (μ := μ)] with x hx hz
    exact hx.trans hz.symm
  have hclosure : K.topologicalClosure = ⊤ := by
    rw [← K.orthogonal_orthogonal_eq_closure, horth, Submodule.bot_orthogonal_eq_top]
  change Dense (Set.range (smoothCompactToL2 μ))
  rw [dense_iff_closure_eq]
  change (K.topologicalClosure : Set (Lp ℝ 2 μ)) = Set.univ
  rw [hclosure]
  rfl

end GaussianTilt.Letwin
