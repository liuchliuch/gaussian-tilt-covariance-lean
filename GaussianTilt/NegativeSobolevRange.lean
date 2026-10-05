import GaussianTilt.EllipticRegularityRoughLiouville
import GaussianTilt.NegativeSobolevClosure

/-!
# Density of the actual weighted Laplacian range

For every smooth potential defining a finite Gibbs measure, the norm closure
of L(C∞c) is the entire mean-zero L² space. The proof invokes the proved rough
elliptic Liouville theorem and Hilbert orthogonal-complement duality. Neither
range density nor elliptic regularity is a premise.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ContDiff Topology ENNReal InnerProductSpace
namespace GaussianTilt.Letwin

/-- The orthogonal complement of the actual compact smooth generator range
consists only of genuine constant L² classes. -/
theorem weightedLaplacianToL2_orthogonal_le_constants {n : ℕ}
    {φ : CoordinateSpace n → ℝ} [IsFiniteMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ ∞ φ) :
    (LinearMap.range (weightedLaplacianToL2 hφ))ᗮ ≤ ℝ ∙ l2One (potentialMeasure φ) := by
  intro f hf
  let μ := potentialMeasure φ
  let K := LinearMap.range (weightedLaplacianToL2 hφ)
  have horth : ∀ g : CoordinateSpace n → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      (∫ x, f x * weightedLaplacian φ g x ∂μ) = 0 := by
    intro g hg hgc
    let v : smoothCompactCore n := ⟨g, hg, hgc⟩
    have hp : inner ℝ (weightedLaplacianToL2 hφ v) f = 0 :=
      (K.mem_orthogonal f).mp hf _ ⟨v, rfl⟩
    have hpair := inner_toLp_weightedLaplacian hφ (Lp.memLp f) v
    rw [Lp.toLp_coeFn] at hpair
    rw [← hpair, real_inner_comm]
    exact hp
  obtain ⟨c, hc⟩ := weighted_generator_orthogonal_ae_const hφ (Lp.memLp f) horth
  apply Submodule.mem_span_singleton.mpr
  refine ⟨c, ?_⟩
  apply Lp.ext
  filter_upwards [hc, Lp.coeFn_smul c (l2One μ), l2One_ae μ] with x hx hs ho
  simp only [Pi.smul_apply, smul_eq_mul] at hs
  rw [hs, ho, mul_one, hx]

/-- The actual missing Euclidean H⁻¹ range-density theorem. Smooth compact
generator images are norm-dense in mean-zero weighted L². Convexity is not
needed for density; it enters the separate proved Bochner estimate. -/
theorem weightedLaplacianToL2_closure_eq_meanZero {n : ℕ}
    {φ : CoordinateSpace n → ℝ} [IsFiniteMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ ∞ φ) :
    (LinearMap.range (weightedLaplacianToL2 hφ)).topologicalClosure =
      meanZeroL2 (potentialMeasure φ) := by
  apply le_antisymm (weightedLaplacianToL2_closure_le hφ)
  change (ℝ ∙ l2One (potentialMeasure φ))ᗮ ≤ _
  rw [← Submodule.orthogonal_orthogonal_eq_closure]
  exact Submodule.orthogonal_le (weightedLaplacianToL2_orthogonal_le_constants hφ)

end GaussianTilt.Letwin
