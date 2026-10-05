import GaussianTilt.MomentMapLinearDirichletFlatHarmonicTaylor
import GaussianTilt.MomentMapLinearDirichletHalfBallEuclidean

/-!
# Actual flat harmonic replacement and its quadratic error

Subtracting a genuine zero-boundary Poisson correction cancels the literal
weak forcing. The proved odd harmonic reflection and Taylor estimate then
produce a harmonic zero-plane polynomial; adding back the actual correction
costs only its proved supremum bound.
-/
noncomputable section
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 1000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

/-- A uniform quadratic approximation by genuine harmonic replacement.
The two functions solve the same literal weak equation; all regularity of
their harmonic difference is derived by reflection. -/
theorem exists_flat_harmonic_replacement_bound [NeZero n] :
    ∃ K : ℝ, 0 < K ∧ ∀ (j : Fin n) (u v : KernelSpace n → ℝ),
      MemLp u 2 volume → MemLp v 2 volume →
      ∀ Cu Cv Bu Bv : ℝ, 0 ≤ Cu → 0 ≤ Cv → 0 ≤ Bu → 0 ≤ Bv →
      (∀ x, x j ≤ 0 → u x = 0) → (∀ x, x j ≤ 0 → v x = 0) →
      (∀ x ∈ Metric.ball (0 : KernelSpace n) 2, |u x| ≤ Cu * |x j|) →
      (∀ x ∈ Metric.ball (0 : KernelSpace n) 2, |v x| ≤ Cv * |x j|) →
      (∀ x ∈ Metric.ball (0 : KernelSpace n) 2, |u x| ≤ Bu) →
      (∀ x ∈ Metric.ball (0 : KernelSpace n) 2, |v x| ≤ Bv) →
      ContinuousOn u (Metric.ball 0 2 ∩ {x | 0 < x j}) → Continuous v →
      (∀ φ : KernelSpace n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
        tsupport φ ⊆ Metric.ball 0 2 ∩ {x | 0 < x j} →
        (∫ x, u x * kernelLaplacian φ x) = ∫ x, v x * kernelLaplacian φ x) →
      ∃ A : KernelSpace n →L[ℝ] ℝ, ∃ Q : KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ,
        (∀ x, x j = 0 → flatTaylorPolynomial A Q x = 0) ∧
        (∀ x, kernelLaplacian (flatTaylorPolynomial A Q) x = 0) ∧
        (∀ z ∈ Metric.ball (0 : KernelSpace n) (1/4), 0 ≤ z j →
          |u z - flatTaylorPolynomial A Q z| ≤ K * (Bu+Bv) * ‖z‖ ^ 3 + Bv) := by
  obtain ⟨K, hK, hTaylor⟩ := exists_flat_harmonic_quadratic_approximation (n := n)
  refine ⟨K, hK, ?_⟩
  intro j u v hu hv Cu Cv Bu Bv hCu hCv hBu hBv hu0 hv0 hug hvg hub hvb huc hvc hsame
  let h := fun x => u x - v x
  have hh : MemLp h 2 volume := hu.sub hv
  have hh0 (x : KernelSpace n) (hx : x j ≤ 0) : h x = 0 := by simp [h, hu0 x hx, hv0 x hx]
  have hhg (x : KernelSpace n) (hx : x ∈ Metric.ball (0 : KernelSpace n) 2) : |h x| ≤ (Cu+Cv)*|x j| := by
    exact (abs_sub _ _).trans ((add_le_add (hug x hx) (hvg x hx)).trans_eq (by ring))
  have hhb (x : KernelSpace n) (hx : x ∈ Metric.ball (0 : KernelSpace n) 2) : |h x| ≤ Bu+Bv :=
    (abs_sub _ _).trans (add_le_add (hub x hx) (hvb x hx))
  have hhc : ContinuousOn h (Metric.ball (0 : KernelSpace n) 2 ∩ {x | 0 < x j}) :=
    huc.sub hvc.continuousOn
  have hheq : ∀ φ : KernelSpace n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Metric.ball 0 2 ∩ {x | 0 < x j} → (∫ x, h x * kernelLaplacian φ x) = 0 := by
    intro φ hφ hφc hφs
    change (∫ x, (u x-v x)*kernelLaplacian φ x) = 0
    simp_rw [sub_mul]
    rw [integral_sub (integrable_locally_mul_laplacian (hu.locallyIntegrable (by norm_num)) (contDiff_infty.mp hφ 2) hφc)
      (integrable_locally_mul_laplacian (hv.locallyIntegrable (by norm_num)) (contDiff_infty.mp hφ 2) hφc),
      hsame φ hφ hφc hφs, sub_self]
  obtain ⟨A,Q,hPlane,hHarm,hError⟩ := hTaylor j h hh (Cu+Cv) (add_nonneg hCu hCv) hh0 hhg hhc hheq
    (Bu+Bv) (add_nonneg hBu hBv) hhb
  refine ⟨A,Q,hPlane,hHarm,?_⟩
  intro z hz hzj
  have hz2 : z ∈ Metric.ball (0 : KernelSpace n) 2 := Metric.ball_subset_ball (by norm_num : (1/4 : ℝ) ≤ 2) hz
  have he : u z-flatTaylorPolynomial A Q z = (h z-flatTaylorPolynomial A Q z)+v z := by dsimp [h]; ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add (hError z hz hzj) (hvb z hz2))

end GaussianTilt.MomentMapLinearDirichlet
