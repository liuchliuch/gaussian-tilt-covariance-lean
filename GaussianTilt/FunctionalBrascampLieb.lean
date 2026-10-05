import GaussianTilt.FunctionalBrascampEnergy
import GaussianTilt.LetwinPerturbation

/-!
# The genuine functional Brascamp–Lieb inequality

For a smooth strictly convex potential and a bounded smooth observable, the
variance under the actual probability density `exp (-φ)` is bounded by the
actual inverse-Hessian Dirichlet integral. The sole energy hypothesis is
integrability of that explicit function.

The proof is the infinitesimal Prékopa argument: the exact Schur-complement
Hessian makes buffered joint potentials locally convex on every compact
convex cutoff; proved marginal logconcavity and differentiated integrals give
the compact inequality; actual Gibbs expectation convergence removes the
cutoff and the positive buffer tends to zero.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped ContDiff
namespace GaussianTilt.FunctionalBrascampLieb
open GaussianTilt.Letwin

/-- Functional Brascamp–Lieb for the regular finite-energy class used in
Letwin's Lemma 2.5. Neither a Poincaré inequality nor a functional variance
bound is assumed anywhere in the proof. -/
theorem variance_le_inverseHessian_energy {n : ℕ} {φ f : CoordinateSpace n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ ∞ φ) (hf : ContDiff ℝ ∞ f)
    (hH : ∀ x, (coordinateHessian φ x).PosDef)
    (hb : ∃ B : ℝ, ∀ x, |f x| ≤ B)
    (hi : Integrable (diffusionGamma (inverseHessian φ) f f) (potentialMeasure φ)) :
    variance f (potentialMeasure φ) ≤
      ∫ x, diffusionGamma (inverseHessian φ) f f x ∂potentialMeasure φ := by
  apply variance_le_of_local_jointConvex_exhaustion hφ.continuous hf.continuous
    (contDiff_inverseHessian_energy hφ hf hH).continuous hb hi
  intro m ε hε
  have h := functionalPerturbation_locally_convex hφ hf hH (cutoffBall_compact m)
    (convex_closedBall _ _) hε
  simpa only [functionalPerturbation, jointPotential] using h

end GaussianTilt.FunctionalBrascampLieb
