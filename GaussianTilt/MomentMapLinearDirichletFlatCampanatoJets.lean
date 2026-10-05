import GaussianTilt.MomentMapLinearDirichletFlatTaylorJets
import GaussianTilt.MomentMapCampanatoHalfBallEndpoint

/-! # Exact conversion of arbitrary bilinear Taylor data to genuine symmetric jets -/
noncomputable section
open Set
open scoped Topology ContDiff Gradient
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapRegularity GaussianTilt.MomentMapSchauder
variable {n : ℕ}

/-- An arbitrary bilinear quadratic polynomial has the same diagonal as its
actual symmetric Hessian. No symmetry of the supplied bilinear form is needed. -/
lemma flatTaylorPolynomial_eq_quadraticJet
    (A : KernelSpace n →L[ℝ] ℝ) (Q : KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ)
    (x : KernelSpace n) :
    flatTaylorPolynomial A Q x = quadraticJet 0 (gradient (flatTaylorPolynomial A Q) 0) 0
      (frechetHessian (flatTaylorPolynomial A Q) 0) x := by
  simp only [quadraticJet, sub_zero, zero_add, inner_gradient_eq_fderiv, inner_frechetHessian,
    fderiv_flatTaylorPolynomial, map_zero, ContinuousLinearMap.zero_apply, zero_add, mul_zero, add_zero]
  rw [← directionalHessian_eq_secondFrechet_at
    (contDiff_infty.mp (contDiff_flatTaylorPolynomial A Q) 2).contDiffAt,
    directionalHessian_flatTaylorPolynomial]
  unfold flatTaylorPolynomial
  ring

lemma flatTaylorPolynomial_frechetHessian_symmetric
    (A : KernelSpace n →L[ℝ] ℝ) (Q : KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ) :
    ∀ v w, inner ℝ (frechetHessian (flatTaylorPolynomial A Q) 0 v) w =
      inner ℝ v (frechetHessian (flatTaylorPolynomial A Q) 0 w) :=
  frechetHessian_symmetric (contDiff_infty.mp (contDiff_flatTaylorPolynomial A Q) 2) 0

end GaussianTilt.MomentMapLinearDirichlet
