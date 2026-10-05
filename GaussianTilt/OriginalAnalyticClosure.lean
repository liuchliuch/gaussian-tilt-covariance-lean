import GaussianTilt.MomentMapClassicalDirichletSolved
import GaussianTilt.MomentMapRegularityClassicalSourceBridge
import GaussianTilt.ActualUpperFlowGradient
import GaussianTilt.UpperOriginalResults

/-! # Unconditional closure of the actual source and original upper bound

The classical inner Dirichlet solver is constructed in its imported module.
No analytic estimate, smoothness, solvability, or main-bound proposition is
an argument of the results below. The independent numbered statements and
their proof bridges are kept in separate modules.
-/
noncomputable section
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.L2Operator
namespace GaussianTilt.Reference

/-- The actual compact isotropic quadratic variance theorem, after the
constructed classical Dirichlet/source chain is instantiated. -/
theorem proved_isotropicQuadraticVarianceBound : IsotropicQuadraticVarianceBound := by
  apply MomentMapRegularity.isotropicQuadraticVarianceBound_of_classical_inner_solvers
  intro n hn S d
  exact d.exists_classical_unit_dirichlet

/-- The full original upper bound, for actual compactly supported isotropic
logconcave laws and every nonnegative precision. -/
theorem proved_original_upper_bound : UpperBound :=
  upperBound_of_isotropic_bound proved_isotropicQuadraticVarianceBound

/-- The original matching actual-measure upper and unconditional-body lower
bounds, with no analytic premise. -/
theorem proved_original_main_bounds : UpperBound ∧ LowerBound :=
  mainBounds_of_isotropic_bound proved_isotropicQuadraticVarianceBound

/-- The actual supremum has the original sharp two-sided dimension scale. -/
theorem proved_original_sharp_scale : SharpScale :=
  sharpScale_of_isotropic_bound proved_isotropicQuadraticVarianceBound

end GaussianTilt.Reference
