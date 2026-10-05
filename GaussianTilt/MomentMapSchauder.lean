import GaussianTilt.MomentMapSchauderSmoothBootstrap
import GaussianTilt.MomentMapSchauderConstantInterior
import GaussianTilt.MomentMapSchauderLocalMongeAmpere
import GaussianTilt.MomentMapSchauderLocalExponents
import GaussianTilt.MomentMapSchauderCoordinateDensity
import GaussianTilt.MomentMapSchauderBoundaryEstimate
import GaussianTilt.MomentMapSchauderBoundaryVariableDrift
import GaussianTilt.MomentMapSchauderGlobalCofactorEstimate

/-!
# Proven elliptic estimates and the moment-source smooth bootstrap

Public endpoints in `GaussianTilt.MomentMapSchauder`:

* `exists_constant_interior_holder_of_C2` and
  `exists_poisson_interior_holder_of_C2` derive interior Hessian Hölder
  regularity from a genuinely C² solution and Hölder forcing.
* `exists_interior_first_jet_schauder` proves a local variable-coefficient
  a-priori estimate. Its initial Hessian bounds are completely absorbed.
* `exists_uniform_source_difference_schauder` proves estimates uniform in
  the actual source difference step, with derived averaged-inverse
  coefficients and the literal nondivergence equation.
* `exists_linear_third_order_holder` proves the one-derivative C³,α gain
  for true linear equations with C¹,α coefficients and forcing.
* `reference_contDiffOn_infty_of_C2_lipschitz_hessian` proves local
  smoothness of determinant-one reference solutions from actual local C²
  and Lipschitz-Hessian data, without extending their PDE or positivity.
* `coordinate_positive_density_contDiffOn_infty_of_holder_entries`
  proves interior smoothness directly in raw coordinates for a smooth
  positive spatial density and actual locally positive C²,α Hessian.
* `exists_flat_boundary_schauder_jet` constructs a genuine compatible
  C²,α jet on the closed half-ball from the literal weak Poisson equation,
  with a quantitative norm bound and no initial boundary derivatives.
* `exists_rescaled_normalized_boundary_first_jet_bound` proves the true
  variable-coefficient boundary cutoff/freezing estimate, absorbing the
  initial Hessian modulus and choosing the small radius from the given
  coefficient modulus.
* `exists_boundary_drift_jet_estimate_small_highest` includes the actual
  curvature drift and eliminates lower jets by one-sided interpolation,
  leaving an arbitrarily small global highest-norm term for compact-cover
  absorption.
* `exists_smooth_domain_global_schauder_estimate` proves the genuine
  compact-family global C²,α a priori estimate on every constructed
  smooth convex body, with actual curved-chart drift and norm absorption.
* `exists_smooth_domain_cofactor_homotopy_uniform_estimate` constructs
  the uniform inverse-norm bound for the literal cofactor homotopy,
  combining that global estimate with the actual quadratic C⁰ barrier.
* `moment_source_contDiff_infty` proves smoothness after the genuine first
  C²,α source stage, by the actual higher differentiated equations.
* `moment_source_contDiff_infty_of_transport` additionally derives
  positive definiteness and the classical Monge–Ampère equation from the
  literal moment transport, only after first C² regularity.

The proof chain includes actual radial integrability/scaling,
Newtonian singular-integral Hölder estimates, exact Hessian Green
representation, coefficient freezing, cutoff localization, Taylor
interpolation, geometric absorption, real derivative-limit compactness,
and finite-basis reconstruction of actual higher derivative tensors.

The first C²,α construction for an Alexandrov solution is a separate
prerequisite; this module does not assume ellipticity before that stage.
-/
