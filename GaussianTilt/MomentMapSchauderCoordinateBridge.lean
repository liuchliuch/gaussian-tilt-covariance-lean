import GaussianTilt.MomentMapSchauderSourceRHS
import GaussianTilt.MomentMapRegularityBallHessian

/-! # Exact agreement of raw-coordinate and Euclidean source Hessians -/
noncomputable section
open Set
open scoped ContDiff Gradient
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapRegularity GaussianTilt.Letwin

lemma secondFrechet_comp_linear_between {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : F → ℝ} (hu : ContDiff ℝ 2 u) (P : E →L[ℝ] F) (x : E) :
    fderiv ℝ (fderiv ℝ (u ∘ P)) x =
      (fderiv ℝ (fderiv ℝ u) (P x)).bilinearComp P P := by
  have hud := hu.differentiable (by norm_num)
  have hDu : Differentiable ℝ (fderiv ℝ u) :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiable le_rfl
  have he : fderiv ℝ (u ∘ P) = (fun y => (fderiv ℝ u (P y)).comp P) := by
    funext y
    rw [fderiv_comp y (hud _) P.differentiableAt, P.fderiv]
  rw [he, fderiv_clm_comp (c := fun y => fderiv ℝ u (P y)) (d := fun _ => P)
    ((hDu _).comp x P.differentiableAt) (differentiableAt_const P)]
  have hdc : fderiv ℝ (fun y => fderiv ℝ u (P y)) x =
      (fderiv ℝ (fderiv ℝ u) (P x)).comp P :=
    ((hDu (P x)).hasFDerivAt.comp x P.hasFDerivAt).fderiv
  rw [hdc]
  ext v w
  simp [ContinuousLinearMap.bilinearComp_apply]

variable {n : ℕ}

lemma coordinateEquiv_symm_single (i : Fin n) :
    (coordinateEquiv n).symm (Pi.single i 1)=EuclideanSpace.basisFun (Fin n) ℝ i := by
  rw [EuclideanSpace.basisFun_apply]
  rfl

/-- The two source theories use exactly the same Hessian matrix, rather
than merely equivalent norms or a chosen matrix representative. -/
theorem coordinateHessian_pullback_eq_euclidean {φ : KernelSpace n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (x : KernelSpace n) :
    coordinateHessian (coordinatePullback φ) (coordinateEquiv n x)=euclideanHessianMatrix φ x := by
  have hc : ContDiff ℝ 2 (coordinatePullback φ) := hφ.comp (coordinateEquiv n).symm.contDiff
  ext i j
  rw [coordinateHessian_eq_fderiv_fderiv hc]
  change fderiv ℝ (fderiv ℝ (φ ∘ (coordinateEquiv n).symm.toContinuousLinearMap))
    (coordinateEquiv n x) (Pi.single j 1) (Pi.single i 1)=_
  rw [secondFrechet_comp_linear_between hφ]
  simp only [ContinuousLinearMap.bilinearComp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply, coordinateEquiv_symm_single]
  exact (hφ.contDiffAt.isSymmSndFDerivAt (by norm_num)) _ _

/-- A literal raw-coordinate Monge–Ampère equation transfers exactly to
the Euclidean operator used by the proved Schauder estimates. -/
theorem euclidean_source_equation_of_coordinate {φ V : KernelSpace n → ℝ}
    (hφ : ContDiff ℝ 2 φ)
    (hpos : ∀ x, (coordinateHessian (coordinatePullback φ) x).PosDef)
    (hMA : ∀ x, Real.log (coordinateHessian (coordinatePullback φ) x).det=
      -coordinatePullback φ x+coordinatePullback V (coordinateGradient (coordinatePullback φ) x)) :
    (∀ x, (euclideanHessianMatrix φ x).PosDef) ∧
    (∀ x, Real.log (euclideanHessianMatrix φ x).det= -φ x+V (gradient φ x)) := by
  constructor
  · intro x
    rw [← coordinateHessian_pullback_eq_euclidean hφ]
    exact hpos _
  · intro x
    have hh := hMA (coordinateEquiv n x)
    rw [coordinateHessian_pullback_eq_euclidean hφ,
      coordinateGradient_pullback (hφ.differentiable (by norm_num))] at hh
    simpa only [coordinatePullback, Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using hh

/-- The first genuine source bootstrap from the literal moment transport.
Positive definiteness and the Monge–Ampère equation are derived only after
first C²,α regularity, using the previously proved Jacobian theorem. -/
theorem moment_source_contDiff_three_of_transport [NeZero n]
    {φ V : KernelSpace n → ℝ} (hφ : ContDiff ℝ 2 φ)
    {Ω : Set (KernelSpace n)} (hΩ : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (hV : ContDiffOn ℝ 2 V Ω) (hgrad : ∀ x, gradient φ x ∈ Ω)
    (hc : StrictConvexOn ℝ univ (coordinatePullback φ))
    {f : CoordinateSpace n → ℝ} (hfm : Measurable f) (hfn : ∀ z, 0 ≤ f z)
    (hVc : Continuous (fun x => coordinatePullback V (coordinateGradient (coordinatePullback φ) x)))
    (hvalue : ∀ x, f (coordinateGradient (coordinatePullback φ) x)=
      Real.exp (-coordinatePullback V (coordinateGradient (coordinatePullback φ) x)))
    (hmap : momentMeasure (coordinatePullback φ)=MeasureTheory.volume.withDensity (fun x => ENNReal.ofReal (f x)))
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hloc : ∀ a : KernelSpace n, ∃ R H : ℝ, 0 < R ∧ 0 ≤ H ∧
      ∀ x ∈ Metric.closedBall a (2*R), ∀ y ∈ Metric.closedBall a (2*R),
        ‖fderiv ℝ (fderiv ℝ φ) x-fderiv ℝ (fderiv ℝ φ) y‖ ≤ H*‖x-y‖^α) :
    ContDiff ℝ 3 φ := by
  have hφc : ContDiff ℝ 2 (coordinatePullback φ) := hφ.comp (coordinateEquiv n).symm.contDiff
  obtain ⟨hpos, hMA⟩ := posDef_and_mongeAmpere_of_strictConvex_transport hφc hc hfm hfn hVc hvalue hmap
  obtain ⟨hepos, heMA⟩ := euclidean_source_equation_of_coordinate hφ hpos hMA
  exact moment_source_contDiff_three hφ hΩ hΩc hV hgrad hepos heMA hα hα1 hloc

end GaussianTilt.MomentMapSchauder
