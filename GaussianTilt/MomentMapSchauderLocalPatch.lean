import GaussianTilt.MomentMapSchauderSmoothBootstrap
import GaussianTilt.MomentMapSchauderLocalSourceDifferences

/-! # Honest local extensions and agreement of actual derivative jets -/
noncomputable section
set_option maxSynthPendingDepth 1000
open Set Filter
open scoped ContDiff Topology
namespace GaussianTilt.MomentMapSchauder
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma eqOn_iteratedFDeriv_of_eqOn_open {f g : E → F} {U : Set E}
    (hU : IsOpen U) (he : EqOn f g U) (k : ℕ) :
    EqOn (iteratedFDeriv ℝ k f) (iteratedFDeriv ℝ k g) U := by
  intro x hx
  have hh : f =ᶠ[𝓝 x] g := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact he hy
  exact (hh.iteratedFDeriv ℝ k).self_of_nhds

lemma HolderJetOn.congr_of_eqOn_open {f g : E → F} {U S : Set E} {k : ℕ} {α : ℝ}
    (hf : HolderJetOn α k f S) (hU : IsOpen U) (hS : S ⊆ U) (he : EqOn f g U) :
    HolderJetOn α k g S := by
  intro j hj
  exact (hf j hj).congr (fun x hx => eqOn_iteratedFDeriv_of_eqOn_open hU he j (hS hx))

/-- A genuinely local Cᵏ scalar function has a constructed global compact
Cᵏ extension agreeing on a prescribed smaller ball. No equation or Hessian
positivity is asserted outside that ball. -/
theorem exists_global_contDiff_patch [FiniteDimensional ℝ E] {u : E → ℝ}
    {U : Set E} (hU : IsOpen U) (k : ℕ) (hu : ContDiffOn ℝ (k : WithTop ℕ∞) u U)
    (a : E) {r R : ℝ} (hr : 0 < r) (hrR : r < R) (hsub : Metric.ball a R ⊆ U) :
    ∃ v : E → ℝ, ContDiff ℝ (k : WithTop ℕ∞) v ∧ HasCompactSupport v ∧ EqOn v u (Metric.ball a r) := by
  obtain ⟨χ, hχ, hχc, hs, _, hone⟩ := exists_interior_cutoff a hr hrR
  refine ⟨fun x => χ x*u x,
    contDiff_cutoff_mul_of_contDiffOn hU hu (contDiff_infty.mp hχ k) (hs.trans hsub), hχc.mul_right, ?_⟩
  intro x hx
  dsimp only
  rw [hone x (Metric.ball_subset_closedBall hx), one_mul]

theorem exists_global_contDiff_eventuallyEq [FiniteDimensional ℝ E] {u : E → ℝ}
    (k : ℕ) {a : E} (hu : ContDiffAt ℝ (k : WithTop ℕ∞) u a) :
    ∃ v : E → ℝ, ContDiff ℝ (k : WithTop ℕ∞) v ∧ v =ᶠ[𝓝 a] u := by
  obtain ⟨U, hUa, huc⟩ := hu.contDiffOn le_rfl (by simp)
  obtain ⟨R, hR, hsub⟩ := Metric.mem_nhds_iff.mp hUa
  obtain ⟨v, hvc, _, hv⟩ := exists_global_contDiff_patch Metric.isOpen_ball k (huc.mono hsub)
    a (r := R/2) (R := R) (by linarith) (by linarith) Subset.rfl
  refine ⟨v, hvc, ?_⟩
  filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by linarith : (0 : ℝ) < R/2))] with x hx
  exact hv hx

open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapRegularity GaussianTilt.Letwin
variable {n : ℕ}

/-- The exact raw-coordinate/Euclidean Hessian bridge needs only C² at the
point. This is suitable for local reference solutions on open domains. -/
theorem coordinateHessian_pullback_eq_euclidean_at {u : KernelSpace n → ℝ}
    {x : KernelSpace n} (hu : ContDiffAt ℝ 2 u x) :
    coordinateHessian (coordinatePullback u) (coordinateEquiv n x)=euclideanHessianMatrix u x := by
  obtain ⟨v, hvc, he⟩ := exists_global_contDiff_eventuallyEq 2 hu
  have hvc' : ContDiff ℝ 2 (coordinatePullback v) := hvc.comp (coordinateEquiv n).symm.contDiff
  have hec : coordinatePullback v =ᶠ[𝓝 (coordinateEquiv n x)] coordinatePullback u := by
    have ht := (coordinateEquiv n).symm.continuous.tendsto (coordinateEquiv n x)
    simp only [ContinuousLinearEquiv.symm_apply_apply] at ht
    exact he.comp_tendsto ht
  have huc' : ContDiffAt ℝ 2 (coordinatePullback u) (coordinateEquiv n x) :=
    hvc'.contDiffAt.congr_of_eventuallyEq hec.symm
  have hH : coordinateHessian (coordinatePullback v) (coordinateEquiv n x)=
      coordinateHessian (coordinatePullback u) (coordinateEquiv n x) := by
    ext i j
    rw [coordinateHessian_eq_secondFDerivAt hvc'.contDiffAt, coordinateHessian_eq_secondFDerivAt huc',
      hec.fderiv.fderiv_eq]
  rw [← hH, coordinateHessian_pullback_eq_euclidean hvc]
  ext i j
  exact congrArg (fun B : KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ => B (EuclideanSpace.basisFun (Fin n) ℝ i)
    (EuclideanSpace.basisFun (Fin n) ℝ j)) he.fderiv.fderiv_eq

end GaussianTilt.MomentMapSchauder
