import GaussianTilt.MomentMapLinearDirichletNewtonianPotentialCompactness

/-! # Genuine C²,α Poisson potentials for compact Hölder data -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff Convolution BoundedContinuousFunction
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapSchauder GaussianTilt.HolderSpace
variable {n : ℕ}

def kernelHessianTrace (B : KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ) : ℝ :=
  ∑ i, B (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ i)

lemma continuous_kernelHessianTrace : Continuous (kernelHessianTrace (n := n)) := by
  unfold kernelHessianTrace
  fun_prop

lemma kernelLaplacian_eq_trace {u : KernelSpace n → ℝ} (hu : ContDiff ℝ 2 u) (x : KernelSpace n) :
    kernelLaplacian u x = kernelHessianTrace (fderiv ℝ (fderiv ℝ u) x) := by
  simp only [kernelLaplacian, directionalHessian_eq_secondFrechet hu, kernelHessianTrace]

lemma potential_eq_jet_nhds {f : KernelSpace n → ℝ} {R α : ℝ}
    (j : Jet (KernelSpace n) ℝ (convex_closedBall (0 : KernelSpace n) R) α)
    (hj : ∀ y : Metric.closedBall (0 : KernelSpace n) R,
      value _ ℝ α (jetValue (KernelSpace n) ℝ (convex_closedBall (0 : KernelSpace n) R) α j) y = newtonianPotential f y)
    {x : KernelSpace n} (hx : x ∈ interior (Metric.closedBall (0 : KernelSpace n) R)) :
    newtonianPotential f =ᶠ[𝓝 x]
      extendValue α (jetValue (KernelSpace n) ℝ (convex_closedBall (0 : KernelSpace n) R) α j) := by
  filter_upwards [isOpen_interior.mem_nhds hx] with y hy
  rw [extendValue_mem α _ (interior_subset hy)]
  exact (hj ⟨y, interior_subset hy⟩).symm

lemma potential_second_eq_jet {f : KernelSpace n → ℝ} {R α : ℝ} (hα : 0 < α)
    (j : Jet (KernelSpace n) ℝ (convex_closedBall (0 : KernelSpace n) R) α)
    (hj : ∀ y : Metric.closedBall (0 : KernelSpace n) R,
      value _ ℝ α (jetValue (KernelSpace n) ℝ (convex_closedBall (0 : KernelSpace n) R) α j) y = newtonianPotential f y)
    {x : KernelSpace n} (hx : x ∈ interior (Metric.closedBall (0 : KernelSpace n) R)) :
    fderiv ℝ (fderiv ℝ (newtonianPotential f)) x =
      value _ (KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ) α
        (jetSecond (KernelSpace n) ℝ (convex_closedBall (0 : KernelSpace n) R) α j) ⟨x, interior_subset hx⟩ := by
  rw [(potential_eq_jet_nhds j hj hx).fderiv.fderiv.self_of_nhds,
    jet_second_eq_fderiv_fderiv (convex_closedBall (0 : KernelSpace n) R) hα j hx,
    extendValue_mem α _ (interior_subset hx)]

/-- Global C² regularity of the literal Newtonian integral for compact
Hölder data, proved by actual smooth approximation and compatible jet limits. -/
theorem newtonianPotential_contDiff_two [NeZero n]
    {f : KernelSpace n → ℝ} (hf : Continuous f) (hs : HasCompactSupport f)
    {α H : ℝ} (hα : 0 < α) (hα1 : α < 1) (hH : 0 ≤ H)
    (hholder : ∀ x y, |f x - f y| ≤ H * ‖x - y‖ ^ α) :
    ContDiff ℝ 2 (newtonianPotential f) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  let R := ‖x‖ + 1
  obtain ⟨j, hj, φ, hφ, hlim⟩ := exists_newtonianPotential_holder_jet hf hs hα hα1 hH
    (show 0 ≤ R by dsimp [R]; positivity) hholder
  have hx : x ∈ interior (Metric.closedBall (0 : KernelSpace n) R) := by
    rw [interior_closedBall, Metric.mem_ball, dist_zero_right]
    · exact lt_add_one _
    · dsimp [R]; positivity
  exact ((jet_contDiffOn_two (convex_closedBall (0 : KernelSpace n) R) hα j).contDiffAt
    (isOpen_interior.mem_nhds hx)).congr_of_eventuallyEq (potential_eq_jet_nhds j hj hx)

/-- The genuine pointwise Poisson equation survives the proved Hessian
limit and the true normalized mollifier limit. -/
theorem newtonianPotential_laplacian_holder [NeZero n]
    {f : KernelSpace n → ℝ} (hf : Continuous f) (hs : HasCompactSupport f)
    {α H : ℝ} (hα : 0 < α) (hα1 : α < 1) (hH : 0 ≤ H)
    (hholder : ∀ x y, |f x - f y| ≤ H * ‖x - y‖ ^ α) (x : KernelSpace n) :
    kernelLaplacian (newtonianPotential f) x = (2 * (n : ℝ) * fundamentalApproxMass n) * f x := by
  let R := ‖x‖ + 1
  obtain ⟨j, hj, φ, hφ, hlim⟩ := exists_newtonianPotential_holder_jet hf hs hα hα1 hH
    (show 0 ≤ R by dsimp [R]; positivity) hholder
  have hx : x ∈ interior (Metric.closedBall (0 : KernelSpace n) R) := by
    rw [interior_closedBall, Metric.mem_ball, dist_zero_right]
    · exact lt_add_one _
    · dsimp [R]; positivity
  have ht := (continuous_kernelHessianTrace.tendsto _).comp (hlim ⟨x, interior_subset hx⟩)
  have he : (fun k => kernelHessianTrace
      (fderiv ℝ (fderiv ℝ (newtonianPotential (harmonicMollify (φ k) f))) x)) =
      (fun k => (2 * (n : ℝ) * fundamentalApproxMass n) * harmonicMollify (φ k) f x) := by
    funext k
    rw [← kernelLaplacian_eq_trace (contDiff_infty.mp (smooth_newtonianPotential
      (harmonicMollify_smooth hf.locallyIntegrable _) (harmonicMollify_compact hs _)) 2),
      newtonianPotential_laplacian (harmonicMollify_smooth hf.locallyIntegrable _) (harmonicMollify_compact hs _)]
  change Tendsto (fun k => kernelHessianTrace
    (fderiv ℝ (fderiv ℝ (newtonianPotential (harmonicMollify (φ k) f))) x)) atTop _ at ht
  rw [he] at ht
  have hft := ((harmonicMollify_tendsto_of_continuous hf x).comp hφ.tendsto_atTop).const_mul
    (2 * (n : ℝ) * fundamentalApproxMass n)
  rw [kernelLaplacian_eq_trace (newtonianPotential_contDiff_two hf hs hα hα1 hH hholder),
    potential_second_eq_jet hα j hj hx]
  exact tendsto_nhds_unique ht hft

/-- The actual Hessian has a local Hölder modulus on every compact ball. -/
theorem newtonianPotential_hessian_locally_holder [NeZero n]
    {f : KernelSpace n → ℝ} (hf : Continuous f) (hs : HasCompactSupport f)
    {α H : ℝ} (hα : 0 < α) (hα1 : α < 1) (hH : 0 ≤ H)
    (hholder : ∀ x y, |f x - f y| ≤ H * ‖x - y‖ ^ α) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Metric.closedBall (0 : KernelSpace n) R,
      ∀ y ∈ Metric.closedBall (0 : KernelSpace n) R,
        ‖fderiv ℝ (fderiv ℝ (newtonianPotential f)) x - fderiv ℝ (fderiv ℝ (newtonianPotential f)) y‖ ≤
          C * ‖x - y‖ ^ α := by
  obtain ⟨j, hj, φ, hφ, hlim⟩ := exists_newtonianPotential_holder_jet hf hs hα hα1 hH
    (show 0 ≤ R + 1 by linarith) hholder
  let J := jetSecond (KernelSpace n) ℝ (convex_closedBall (0 : KernelSpace n) (R + 1)) α j
  refine ⟨‖J‖, norm_nonneg _, ?_⟩
  intro x hx y hy
  have hin {z : KernelSpace n} (hz : z ∈ Metric.closedBall (0 : KernelSpace n) R) :
      z ∈ interior (Metric.closedBall (0 : KernelSpace n) (R + 1)) := by
    rw [interior_closedBall, Metric.mem_ball, dist_zero_right]
    · have hn : ‖z‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
      linarith
    · positivity
  rw [potential_second_eq_jet hα j hj (hin hx), potential_second_eq_jet hα j hj (hin hy)]
  simpa only [Subtype.dist_eq, dist_eq_norm] using
    norm_value_sub_le (Metric.closedBall (0 : KernelSpace n) (R + 1))
      (KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ) α J ⟨x, interior_subset (hin hx)⟩ ⟨y, interior_subset (hin hy)⟩

end GaussianTilt.MomentMapLinearDirichlet
