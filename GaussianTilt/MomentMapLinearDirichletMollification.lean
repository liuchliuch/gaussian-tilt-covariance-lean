import GaussianTilt.MomentMapLinearDirichletBoundaryTrace
import GaussianTilt.NegativeSobolevMollifierDistribution

/-!
# Actual interior mollification of the constructed weak Dirichlet equation

Every translated compact smooth kernel supported inside the domain is an
admissible test. Thus the genuine mollified weak solution satisfies the
ordinary pointwise Poisson equation wherever the kernel fits inside Ω.
-/
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin
variable {n : ℕ}

/-- The original weak solution yields a true pointwise PDE after actual
convolution; the only geometric condition is interior support of the kernel. -/
theorem weakDirichletLaplaceSolution_convolution_equation {Ω : Set (CoordinateSpace n)}
    (i : Fin n) {R : ℝ} (hR : 0 ≤ R) (hstrip : ∀ x ∈ Ω, |x i| ≤ R)
    (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n)))
    {ρ : CoordinateSpace n → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    (x : CoordinateSpace n) (hx : tsupport (fun y => ρ (x - y)) ⊆ Ω) :
    euclideanLaplacian
      (scalarConvolution ρ (dirichletValue Ω (weakDirichletLaplaceSolution i hR hstrip f))) x =
        -scalarConvolution ρ f x := by
  have hψ : ContDiff ℝ ∞ (fun y : CoordinateSpace n => ρ (x - y)) :=
    hρ.comp (contDiff_const.sub contDiff_id)
  have hψc : HasCompactSupport (fun y => ρ (x - y)) := hρc.comp_homeomorph (Homeomorph.subLeft x)
  have he := weakDirichletLaplaceSolution_distribution i hR hstrip f hψ hψc hx
  simp only [euclideanLaplacian_const_sub_comp hρ] at he
  rw [euclideanLaplacian_scalarConvolution hρ hρc (Lp.memLp _),
    scalarConvolution_flip_apply, scalarConvolution_flip_apply]
  exact he

lemma tsupport_const_sub_subset_closedBall {ρ : CoordinateSpace n → ℝ}
    {r : ℝ} (hρ : tsupport ρ ⊆ Metric.closedBall 0 r) (x : CoordinateSpace n) :
    tsupport (fun y => ρ (x - y)) ⊆ Metric.closedBall x r := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro y hy
  have hh := hρ (subset_tsupport ρ hy)
  simpa only [Metric.mem_closedBall, dist_zero_right, dist_eq_norm, norm_sub_rev, sub_zero] using hh

/-- The explicit canonical mollifiers satisfy the actual Poisson equation
at every point whose closed kernel ball lies in the domain. -/
theorem weakDirichletLaplaceSolution_mollify_equation {Ω : Set (CoordinateSpace n)}
    (i : Fin n) {R : ℝ} (hR : 0 ≤ R) (hstrip : ∀ x ∈ Ω, |x i| ≤ R)
    (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n))) (k : ℕ)
    (x : CoordinateSpace n) (hx : Metric.closedBall x ((k : ℝ) + 1)⁻¹ ⊆ Ω) :
    euclideanLaplacian
      (mollify k (dirichletValue Ω (weakDirichletLaplaceSolution i hR hstrip f))) x =
        -mollify k f x := by
  apply weakDirichletLaplaceSolution_convolution_equation i hR hstrip f
    (canonicalMollifier_smooth n k) (canonicalMollifier_compact n k) x
  apply (tsupport_const_sub_subset_closedBall (ρ := canonicalMollifier n k) ?_ x).trans hx
  change tsupport ((canonicalMollifierBump n k).normed volume) ⊆ _
  rw [ContDiffBump.tsupport_normed_eq]
  exact subset_rfl

/-- Interior points eventually satisfy the ordinary mollified equation,
with smooth mollifications and genuine L² approximation supplied by the
fixed canonical family. -/
theorem weakDirichletLaplaceSolution_mollify_equation_eventually {Ω : Set (CoordinateSpace n)}
    (hΩ : IsOpen Ω) (i : Fin n) {R : ℝ} (hR : 0 ≤ R) (hstrip : ∀ x ∈ Ω, |x i| ≤ R)
    (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n))) {x : CoordinateSpace n} (hx : x ∈ Ω) :
    ∀ᶠ k : ℕ in atTop,
      euclideanLaplacian
        (mollify k (dirichletValue Ω (weakDirichletLaplaceSolution i hR hstrip f))) x =
          -mollify k f x := by
  obtain ⟨r, hr, hrΩ⟩ := Metric.mem_nhds_iff.mp (hΩ.mem_nhds hx)
  have ht : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  filter_upwards [(tendsto_order.mp ht).2 r hr] with k hk
  apply weakDirichletLaplaceSolution_mollify_equation i hR hstrip f k x
  exact (Metric.closedBall_subset_ball hk).trans hrΩ

end GaussianTilt.MomentMapLinearDirichlet
