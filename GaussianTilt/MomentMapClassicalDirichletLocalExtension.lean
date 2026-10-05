import GaussianTilt.MomentMapRegularityReferenceExtension
import GaussianTilt.MomentMapClassicalDirichletBoundaryAtlas
import GaussianTilt.MomentMapRegularityConstantDensityCalabi

/-! # Actual smooth coordinate representatives on compact boundary charts -/
noncomputable section
open Set Filter
open scoped Topology ContDiff Manifold
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

/-- A genuine cutoff construction in raw coordinates. No smooth extension
through the boundary of the original solution domain is assumed. -/
theorem exists_global_smooth_coordinate_eq_near_compact
    {u : CoordinateSpace n → ℝ} {U K : Set (CoordinateSpace n)}
    (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ v : CoordinateSpace n → ℝ, ContDiff ℝ ∞ v ∧ ∀ x ∈ K, v =ᶠ[𝓝 x] u := by
  obtain ⟨χ,hχ0,hχ1,hχb⟩ := exists_smooth_zero_one_nhds_of_isClosed
    𝓘(ℝ, CoordinateSpace n) hU.isClosed_compl hK.isClosed
    (disjoint_left.mpr (fun x hxU hxK => hxU (hKU hxK)))
  let v := fun x => χ x*u x
  have hχ : ContDiff ℝ ∞ (χ : CoordinateSpace n → ℝ) := χ.contMDiff.contDiff
  have hv : ContDiff ℝ ∞ v := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ U
    · exact hχ.contDiffAt.mul (hu.contDiffAt (hU.mem_nhds hx))
    · have hzero : ∀ᶠ y in 𝓝 x, χ y = 0 := hχ0.filter_mono (nhds_le_nhdsSet hx)
      apply contDiffAt_const.congr_of_eventuallyEq
      filter_upwards [hzero] with y hy
      change χ y*u y = 0
      rw [hy,zero_mul]
  refine ⟨v,hv,?_⟩
  intro x hx
  have hone : ∀ᶠ y in 𝓝 x, χ y = 1 := hχ1.filter_mono (nhds_le_nhdsSet hx)
  filter_upwards [hone] with y hy
  change χ y*u y = u y
  rw [hy,one_mul]

namespace BoundaryChartPatch
variable {w : CoordinateSpace n → ℝ} (p : BoundaryChartPatch w)

/-- Each actual chart quotient has a constructed global smooth representative
agreeing on a neighborhood of the entire compact denominator-controlled patch. -/
theorem exists_smooth_chart_representatives (hw : ContDiff ℝ ∞ w) :
    ∃ β : Fin n → CoordinateSpace n → ℝ,
      (∀ a, ContDiff ℝ ∞ (β a)) ∧
      ∀ y ∈ Metric.closedBall p.center p.radius, ∀ a,
        β a =ᶠ[𝓝 y] boundaryChartCoefficient w p.index a := by
  let U := {y | coordinateDerivative p.index w y ≠ 0}
  have hU : IsOpen U := isOpen_ne.preimage (smooth_coordinateDerivative hw p.index).continuous
  have hβ (a : Fin n) : ContDiffOn ℝ ∞ (boundaryChartCoefficient w p.index a) U :=
    fun y hy => (contDiffAt_boundaryChartCoefficient hw hy a).contDiffWithinAt
  have hKU : Metric.closedBall p.center p.radius ⊆ U := fun y hy => p.derivative_ne_zero hy
  have hex (a : Fin n) := exists_global_smooth_coordinate_eq_near_compact hU (hβ a)
    (isCompact_closedBall p.center p.radius) hKU
  choose β hβs he using hex
  exact ⟨β,hβs,fun y hy a => he a y hy⟩

/-- Compactness supplies fixed third-derivative constants for these actual
chart representatives, uniformly over the finite tangent index family. -/
theorem exists_smooth_chart_representatives_with_third_bound (hw : ContDiff ℝ ∞ w) :
    ∃ β : Fin n → CoordinateSpace n → ℝ, ∃ B₃ : ℝ, 0 ≤ B₃ ∧
      (∀ a, ContDiff ℝ ∞ (β a)) ∧
      (∀ y ∈ Metric.closedBall p.center p.radius, ∀ a,
        β a =ᶠ[𝓝 y] boundaryChartCoefficient w p.index a) ∧
      (∀ y ∈ Metric.closedBall p.center p.radius, ∀ a i j k,
        |coordinateThirdDerivative (β a) y i j k| ≤ B₃) := by
  obtain ⟨β,hβs,he⟩ := p.exists_smooth_chart_representatives hw
  have hc : Continuous (fun y => fun a i j k : Fin n => coordinateThirdDerivative (β a) y i j k) :=
    continuous_pi (fun a => continuous_pi (fun i => continuous_pi (fun j => continuous_pi
      (fun k => (smooth_coordinateThirdDerivative (hβs a) i j k).continuous))))
  obtain ⟨B,hB⟩ := (isCompact_closedBall p.center p.radius).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨β,max B 0,le_max_right _ _,hβs,he,?_⟩
  intro y hy a i j k
  have hh := hB y hy
  exact ((norm_le_pi_norm (fun k => coordinateThirdDerivative (β a) y i j k) k).trans
    ((norm_le_pi_norm (fun j k => coordinateThirdDerivative (β a) y i j k) j).trans
      ((norm_le_pi_norm (fun i j k => coordinateThirdDerivative (β a) y i j k) i).trans
        (norm_le_pi_norm (fun a i j k => coordinateThirdDerivative (β a) y i j k) a)))).trans
    (hh.trans (le_max_left _ _))

end BoundaryChartPatch
end GaussianTilt.MomentMapRegularity
