import GaussianTilt.MomentMapRegularitySecondOrderDensity
import GaussianTilt.MomentMapRegularityInteriorHolder

/-!
# Hölder Alexandrov density derived from the actual moment transport

This discharges the first-order inputs of the second-order density bridge:
continuous differentiability, a locally Hölder gradient, and confinement of
all gradients to the closed target all follow from the genuine transport.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators Gradient NNReal ENNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

/-- All first-order data needed by Caffarelli's second-order step are now
conclusions of the transport equation. The only target regularity input is
local `C¹` regularity of `V` on the closed bounded convex target. -/
theorem local_holder_density_of_target_transport {φ V : E n → ℝ}
    {L : ℝ≥0} (hL : LipschitzWith L φ) (hc : ConvexOn ℝ univ φ)
    {K : Set (E n)} (hK : IsOpen K) (hKc : Convex ℝ K)
    (hKb : Bornology.IsBounded K)
    (hV : ∀ p ∈ closure K, ContDiffAt ℝ 1 V p)
    (hmap : (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x)))).map
      (gradient φ) = volume.withDensity (fun x => ENNReal.ofReal
        (K.indicator (fun y => Real.exp (-V y)) x))) :
    ∀ x : E n, ∃ r c D H α : ℝ, 0 < r ∧ 0 < c ∧ 0 < D ∧ 0 < H ∧
      0 < α ∧ α ≤ 1 ∧
      (∀ y ∈ Metric.ball x r, c ≤ Real.exp (V (gradient φ y) - φ y) ∧
        Real.exp (V (gradient φ y) - φ y) ≤ D) ∧
      (∀ y ∈ Metric.ball x r, ∀ z ∈ Metric.ball x r,
        |Real.exp (V (gradient φ y) - φ y) - Real.exp (V (gradient φ z) - φ z)| ≤
          H * ‖y - z‖ ^ α) := by
  have hVc : ContinuousOn V (closure K) := fun p hp => (hV p hp).continuousAt.continuousWithinAt
  have hC1 := contDiff_one_of_target_density hL hc hK hKc hKb hVc hmap
  have hd : Differentiable ℝ φ := hC1.differentiable (by norm_num)
  have hg : Continuous (gradient φ) := continuous_gradient_of_lipschitz_convex_differentiable hL hc hd
  have hgK (x : E n) : gradient φ x ∈ closure K :=
    supportsAt_mem_closure_of_ae_gradient hL hc hKc
      (ae_gradient_mem_of_target_density hL.continuous hK (hVc.mono subset_closure) hmap)
      (supportsAt_gradient hc (hd x))
  exact local_holder_density_of_local_holder_gradient hL hg (fun x => hV _ (hgK x))
    (local_holder_gradient_of_target_density hL hc hK hKc hKb hVc hmap)

/-- For a globally smooth target potential, the literal source density is
continuous even before second-order regularity of the source is proved. -/
theorem continuous_density_of_target_transport {φ V : E n → ℝ}
    {L : ℝ≥0} (hL : LipschitzWith L φ) (hc : ConvexOn ℝ univ φ)
    {K : Set (E n)} (hK : IsOpen K) (hKc : Convex ℝ K)
    (hKb : Bornology.IsBounded K) (hV : Continuous V)
    (hmap : (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x)))).map
      (gradient φ) = volume.withDensity (fun x => ENNReal.ofReal
        (K.indicator (fun y => Real.exp (-V y)) x))) :
    Continuous (fun x => Real.exp (V (gradient φ x) - φ x)) := by
  have hC1 := contDiff_one_of_target_density hL hc hK hKc hKb hV.continuousOn hmap
  have hg := continuous_gradient_of_lipschitz_convex_differentiable hL hc
    (hC1.differentiable (by norm_num))
  exact Real.continuous_exp.comp ((hV.comp hg).sub hL.continuous)

end GaussianTilt.MomentMapRegularity
