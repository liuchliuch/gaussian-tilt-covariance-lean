import GaussianTilt.MomentMapLinearDirichletCoordinates
import GaussianTilt.MomentMapLinearDirichletClassicalEquation

/-!
# Patching an interior classical representative to the actual zero boundary

An AE defining-function bound becomes pointwise by interior continuity.
Its zero extension is then continuous at every boundary point by squeezing
against the continuous defining function. This preserves the original AE
class and supplies genuine boundary values, without an assumed trace.
-/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma continuousOn_bound_of_ae {Ω : Set (CoordinateSpace n)} (hΩ : IsOpen Ω)
    {v w : CoordinateSpace n → ℝ} (hv : ContinuousOn v Ω) (hw : Continuous w) {B : ℝ}
    (hbound : ∀ᵐ x ∂volume, x ∈ Ω → |v x| ≤ B * |w x|) :
    ∀ x ∈ Ω, |v x| ≤ B * |w x| := by
  have hc : ContinuousOn (fun x => |v x|) Ω := by simpa only [Real.norm_eq_abs] using hv.norm
  have hd : ContinuousOn (fun x => B * |w x|) Ω :=
    continuousOn_const.mul hw.abs.continuousOn
  have hae : (fun x => min |v x| (B * |w x|)) =ᵐ[volume.restrict Ω] (fun x => |v x|) := by
    apply (ae_restrict_iff' hΩ.measurableSet).mpr
    filter_upwards [hbound] with x hx hxΩ
    exact min_eq_left (hx hxΩ)
  have he := Measure.eqOn_open_of_ae_eq hae hΩ (hc.inf hd) hc
  intro x hx
  exact min_eq_left_iff.mp (he hx)

/-- The actual zero extension of an interior continuous function is
continuous across the boundary whenever a vanishing defining barrier
controls it almost everywhere. -/
theorem continuous_zero_extension_of_boundary_barrier {Ω : Set (CoordinateSpace n)}
    (hΩ : IsOpen Ω) {v w : CoordinateSpace n → ℝ}
    (hv : ContinuousOn v Ω) (hw : Continuous w) (hwb : ∀ x ∈ frontier Ω, w x = 0)
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ᵐ x ∂volume, x ∈ Ω → |v x| ≤ B * |w x|) :
    Continuous (Ω.indicator v) := by
  classical
  have hvbound := continuousOn_bound_of_ae hΩ hv hw hbound
  have hglobal (x : CoordinateSpace n) : |Ω.indicator v x| ≤ B * |w x| := by
    by_cases hx : x ∈ Ω
    · rw [indicator_of_mem hx]
      exact hvbound x hx
    · rw [indicator_of_notMem hx, abs_zero]
      exact mul_nonneg hB (abs_nonneg _)
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hxΩ : x ∈ Ω
  · apply (hv.continuousAt (hΩ.mem_nhds hxΩ)).congr_of_eventuallyEq
    filter_upwards [hΩ.mem_nhds hxΩ] with y hy
    exact indicator_of_mem hy v
  · have hvx : Ω.indicator v x = 0 := indicator_of_notMem hxΩ v
    by_cases hxcl : x ∈ closure Ω
    · have hxf : x ∈ frontier Ω := by
        rw [frontier, hΩ.interior_eq]
        exact ⟨hxcl, hxΩ⟩
      have hwx := hwb x hxf
      apply tendsto_iff_norm_sub_tendsto_zero.mpr
      simp only [hvx, sub_zero, Real.norm_eq_abs]
      apply squeeze_zero' (Eventually.of_forall (fun y => abs_nonneg (Ω.indicator v y)))
        (Eventually.of_forall hglobal)
      simpa only [hwx, abs_zero, mul_zero] using
        (tendsto_const_nhds.mul hw.continuousAt.tendsto.abs :
          Tendsto (fun y => B * |w y|) (𝓝 x) (𝓝 (B * |w x|)))
    · apply (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hxcl] with y hy
      exact indicator_of_notMem (fun hyΩ => hy (subset_closure hyΩ)) v

lemma zero_extension_ae_eq {Ω : Set (CoordinateSpace n)} {u v : CoordinateSpace n → ℝ}
    (huv : ∀ᵐ x ∂volume, x ∈ Ω → v x = u x)
    (hu0 : ∀ᵐ x ∂volume, x ∉ Ω → u x = 0) : Ω.indicator v =ᵐ[volume] u := by
  classical
  filter_upwards [huv, hu0] with x hx hz
  by_cases hxΩ : x ∈ Ω
  · rw [indicator_of_mem hxΩ, hx hxΩ]
  · rw [indicator_of_notMem hxΩ, hz hxΩ]

end GaussianTilt.MomentMapLinearDirichlet
