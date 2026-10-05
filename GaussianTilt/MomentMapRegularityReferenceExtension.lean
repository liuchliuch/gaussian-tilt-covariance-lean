import GaussianTilt.MomentMapRegularityGeometry
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! # Actual smooth extension near a compact interior set

A smooth cutoff equals one near the compact set and vanishes near the
complement of the actual smooth domain. Multiplication supplies a genuine
global smooth extension there, without any boundary extension assumption.
-/
noncomputable section
open Set Filter
open scoped Topology ContDiff Manifold
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

/-- Smoothness on an open domain supplies a globally smooth representative
agreeing on a neighborhood of every point of a chosen compact subset. -/
theorem exists_global_smooth_eq_near_compact {u : E n → ℝ} {U K : Set (E n)}
    (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ v : E n → ℝ, ContDiff ℝ ∞ v ∧ ∀ x ∈ K, v =ᶠ[𝓝 x] u := by
  obtain ⟨χ,hχ0,hχ1,hχb⟩ := exists_smooth_zero_one_nhds_of_isClosed
    𝓘(ℝ, E n) hU.isClosed_compl hK.isClosed
    (disjoint_left.mpr (fun x hxU hxK => hxU (hKU hxK)))
  let v := fun x => χ x*u x
  have hχ : ContDiff ℝ ∞ (χ : E n → ℝ) := χ.contMDiff.contDiff
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

/-- The finite-order version, with no higher regularity premise. -/
theorem exists_global_contDiff_eq_near_compact (m : ℕ) {u : E n → ℝ} {U K : Set (E n)}
    (hU : IsOpen U) (hu : ContDiffOn ℝ m u U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ v : E n → ℝ, ContDiff ℝ m v ∧ ∀ x ∈ K, v =ᶠ[𝓝 x] u := by
  obtain ⟨χ,hχ0,hχ1,hχb⟩ := exists_smooth_zero_one_nhds_of_isClosed
    𝓘(ℝ, E n) hU.isClosed_compl hK.isClosed
    (disjoint_left.mpr (fun x hxU hxK => hxU (hKU hxK)))
  let v := fun x => χ x*u x
  have hχ : ContDiff ℝ m (χ : E n → ℝ) := contDiff_infty.mp χ.contMDiff.contDiff m
  have hv : ContDiff ℝ m v := by
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

end GaussianTilt.MomentMapRegularity
