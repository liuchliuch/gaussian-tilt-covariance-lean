import GaussianTilt.MomentMapSchauderBoundaryVariableFreezing
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! # The true weak equation of a local classical boundary solution -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option maxHeartbeats 2200000
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff Manifold
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapLinearDirichlet
variable {n : ℕ}

/-- Smooth compact localization on an arbitrary compact subset of an open
Euclidean domain. Agreement is on a neighborhood, so all actual jets agree. -/
theorem exists_smooth_compact_cutoff_neighborhood {K U : Set (KernelSpace n)}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : KernelSpace n → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧
      ∀ x ∈ K, χ =ᶠ[𝓝 x] (fun _ => 1) := by
  obtain ⟨δ,hδ,hsub⟩ := hK.exists_cthickening_subset_open hU hKU
  obtain ⟨χ,hχ,_,hs,hone⟩ := exists_msmooth_support_eq_eq_one_iff (𝓘(ℝ,KernelSpace n))
    (isOpen_thickening : IsOpen (thickening δ K))
    (isClosed_cthickening : IsClosed (cthickening (δ/2) K))
    (cthickening_subset_thickening' hδ (by linarith) K)
  have hts : tsupport χ ⊆ cthickening δ K := by
    rw [tsupport,hs]
    exact closure_thickening_subset_cthickening δ K
  refine ⟨χ,hχ.contDiff,(hK.cthickening).of_isClosed_subset (isClosed_tsupport _) hts,hts.trans hsub,?_⟩
  intro x hx
  have hn : thickening (δ/2) K ∈ 𝓝 x := isOpen_thickening.mem_nhds (self_subset_thickening (by positivity) K hx)
  filter_upwards [hn] with y hy
  exact (hone y).mp (thickening_subset_cthickening (δ/2) K hy)

/-- The classical second Green identity requires C² regularity only on
the open set containing the compact test support. -/
theorem integral_local_kernelLaplacian_swap {U : Set (KernelSpace n)} (hU : IsOpen U)
    {u ψ : KernelSpace n → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (hψ : ContDiff ℝ 2 ψ) (hψs : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ U) :
    (∫ x, u x*kernelLaplacian ψ x)=∫ x, ψ x*kernelLaplacian u x := by
  obtain ⟨χ,hχ,hχs,hχU,hone⟩ := exists_smooth_compact_cutoff_neighborhood hψs hU hψU
  let v := fun x => χ x*u x
  have hv : ContDiff ℝ 2 v := contDiff_cutoff_mul_of_contDiffOn hU hu (contDiff_infty.mp hχ 2) hχU
  have hve : ∀ x ∈ tsupport ψ, v =ᶠ[𝓝 x] u := by
    intro x hx
    filter_upwards [hone x hx] with y hy
    change χ y*u y=u y
    rw [hy,one_mul]
  have hgreen := integral_mul_kernelLaplacian_swap hψ hv hψs
  calc
    _ = ∫ x, kernelLaplacian ψ x*v x := by
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : x ∈ tsupport ψ
      · rw [(hve x hx).self_of_nhds,mul_comm]
      · have hh : kernelLaplacian ψ x=0 := by
          have he : ψ =ᶠ[𝓝 x] (fun _ => (0:ℝ)) := notMem_tsupport_iff_eventuallyEq.mp hx
          rw [kernelLaplacian_congr_nhds he]
          simp [kernelLaplacian,directionalHessian]
        rw [hh,mul_zero,zero_mul]
    _ = ∫ x, ψ x*kernelLaplacian v x := hgreen.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : x ∈ tsupport ψ
      · rw [kernelLaplacian_congr_nhds (hve x hx)]
      · rw [image_eq_zero_of_notMem_tsupport hx,zero_mul,zero_mul]

/-- An actual C² solution with the concrete zero-extension and growth
properties satisfies the literal compact-test equation used by the proved
flat-boundary Schauder theorem. -/
theorem flatWeakPoisson_of_classical {j : Fin n} {u g : KernelSpace n → ℝ}
    (huL2 : MemLp u 2 volume) (hu0 : ∀ x, x j ≤ 0 → u x=0)
    (hu : ContDiffOn ℝ 2 u (flatUpperBall j 2))
    (hgrowth : ∃ A : ℝ, 0 ≤ A ∧ ∀ x ∈ Metric.ball (0 : KernelSpace n) 2, |u x| ≤ A*|x j|)
    (heq : ∀ x ∈ flatUpperBall j 2, kernelLaplacian u x= -g x) :
    FlatWeakPoisson j u g := by
  refine ⟨huL2,hu0,hu.continuousOn,hgrowth,?_⟩
  intro ψ hψ hψs hψU
  rw [integral_local_kernelLaplacian_swap (isOpen_flatUpperBall j 2) hu (contDiff_infty.mp hψ 2) hψs hψU]
  have he : (∫ x, ψ x*kernelLaplacian u x)=∫ x, -(g x*ψ x) := by
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x ∈ tsupport ψ
    · rw [heq x (hψU hx)]
      ring
    · rw [image_eq_zero_of_notMem_tsupport hx,zero_mul,mul_zero,neg_zero]
  rw [he,integral_neg]

end GaussianTilt.MomentMapSchauder
