import GaussianTilt.MomentMapSchauderCutoff
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Honest compact localization of an interior C² equation

A constructed bump is supported strictly inside the original domain.
Multiplying by it gives a globally C² compactly supported function, even
when the original function has no regularity outside the domain. Values
and actual derivatives agree on the smaller open ball.
-/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace GaussianTilt.MomentMapSchauder
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A smooth cutoff can multiply a function known smooth only on an open
set, provided its closed support lies strictly in that set. -/
theorem contDiff_cutoff_mul_of_contDiffOn {u χ : E → ℝ} {U : Set E}
    {k : WithTop ℕ∞} (hU : IsOpen U) (hu : ContDiffOn ℝ k u U)
    (hχ : ContDiff ℝ k χ) (hsupp : tsupport χ ⊆ U) :
    ContDiff ℝ k (fun x => χ x * u x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ U
  · exact hχ.contDiffAt.mul (hu.contDiffAt (hU.mem_nhds hx))
  · have hxnot : x ∉ tsupport χ := fun hs => hx (hsupp hs)
    have he : (fun y => χ y * u y) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hxnot] with y hy
      change χ y = 0 at hy
      rw [hy, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq he

/-- A concrete interior bump with strict support separation. -/
theorem exists_interior_cutoff [FiniteDimensional ℝ E] (x : E) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) :
    ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ Metric.ball x R ∧ (∀ y, 0 ≤ χ y ∧ χ y ≤ 1) ∧
      ∀ y ∈ Metric.closedBall x r, χ y = 1 := by
  let b : ContDiffBump x :=
    { rIn := r, rOut := (r + R) / 2, rIn_pos := hr, rIn_lt_rOut := by linarith }
  refine ⟨b, b.contDiff, b.hasCompactSupport, ?_, ?_, ?_⟩
  · rw [b.tsupport_eq]
    exact Metric.closedBall_subset_ball (by dsimp [b]; linarith)
  · exact fun y => ⟨b.nonneg, b.le_one⟩
  · intro y hy
    exact b.one_of_mem_closedBall hy

lemma cutoff_mul_eventuallyEq {u χ : E → ℝ} {U : Set E} (hU : IsOpen U)
    (hχ : ∀ y ∈ U, χ y = 1) {x : E} (hx : x ∈ U) :
    (fun y => χ y * u y) =ᶠ[𝓝 x] u := by
  filter_upwards [hU.mem_nhds hx] with y hy
  rw [hχ y hy, one_mul]

/-- Values and both actual Fréchet derivatives are unchanged on the
interior region where the cutoff is identically one. -/
theorem cutoff_mul_derivatives_eq {u χ : E → ℝ} {U : Set E} (hU : IsOpen U)
    (hχ : ∀ y ∈ U, χ y = 1) {x : E} (hx : x ∈ U) :
    χ x * u x = u x ∧ fderiv ℝ (fun y => χ y * u y) x = fderiv ℝ u x ∧
      fderiv ℝ (fderiv ℝ (fun y => χ y * u y)) x = fderiv ℝ (fderiv ℝ u) x := by
  have he := cutoff_mul_eventuallyEq (u := u) hU hχ hx
  exact ⟨by rw [hχ x hx, one_mul], he.fderiv_eq, he.fderiv.fderiv_eq⟩

/-- Every genuinely local C² function admits a constructed global C²
compact localization agreeing with its first two derivatives on a smaller
ball. No extension or boundary regularity premise is hidden here. -/
theorem exists_compact_C2_localization [FiniteDimensional ℝ E]
    {u : E → ℝ} {x : E} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hu : ContDiffOn ℝ 2 u (Metric.ball x R)) :
    ∃ v : E → ℝ, ContDiff ℝ 2 v ∧ HasCompactSupport v ∧
      ∀ y ∈ Metric.ball x r, v y = u y ∧ fderiv ℝ v y = fderiv ℝ u y ∧
        fderiv ℝ (fderiv ℝ v) y = fderiv ℝ (fderiv ℝ u) y := by
  obtain ⟨χ, hχ, hχc, hsupp, _, hχone⟩ := exists_interior_cutoff x hr hrR
  refine ⟨fun y => χ y * u y,
    contDiff_cutoff_mul_of_contDiffOn Metric.isOpen_ball hu (contDiff_infty.mp hχ 2) hsupp,
    hχc.mul_right, ?_⟩
  intro y hy
  exact cutoff_mul_derivatives_eq Metric.isOpen_ball
    (fun z hz => hχone z (Metric.ball_subset_closedBall hz)) hy

end GaussianTilt.MomentMapSchauder
