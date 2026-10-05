import GaussianTilt.PaperResults

/-! # The exact supremum conclusion from the original upper and lower statements -/
noncomputable section
open MeasureTheory Set
open scoped Matrix.Norms.L2Operator
namespace GaussianTilt.Reference

/-- The optimal two-sided scale follows for the actual supremum over isotropic
convex bodies, with nonemptiness and boundedness both proved from the original
upper and lower results. This is an assembly implication, not a substitute for
proving either bound. -/
theorem sharpScale_of_upper_lower (hu : UpperBound) (hl : LowerBound) : SharpScale := by
  obtain ⟨C, hC, hupper⟩ := hu
  obtain ⟨c, hc, n₀, hlower⟩ := hl
  refine ⟨c, C, hc, hC, n₀, ?_⟩
  intro n hn
  let S : Set ℝ := {v | ∃ K : Set (Space n), ∃ t : ℝ,
    convexBody K ∧ isotropic (uniform K) ∧ 0 < t ∧
      v = ‖covariance (gaussianTilt (uniform K) t)‖}
  obtain ⟨K, t, hK, hunc, hiso, ht, hcov⟩ := hlower n hn
  have hmem : ‖covariance (gaussianTilt (uniform K) t)‖ ∈ S :=
    ⟨K, t, hK, hiso, ht, rfl⟩
  have hsup (v : ℝ) (hv : v ∈ S) : v ≤ C * (n : ℝ) ^ (2 / 5 : ℝ) := by
    obtain ⟨L, u, hL, hLiso, hu, rfl⟩ := hv
    exact hupper n (uniform L) (uniform_probability hL) (uniform_compactlySupported hL)
      hLiso (uniform_logconcave hL) u hu.le
  have hbounded : BddAbove S := ⟨C * (n : ℝ) ^ (2 / 5 : ℝ), hsup⟩
  change c * (n : ℝ) ^ (2 / 5 : ℝ) ≤ sSup S ∧ sSup S ≤ C * (n : ℝ) ^ (2 / 5 : ℝ)
  exact ⟨hcov.trans (le_csSup hbounded hmem), csSup_le ⟨_, hmem⟩ hsup⟩

end GaussianTilt.Reference
