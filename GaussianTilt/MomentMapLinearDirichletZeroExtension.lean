import GaussianTilt.MomentMapLinearDirichletDistribution

/-!
# Actual zero exterior values of the constructed Dirichlet solution

Orthogonality against exterior-supported L² functions is closed in the
Sobolev-jet topology. Testing against the actual masked value proves that
all elements of H₀¹ vanish outside the domain almost everywhere. No trace
or boundary-value theorem is assumed.
-/
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin
variable {n : ℕ}

lemma dirichletValue_orthogonal_exterior {Ω : Set (CoordinateSpace n)}
    (u : dirichletSobolev Ω) (g : Lp ℝ 2 (volume : Measure (CoordinateSpace n)))
    (hg : ∀ᵐ x ∂volume, x ∈ Ω → g x = 0) : inner ℝ (dirichletValue Ω u) g = 0 := by
  let μ : Measure (CoordinateSpace n) := volume
  have hclosed : IsClosed {v : SobolevJet μ | inner ℝ (v 0) g = 0} :=
    isClosed_eq ((PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin (n + 1) => Lp ℝ 2 μ) 0).continuous.inner continuous_const)
      continuous_const
  have hcore : (LinearMap.range (dirichletJet Ω) : Set (SobolevJet μ)) ⊆
      {v | inner ℝ (v 0) g = 0} := by
    rintro _ ⟨f, rfl⟩
    change inner ℝ (smoothCompactToL2 volume f.1) g = 0
    rw [real_inner_comm, inner_Lp_smoothCompactToL2]
    apply integral_eq_zero_of_ae
    filter_upwards [hg] with x hx
    by_cases hxΩ : x ∈ Ω
    · rw [hx hxΩ, zero_mul]
      rfl
    · have hzero : f.1.1 x = 0 := image_eq_zero_of_notMem_tsupport (fun hh => hxΩ (f.2 hh))
      rw [hzero, mul_zero]
      rfl
  exact (closure_minimal hcore hclosed) u.2

/-- Every value in the actual Dirichlet Sobolev completion is zero outside
its domain. The proof uses an actual L² indicator test, not an assumed trace. -/
theorem dirichletValue_ae_zero_outside {Ω : Set (CoordinateSpace n)} (hΩ : MeasurableSet Ω)
    (u : dirichletSobolev Ω) : ∀ᵐ x ∂volume, x ∉ Ω → (dirichletValue Ω u) x = 0 := by
  classical
  let U := dirichletValue Ω u
  let F := Ωᶜ.indicator (fun x => U x)
  have hF : MemLp F 2 volume := (Lp.memLp U).indicator hΩ.compl
  let G : Lp ℝ 2 (volume : Measure (CoordinateSpace n)) := hF.toLp F
  have hG : G =ᵐ[volume] F := hF.coeFn_toLp
  have hGin : ∀ᵐ x ∂volume, x ∈ Ω → G x = 0 := by
    filter_upwards [hG] with x hx hxΩ
    rw [hx]
    exact indicator_of_notMem (by simpa using hxΩ) _
  have horth : inner ℝ U G = 0 := dirichletValue_orthogonal_exterior u G hGin
  have hGG : inner ℝ G G = inner ℝ U G := by
    rw [L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hG] with x hx
    by_cases hxΩ : x ∈ Ω
    · have hx0 : G x = 0 := by rw [hx]; exact indicator_of_notMem (by simpa using hxΩ) _
      simp [hx0]
    · have hxU : G x = U x := by rw [hx]; exact indicator_of_mem hxΩ _
      rw [hxU]
  have hzero : G = 0 := inner_self_eq_zero.mp (hGG.trans horth)
  filter_upwards [hG, Lp.coeFn_zero (E := ℝ) (p := 2) (μ := (volume : Measure (CoordinateSpace n)))] with x hx hz hxΩ
  have hxU : G x = U x := by rw [hx]; exact indicator_of_mem hxΩ _
  have hx0 : G x = 0 := by rw [hzero]; exact hz
  exact hxU.symm.trans hx0

/-- In particular, the constructed weak solution has actual zero exterior
values in its L² representative. -/
theorem weakDirichletLaplaceSolution_ae_zero_outside {Ω : Set (CoordinateSpace n)}
    (hΩm : MeasurableSet Ω) (i : Fin n) {R : ℝ} (hR : 0 ≤ R)
    (hΩ : ∀ x ∈ Ω, |x i| ≤ R) (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n))) :
    ∀ᵐ x ∂volume, x ∉ Ω →
      (dirichletValue Ω (weakDirichletLaplaceSolution i hR hΩ f)) x = 0 :=
  dirichletValue_ae_zero_outside hΩm _

end GaussianTilt.MomentMapLinearDirichlet
