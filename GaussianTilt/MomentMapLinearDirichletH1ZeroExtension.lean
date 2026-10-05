import GaussianTilt.MomentMapLinearDirichletZeroExtension
import GaussianTilt.MomentMapLinearDirichletLocalization

/-! # The genuine zero-exterior full Sobolev jet and domain inclusion -/
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory Set Filter
open scoped Topology ContDiff BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin
variable {n : ℕ}

lemma dirichletGradient_orthogonal_exterior {Ω : Set (CoordinateSpace n)}
    (u : dirichletSobolev Ω) (i : Fin n)
    (g : Lp ℝ 2 (volume : Measure (CoordinateSpace n)))
    (hg : ∀ᵐ x ∂volume, x ∈ Ω → g x=0) : inner ℝ (u.1 i.succ) g=0 := by
  let μ : Measure (CoordinateSpace n) := volume
  have hclosed : IsClosed {v : SobolevJet μ | inner ℝ (v i.succ) g=0} :=
    isClosed_eq ((PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin (n+1) => Lp ℝ 2 μ) i.succ).continuous.inner continuous_const)
      continuous_const
  have hcore : (LinearMap.range (dirichletJet Ω) : Set (SobolevJet μ)) ⊆
      {v | inner ℝ (v i.succ) g=0} := by
    rintro _ ⟨f,rfl⟩
    change inner ℝ (smoothCompactToL2 volume (smoothCompactDerivative i f.1)) g=0
    rw [real_inner_comm,inner_Lp_smoothCompactToL2]
    apply integral_eq_zero_of_ae
    filter_upwards [hg] with x hx
    by_cases hxΩ : x ∈ Ω
    · rw [hx hxΩ,zero_mul]
      rfl
    · have hxout : x ∉ tsupport f.1.1 := fun hh => hxΩ (f.2 hh)
      have hz : coordinateDerivative i f.1.1 x=0 := by
        simp [coordinateDerivative,fderiv_of_notMem_tsupport ℝ hxout]
      change g x*coordinateDerivative i f.1.1 x=0
      rw [hz,mul_zero]
  exact closure_minimal hcore hclosed u.2

/-- Every weak gradient coordinate, as well as the value coordinate, has
the actual zero extension furnished by the closure of interior tests. -/
theorem dirichletGradient_ae_zero_outside {Ω : Set (CoordinateSpace n)} (hΩ : MeasurableSet Ω)
    (u : dirichletSobolev Ω) (i : Fin n) : ∀ᵐ x ∂volume, x ∉ Ω → u.1 i.succ x=0 := by
  classical
  let U := u.1 i.succ
  let F := Ωᶜ.indicator (fun x => U x)
  have hF : MemLp F 2 volume := (Lp.memLp U).indicator hΩ.compl
  let G : Lp ℝ 2 (volume : Measure (CoordinateSpace n)) := hF.toLp F
  have hG : G =ᵐ[volume] F := hF.coeFn_toLp
  have hGin : ∀ᵐ x ∂volume, x ∈ Ω → G x=0 := by
    filter_upwards [hG] with x hx hxΩ
    rw [hx]
    exact indicator_of_notMem (by simpa using hxΩ) _
  have horth : inner ℝ U G=0 := dirichletGradient_orthogonal_exterior u i G hGin
  have hGG : inner ℝ G G=inner ℝ U G := by
    rw [L2.inner_def,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hG] with x hx
    by_cases hxΩ : x ∈ Ω
    · have hx0 : G x=0 := by rw [hx]; exact indicator_of_notMem (by simpa using hxΩ) _
      simp [hx0]
    · have hxU : G x=U x := by rw [hx]; exact indicator_of_mem hxΩ _
      rw [hxU]
  have hzero : G=0 := inner_self_eq_zero.mp (hGG.trans horth)
  filter_upwards [hG,Lp.coeFn_zero (E := ℝ) (p := 2) (μ := (volume : Measure (CoordinateSpace n)))]
    with x hx hz hxΩ
  have hxU : G x=U x := by rw [hx]; exact indicator_of_mem hxΩ _
  have hx0 : G x=0 := by rw [hzero]; exact hz
  exact hxU.symm.trans hx0

/-- The genuine replacement retains the outer zero-flat-trace class. -/
lemma sub_dirichletSobolev_mem_outer {Ω U : Set (CoordinateSpace n)} (hΩU : Ω ⊆ U)
    (u : dirichletSobolev U) (w : dirichletSobolev Ω) :
    u.1-w.1 ∈ dirichletSobolev U :=
  (dirichletSobolev U).sub_mem u.2 (dirichletSobolev_mono hΩU w.2)

end GaussianTilt.MomentMapLinearDirichlet
