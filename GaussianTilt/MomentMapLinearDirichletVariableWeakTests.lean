import GaussianTilt.MomentMapLinearDirichletVariableWeakEnergyChange
import GaussianTilt.MomentMapLinearDirichletVariableWeakPullbackCore

/-! # Constructing admissible physical tests from compact flat-chart tests -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin
variable {n : ℕ}
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 1000

/-- A compact flat test gives a genuine compact physical test. The cutoff
and its support are constructed, and its gradient agrees with the actual
forward-chart test on the inverse-chart image. -/
theorem exists_physical_chart_test {U V D Ω : Set (CoordinateSpace n)}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hV : IsOpen V) (hDV : D⊆V)
    {F ψ : CoordinateSpace n → CoordinateSpace n} (hF : ContDiff ℝ ∞ F) (hψ : Continuous ψ)
    (hleft : ∀ z∈V, F (ψ z)=z) (hright : ∀ x∈U, F x∈V → ψ (F x)=x)
    (hψU : MapsTo ψ V U) (hψΩ : MapsTo ψ D Ω)
    (τ : smoothCompactCore n) (hτD : tsupport τ.1⊆D) :
    ∃ ξ : smoothCompactCore n, tsupport ξ.1⊆Ω ∧ tsupport ξ.1⊆ψ '' V ∧
      (∀ z∈V, ξ.1 (ψ z)=τ.1 z) ∧
      ∀ z∈V, coordinateGradient ξ.1 (ψ z)=coordinateGradient (τ.1 ∘ F) (ψ z) := by
  let K := ψ '' tsupport τ.1
  have hK : IsCompact K := τ.2.2.image hψ
  have hKU : K⊆U := by rintro _ ⟨z,hz,rfl⟩; exact hψU (hDV (hτD hz))
  obtain ⟨χ,hχU,hχone⟩ := exists_smooth_interior_cutoff hU hUb hK hKU
  let ξ := smoothCompactChartPullback χ hF τ
  have hξsupp : tsupport ξ.1⊆Ω∩ψ '' V := by
    intro x hx
    have hxχ : x∈tsupport χ.1 := tsupport_mul_subset_left hx
    have hxτ : F x∈tsupport τ.1 := tsupport_comp_subset_preimage hF.continuous τ.1 (tsupport_mul_subset_right hx)
    have hFxD := hτD hxτ
    have hFxV := hDV hFxD
    have he := hright x (hχU hxχ) hFxV
    exact ⟨he ▸ hψΩ hFxD,⟨F x,hFxV,he⟩⟩
  have hval : ∀ z∈V, ξ.1 (ψ z)=τ.1 z := by
    intro z hz
    change χ.1 (ψ z)*τ.1 (F (ψ z))=τ.1 z
    rw [hleft z hz]
    by_cases hzs : z∈tsupport τ.1
    · rw [hχone (show ψ z∈K from ⟨z,hzs,rfl⟩)]
      simp
    · rw [image_eq_zero_of_notMem_tsupport hzs,mul_zero]
  refine ⟨ξ,fun x hx=>(hξsupp hx).1,fun x hx=>(hξsupp hx).2,hval,?_⟩
  intro z hz
  have hFz : F (ψ z)∈V := by rwa [hleft z hz]
  have he : ξ.1=ᶠ[𝓝 (ψ z)] τ.1 ∘ F := by
    filter_upwards [hU.mem_nhds (hψU hz),hF.continuous.continuousAt.preimage_mem_nhds (hV.mem_nhds hFz)] with x hxU hxV
    have hh := hval (F x) hxV
    rw [hright x hxU hxV] at hh
    exact hh
  funext i
  change fderiv ℝ ξ.1 (ψ z) (Pi.single i 1)=fderiv ℝ (τ.1 ∘ F) (ψ z) (Pi.single i 1)
  rw [(he.fderiv (𝕜:=ℝ)).self_of_nhds]

end GaussianTilt.MomentMapLinearDirichlet
