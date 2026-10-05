import GaussianTilt.MomentMapLinearDirichletVariableWeakTests

/-! # The literal weak divergence equation in nonlinear boundary coordinates -/
noncomputable section
open Set MeasureTheory Filter Matrix
open scoped Topology ContDiff ENNReal BigOperators
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin
variable {n : ℕ}
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 1000

lemma coordinateGradient_eq_zero_off_support (τ : CoordinateSpace n → ℝ) {x : CoordinateSpace n}
    (hx : x∉tsupport τ) : coordinateGradient τ x=0 := by
  funext i
  simp [coordinateGradient,coordinateDerivative,fderiv_of_notMem_tsupport ℝ hx]

/-- Genuine weak Laplace energy yields the literal compact-test equation
for the actual L² derivative coordinates. -/
theorem dirichlet_weak_energy_compact_test {Ω : Set (CoordinateSpace n)}
    (u : dirichletSobolev Ω) (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n)))
    (hu : ∀ v : dirichletSobolev Ω, dirichletEnergy Ω u v=inner ℝ f (dirichletValue Ω v))
    (τ : smoothCompactCore n) (hτ : tsupport τ.1⊆Ω) :
    (∫ x, (fun i:Fin n=>u.1 i.succ x) ⬝ᵥ coordinateGradient τ.1 x)=∫ x, f x*τ.1 x := by
  let v := dirichletCoreToSobolev Ω ⟨τ,hτ⟩
  have hh := hu v
  rw [dirichletEnergy_apply] at hh
  change (∑ i, inner ℝ (u.1 i.succ) (smoothCompactToL2 volume (smoothCompactDerivative i τ)))=
    inner ℝ f (smoothCompactToL2 volume τ) at hh
  simp_rw [inner_Lp_smoothCompactToL2] at hh
  change (∑ i, ∫ x, u.1 i.succ x * coordinateDerivative i τ.1 x) = ∫ x, f x * τ.1 x at hh
  have hi (i:Fin n) : Integrable (fun x=>u.1 i.succ x*coordinateDerivative i τ.1 x) :=
    (Lp.memLp (u.1 i.succ)).integrable_mul (smooth_compact_memLp
      (smooth_coordinateDerivative τ.2.1 i) (τ.2.2.fderiv_apply (𝕜:=ℝ) (Pi.single i 1)))
  rw [← integral_finset_sum Finset.univ (fun i _=>hi i)] at hh
  exact hh

/-- A genuine weak Laplace solution transforms into the literal divergence
energy with coefficient |det Dψ| DF DFᵀ and Jacobian-weighted forcing.
All physical tests and their support are constructed. No boundary gradient,
Hessian, or classical regularity of the unknown is assumed. -/
theorem weak_divergence_equation_in_chart {U V D Ω : Set (CoordinateSpace n)}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hV : IsOpen V) (hDV : D⊆V)
    {F ψ : CoordinateSpace n → CoordinateSpace n} (hF : ContDiff ℝ ∞ F) (hψ : ContDiff ℝ ∞ ψ)
    (hleft : ∀ z∈V, F (ψ z)=z) (hright : ∀ x∈U, F x∈V → ψ (F x)=x)
    (hψU : MapsTo ψ V U) (hψΩ : MapsTo ψ D Ω)
    (G : CoordinateSpace n → CoordinateSpace n) (f : CoordinateSpace n → ℝ)
    (hweak : ∀ ξ:smoothCompactCore n, tsupport ξ.1⊆Ω →
      (∫ x, G x ⬝ᵥ coordinateGradient ξ.1 x)=∫ x,f x*ξ.1 x)
    (τ : smoothCompactCore n) (hτD : tsupport τ.1⊆D) :
    (∫ z, weakChartGradient ψ G z ⬝ᵥ (divergenceChartCoefficient F ψ z *ᵥ coordinateGradient τ.1 z))=
      ∫ z, |(fderiv ℝ ψ z).det| *f (ψ z)*τ.1 z := by
  obtain ⟨ξ,hξΩ,hξim,hval,hgrad⟩ := exists_physical_chart_test hU hUb hV hDV hF hψ.continuous
    hleft hright hψU hψΩ τ hτD
  have hinj : InjOn ψ V := by
    intro x hx y hy hxy
    rw [← hleft x hx,← hleft y hy,hxy]
  have him : MeasurableSet (ψ '' V) := measurable_image_of_fderivWithin hV.measurableSet
    (fun x _=>(hψ.differentiable (by simp) x).hasFDerivAt.hasFDerivWithinAt) hinj
  calc
    _ = ∫ z in V, weakChartGradient ψ G z ⬝ᵥ (divergenceChartCoefficient F ψ z *ᵥ coordinateGradient τ.1 z) := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      rw [coordinateGradient_eq_zero_off_support τ.1 (fun hh=>hz (hDV (hτD hh))),Matrix.mulVec_zero,dotProduct_zero]
    _ = ∫ x in ψ '' V, G x ⬝ᵥ coordinateGradient (τ.1 ∘ F) x :=
      chart_energy_change_of_variables hV (hF.differentiable (by simp))
        (hψ.differentiable (by simp)).differentiableOn hleft G (τ.2.1.differentiable (by simp))
    _ = ∫ x in ψ '' V, G x ⬝ᵥ coordinateGradient ξ.1 x := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem him] with x hx
      obtain ⟨z,hz,rfl⟩ := hx
      rw [hgrad z hz]
    _ = ∫ x, G x ⬝ᵥ coordinateGradient ξ.1 x := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [coordinateGradient_eq_zero_off_support ξ.1 (fun hh=>hx (hξim hh)),dotProduct_zero]
    _ = ∫ x,f x*ξ.1 x := hweak ξ hξΩ
    _ = ∫ x in ψ '' V, f x*ξ.1 x := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport (fun hh=>hx (hξim hh)),mul_zero]
    _ = ∫ z in V, |(fderiv ℝ ψ z).det| *f (ψ z)*τ.1 z := by
      rw [integral_image_eq_integral_abs_det_fderiv_smul volume hV.measurableSet
        (fun x _=>(hψ.differentiable (by simp) x).hasFDerivAt.hasFDerivWithinAt) hinj]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hV.measurableSet] with z hz
      rw [hval z hz]
      change |(fderiv ℝ ψ z).det| *(f (ψ z)*τ.1 z)=_
      ring
    _ = _ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      rw [image_eq_zero_of_notMem_tsupport (fun hh=>hz (hDV (hτD hh))),mul_zero]

end GaussianTilt.MomentMapLinearDirichlet
