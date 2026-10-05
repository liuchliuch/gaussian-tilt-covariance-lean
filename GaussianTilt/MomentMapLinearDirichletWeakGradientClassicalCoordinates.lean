import GaussianTilt.MomentMapLinearDirichletWeakGradientClassical
import GaussianTilt.MomentMapLinearDirichletH1FlatEquation
import GaussianTilt.MomentMapClassicalDirichletSolutionCompactness

/-! # Raw-coordinate continuous weak gradients are actual derivatives -/
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory Set Filter
open scoped Topology ContDiff BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapRegularity
variable {n : ℕ}

/-- Exact volume-preserving coordinate transport of the continuous weak
covector theorem. No weak/classical derivative identification is assumed. -/
theorem hasFDerivAt_of_continuous_coordinate_weak_gradient
    {Ω : Set (CoordinateSpace n)} (hΩ : IsOpen Ω) {u : CoordinateSpace n→ℝ}
    {D : CoordinateSpace n → CoordinateSpace n→L[ℝ]ℝ}
    (hu : ContinuousOn u Ω) (hD : ContinuousOn D Ω)
    (hweak : ∀ i : Fin n, ∀ ψ : smoothCompactCore n, tsupport ψ.1⊆Ω →
      (∫ y, u y*coordinateDerivative i ψ.1 y)= -(∫ y,D y (Pi.single i 1)*ψ.1 y))
    {x : CoordinateSpace n} (hx : x∈Ω) : HasFDerivAt u (D x) x := by
  let e := dirichletCoordinateEquiv n
  let v := u ∘ e
  let E := fun y : KernelSpace n=>(D (e y)).comp e.toContinuousLinearMap
  have hO : IsOpen (e ⁻¹' Ω) := hΩ.preimage e.continuous
  have hv : ContinuousOn v (e ⁻¹' Ω) := hu.comp e.continuous.continuousOn (fun _ hy=>hy)
  have hE : ContinuousOn E (e ⁻¹' Ω) :=
    (hD.comp e.continuous.continuousOn (fun _ hy=>hy)).clm_comp continuousOn_const
  have hw : ∀ i : Fin n, ∀ ψ : KernelSpace n→ℝ,
      ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ⊆e ⁻¹' Ω →
      (∫ y,v y*kernelDirectionalDerivative (EuclideanSpace.basisFun (Fin n) ℝ i) ψ y)=
        -(∫ y,E y (EuclideanSpace.basisFun (Fin n) ℝ i)*ψ y) := by
    intro i ψ hψ hψc hψs
    let g : smoothCompactCore n := ⟨ψ ∘ e.symm,hψ.comp e.symm.contDiff,hψc.comp_homeomorph e.symm.toHomeomorph⟩
    have hgs : tsupport g.1⊆Ω := by
      intro z hz
      have hmem := hψs (tsupport_comp_dirichletCoordinateEquiv_symm hz)
      simpa only [mem_preimage,ContinuousLinearEquiv.apply_symm_apply] using hmem
    have hh := hweak i g hgs
    have hμ : MeasurePreserving e volume volume := PiLp.volume_preserving_ofLp (Fin n)
    rw [← hμ.integral_comp e.toHomeomorph.measurableEmbedding (fun y=>u y*coordinateDerivative i g.1 y),
      ← hμ.integral_comp e.toHomeomorph.measurableEmbedding (fun y=>D y (Pi.single i 1)*g.1 y)] at hh
    have hei : e (EuclideanSpace.basisFun (Fin n) ℝ i)=(Pi.single i 1 : CoordinateSpace n) := by
      rw [EuclideanSpace.basisFun_apply]
      rfl
    simpa only [g,e,coordinateDerivative_toLp_any,Function.comp_apply,ContinuousLinearEquiv.symm_apply_apply,
      E,v,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,hei] using hh
  have hd := hasFDerivAt_of_continuous_weak_gradient hO hv hE hw
    (show e.symm x∈e ⁻¹' Ω by simpa only [mem_preimage,ContinuousLinearEquiv.apply_symm_apply] using hx)
  have hh := hd.comp x e.symm.hasFDerivAt
  have hfun : v ∘ e.symm=u := by funext z; simp only [v,Function.comp_apply,e.apply_symm_apply]
  have hlin : (E (e.symm x)).comp e.symm.toContinuousLinearMap=D x := by
    ext z
    simp only [E,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,e.apply_symm_apply]
  simpa only [hfun,hlin] using hh

theorem contDiffOn_one_of_continuous_coordinate_weak_gradient
    {Ω : Set (CoordinateSpace n)} (hΩ : IsOpen Ω) {u : CoordinateSpace n→ℝ}
    {D : CoordinateSpace n → CoordinateSpace n→L[ℝ]ℝ}
    (hu : ContinuousOn u Ω) (hD : ContinuousOn D Ω)
    (hweak : ∀ i : Fin n, ∀ ψ : smoothCompactCore n, tsupport ψ.1⊆Ω →
      (∫ y,u y*coordinateDerivative i ψ.1 y)= -(∫ y,D y (Pi.single i 1)*ψ.1 y)) :
    ContDiffOn ℝ 1 u Ω := by
  have hd (x : CoordinateSpace n) (hx : x∈Ω) :=
    hasFDerivAt_of_continuous_coordinate_weak_gradient hΩ hu hD hweak hx
  rw [show (1:WithTop ℕ∞)=0+1 from rfl,contDiffOn_succ_iff_fderiv_of_isOpen hΩ]
  refine ⟨fun x hx=>(hd x hx).differentiableAt.differentiableWithinAt,by simp,?_⟩
  rw [contDiffOn_zero]
  exact hD.congr (fun x hx=>(hd x hx).fderiv)

lemma coordinateCovector_single (g : CoordinateSpace n) (i : Fin n) :
    coordinateCovector g (Pi.single i 1)=g i := by
  classical
  rw [coordinateCovector_apply]
  simp [Pi.single_apply]

theorem contDiffOn_one_of_continuous_coordinate_weak_components
    {Ω : Set (CoordinateSpace n)} (hΩ : IsOpen Ω) {u : CoordinateSpace n→ℝ}
    {G : CoordinateSpace n → CoordinateSpace n}
    (hu : ContinuousOn u Ω) (hG : ContinuousOn G Ω)
    (hweak : ∀ i : Fin n, ∀ ψ : smoothCompactCore n, tsupport ψ.1⊆Ω →
      (∫ y,u y*coordinateDerivative i ψ.1 y)= -(∫ y,G y i*ψ.1 y)) :
    ContDiffOn ℝ 1 u Ω ∧ ∀ x∈Ω, HasFDerivAt u (coordinateCovector (G x)) x := by
  have hD := (coordinateCovector (n:=n)).continuous.comp_continuousOn hG
  have hw : ∀ i : Fin n, ∀ ψ : smoothCompactCore n, tsupport ψ.1⊆Ω →
      (∫ y,u y*coordinateDerivative i ψ.1 y)= -(∫ y,coordinateCovector (G y) (Pi.single i 1)*ψ.1 y) := by
    simpa only [coordinateCovector_single] using hweak
  exact ⟨contDiffOn_one_of_continuous_coordinate_weak_gradient hΩ hu hD hw,
    fun x hx=>hasFDerivAt_of_continuous_coordinate_weak_gradient hΩ hu hD hw hx⟩

end GaussianTilt.MomentMapLinearDirichlet
