import GaussianTilt.MomentMapLinearDirichletTangentialNormalRecovery

/-! # True closed-boundary C² regularity from recovered continuous fields -/
noncomputable section
set_option maxHeartbeats 2500000
open MeasureTheory Set Filter Matrix
open scoped Topology ContDiff BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapRegularity GaussianTilt.HolderSpace
variable {n : ℕ}

/-- True interior coordinate derivatives with continuous closed-body
fields extend to genuine within-derivatives and closed-domain C². -/
theorem contDiffOn_two_closed_of_coordinate_interior_fields
    {S : Set (CoordinateSpace n)} (hS : Convex ℝ S) (hSc : IsClosed S) (hint : (interior S).Nonempty)
    {v : CoordinateSpace n→ℝ} {G : CoordinateSpace n → CoordinateSpace n}
    {H : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hv : ContinuousOn v S) (hG : ∀ k,ContinuousOn (fun x=>G x k) S)
    (hH : ∀ k i,ContinuousOn (fun x=>H x k i) S)
    (hDv : ∀ x∈interior S,HasFDerivAt v (coordinateCovector (G x)) x)
    (hDG : ∀ k x,x∈interior S → HasFDerivAt (fun y=>G y k) (coordinateCovector (H x k)) x) :
    ContDiffOn ℝ 2 v S ∧
      (∀ x∈S,HasFDerivWithinAt v (coordinateCovector (G x)) S x) ∧
      ∀ k x,x∈S → HasFDerivWithinAt (fun y=>G y k) (coordinateCovector (H x k)) S x := by
  have hDvc : ContinuousOn (fun x=>coordinateCovector (G x)) S :=
    (coordinateCovector (n:=n)).continuous.comp_continuousOn (continuousOn_pi.mpr hG)
  have hDGc (k : Fin n) : ContinuousOn (fun x=>coordinateCovector (H x k)) S :=
    (coordinateCovector (n:=n)).continuous.comp_continuousOn (continuousOn_pi.mpr (hH k))
  have hDvw (x : CoordinateSpace n) (hx : x∈S) : HasFDerivWithinAt v (coordinateCovector (G x)) S x :=
    hasFDerivWithinAt_of_continuous_interior_field hS hSc hint hv hDvc hDv hx
  have hDGw (k : Fin n) (x : CoordinateSpace n) (hx : x∈S) :
      HasFDerivWithinAt (fun y=>G y k) (coordinateCovector (H x k)) S x :=
    hasFDerivWithinAt_of_continuous_interior_field hS hSc hint (hG k) (hDGc k) (hDG k) hx
  have hUD : UniqueDiffOn ℝ S := uniqueDiffOn_convex hS hint
  have hg1 : ContDiffOn ℝ 1 G S := by
    apply contDiffOn_pi.mpr
    intro k
    rw [show (1:WithTop ℕ∞)=0+1 from rfl,contDiffOn_succ_iff_fderivWithin hUD]
    refine ⟨fun x hx=>(hDGw k x hx).differentiableWithinAt,by simp,?_⟩
    rw [contDiffOn_zero]
    exact (hDGc k).congr (fun x hx=>(hDGw k x hx).fderivWithin (hUD x hx))
  refine ⟨?_,hDvw,hDGw⟩
  rw [show (2:WithTop ℕ∞)=1+1 from rfl,contDiffOn_succ_iff_fderivWithin hUD]
  refine ⟨fun x hx=>(hDvw x hx).differentiableWithinAt,by simp,?_⟩
  exact ((coordinateCovector (n:=n)).contDiff.comp_contDiffOn hg1).congr
    (fun x hx=>(hDvw x hx).fderivWithin (hUD x hx))

/-- The normal weak-flux recovery closes the genuine C² boundary step
when the two weak-gradient representative passes extend continuously to
the convex closed patch. No smooth extension of the unknown is used. -/
theorem contDiffOn_two_closed_of_tangential_weak_gradient_representatives
    {Ω Ω' S : Set (CoordinateSpace n)} (hS : Convex ℝ S) (hSc : IsClosed S) (hint : (interior S).Nonempty)
    (q : Fin n) (u : dirichletSobolev Ω)
    (W : ∀ k : Fin n,k≠q → dirichletSobolev Ω')
    {v : CoordinateSpace n→ℝ} {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    {G : CoordinateSpace n → CoordinateSpace n}
    {J : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {f : CoordinateSpace n→ℝ}
    (hv : ContinuousOn v S) (hval : ∀ᵐ x∂volume,x∈interior S → v x=u.1 0 x)
    (hA : ∀ i k,ContDiffOn ℝ ∞ (fun x=>A x i k) (interior S))
    (hAc : ∀ i k,ContinuousOn (fun x=>A x i k) S)
    (hADc : ∀ i k l,ContinuousOn (coordinateDerivative l (fun x=>A x i k)) S)
    (hGc : ∀ k,ContinuousOn (fun x=>G x k) S)
    (hJc : ∀ k i,ContinuousOn (fun x=>J x k i) S) (hf : ContinuousOn f S)
    (hG : ∀ k,∀ᵐ x∂volume,x∈interior S → G x k=u.1 k.succ x)
    (hW : ∀ k (hk:k≠q),∀ᵐ x∂volume,x∈interior S → (W k hk).1 0 x=u.1 k.succ x)
    (hJ : ∀ k (hk:k≠q) i,∀ᵐ x∂volume,x∈interior S → J x k i=(W k hk).1 i.succ x)
    (hweak : ∀ ψ : smoothCompactCore n,tsupport ψ.1⊆interior S →
      (∫ x,∑ i : Fin n,∑ k : Fin n,A x i k*u.1 k.succ x*coordinateDerivative i ψ.1 x)=∫ x,f x*ψ.1 x)
    (hneq : ∀ x∈S,A x q q≠0) :
    ContDiffOn ℝ 2 v S ∧
      (∀ x∈S,HasFDerivWithinAt v (coordinateCovector (G x)) S x) ∧
      ∀ k x,x∈S → HasFDerivWithinAt (fun y=>G y k) (coordinateCovector (recoveredWeakHessian q A G J f x k)) S x := by
  obtain ⟨_,hDv,hDG⟩ := contDiffOn_two_of_tangential_weak_gradient_representatives isOpen_interior q u W
    (hv.mono interior_subset) hval hA (fun k=>(hGc k).mono interior_subset)
    (fun k i=>(hJc k i).mono interior_subset) (hf.mono interior_subset) hG hW hJ hweak
    (fun x hx=>hneq x (interior_subset hx))
  exact contDiffOn_two_closed_of_coordinate_interior_fields hS hSc hint hv hGc
    (continuousOn_recoveredWeakHessian q hAc hADc hGc hJc hf hneq) hDv hDG

end GaussianTilt.MomentMapLinearDirichlet
