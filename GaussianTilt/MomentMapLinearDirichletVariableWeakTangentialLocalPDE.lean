import GaussianTilt.MomentMapLinearDirichletVariableWeakTangentialPDE

/-! # Differentiation of the genuine local weak divergence equation -/
noncomputable section
open Set MeasureTheory Filter Matrix
open scoped Topology ContDiff ENNReal BigOperators
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin
variable {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 1000

lemma weak_matrix_energy_congr_support {K:Set (CoordinateSpace n)}
    {A B:CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hAB:∀ x∈K,∀ i k,A x i k=B x i k)
    (u:Fin n → CoordinateSpace n → ℝ) (φ:Fin n → CoordinateSpace n → ℝ)
    (hφ:∀ i,tsupport (φ i)⊆K) :
    (∫ x,∑ i:Fin n,∑ k:Fin n,A x i k*u k x*φ i x)=
      ∫ x,∑ i:Fin n,∑ k:Fin n,B x i k*u k x*φ i x := by
  apply integral_congr_ae
  apply ae_of_all
  intro x
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  by_cases hx:x∈K
  · rw [hAB x hx i k]
  · rw [image_eq_zero_of_notMem_tsupport (fun hh=>hx (hφ i hh)),mul_zero,mul_zero]

/-- The actual differentiated compact-test divergence equation with only
local smoothness of the fixed coefficients. The unknowns are genuine H¹
jets; mixed weak derivatives commute by their distributional identities.
No classical derivative of u or of the L² scalar forcing is assumed. -/
theorem weak_divergence_differentiated_local {Ω Ω' U:Set (CoordinateSpace n)}
    (hU:IsOpen U) (u:dirichletSobolev Ω) (w:dirichletSobolev Ω') (a:Fin n)
    (hval:∀ᵐ x∂volume,x∈U → w.1 0 x=u.1 a.succ x)
    (A:CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hA:∀ i k,ContDiffOn ℝ ∞ (fun x=>A x i k) U) (f:CoordinateSpace n → ℝ)
    (heq:∀ψ:smoothCompactCore n,tsupport ψ.1⊆U →
      (∫ x,∑ i:Fin n,∑ k:Fin n,A x i k*u.1 k.succ x*coordinateDerivative i ψ.1 x)=∫ x,f x*ψ.1 x)
    (ψ:smoothCompactCore n) (hψ:tsupport ψ.1⊆U) :
    (∫ x,∑ i:Fin n,∑ k:Fin n,A x i k*w.1 k.succ x*coordinateDerivative i ψ.1 x)=
      -(∫ x,f x*coordinateDerivative a ψ.1 x)-
      ∫ x,∑ i:Fin n,∑ k:Fin n,coordinateDerivative a (fun y=>A y i k) x*u.1 k.succ x*coordinateDerivative i ψ.1 x := by
  choose B₀ hBs hBe using fun i k=>
    GaussianTilt.MomentMapRegularity.exists_global_smooth_eq_near_compact_coordinate hU (hA i k) ψ.2.2 hψ
  let B:CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ := fun x i k=>B₀ i k x
  have hBval (x:CoordinateSpace n) (hx:x∈tsupport ψ.1) (i k:Fin n) : B x i k=A x i k :=
    (hBe i k x hx).self_of_nhds
  have hBder (x:CoordinateSpace n) (hx:x∈tsupport ψ.1) (i k:Fin n) :
      coordinateDerivative a (fun y=>B y i k) x=coordinateDerivative a (fun y=>A y i k) x := by
    unfold coordinateDerivative
    rw [((hBe i k x hx).fderiv (𝕜:=ℝ)).self_of_nhds]
  have hs (i:Fin n) : tsupport (coordinateDerivative i ψ.1)⊆tsupport ψ.1 := coordinateDerivative_tsupport_subset ψ.1 i
  have hs2 (i:Fin n) : tsupport (coordinateDerivative i (coordinateDerivative a ψ.1))⊆tsupport ψ.1 :=
    (coordinateDerivative_tsupport_subset (coordinateDerivative a ψ.1) i).trans (hs a)
  have htest := heq (smoothCompactDerivative a ψ) ((hs a).trans hψ)
  have htestB : (∫ x,∑ i:Fin n,∑ k:Fin n,B x i k*u.1 k.succ x*coordinateDerivative i (coordinateDerivative a ψ.1) x)=
      ∫ x,f x*coordinateDerivative a ψ.1 x :=
    (weak_matrix_energy_congr_support hBval (fun k x=>u.1 k.succ x)
      (fun i=>coordinateDerivative i (coordinateDerivative a ψ.1)) hs2).trans htest
  have hh := weak_differentiated_equation_of_test_equation u w a hval B hBs f ψ hψ htestB
  have hleft := weak_matrix_energy_congr_support hBval (fun k x=>w.1 k.succ x) (fun i=>coordinateDerivative i ψ.1) hs
  have hright := weak_matrix_energy_congr_support hBder (fun k x=>u.1 k.succ x) (fun i=>coordinateDerivative i ψ.1) hs
  rw [hleft,hright] at hh
  exact hh

end GaussianTilt.MomentMapLinearDirichlet
