import GaussianTilt.MomentMapLinearDirichletTangentialNormalWeakProduct

/-! # Genuine non-normal weak Hessian entries from actual tangential H¹ jets -/
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory Set Filter Matrix
open scoped Topology ContDiff BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapRegularity
variable {n : ℕ}

lemma HasLocalWeakDerivative.congr_ae {U : Set (CoordinateSpace n)}
    {f g f' g' : CoordinateSpace n→ℝ} {i : Fin n}
    (h : HasLocalWeakDerivative U f g i)
    (hf : ∀ᵐ x∂volume,x∈U → f' x=f x)
    (hg : ∀ᵐ x∂volume,x∈U → g' x=g x) : HasLocalWeakDerivative U f' g' i := by
  intro ψ hψ
  have hl : (∫ x,f' x*coordinateDerivative i ψ.1 x)=∫ x,f x*coordinateDerivative i ψ.1 x := by
    apply integral_congr_ae
    filter_upwards [hf] with x hx
    by_cases hxU : x∈U
    · rw [hx hxU]
    · have hz : coordinateDerivative i ψ.1 x=0 :=
        image_eq_zero_of_notMem_tsupport (fun hh=>hxU (hψ (coordinateDerivative_tsupport_subset ψ.1 i hh)))
      rw [hz,mul_zero,mul_zero]
  have hr : (∫ x,g' x*ψ.1 x)=∫ x,g x*ψ.1 x := by
    apply integral_congr_ae
    filter_upwards [hg] with x hx
    by_cases hxU : x∈U
    · rw [hx hxU]
    · rw [image_eq_zero_of_notMem_tsupport (fun hh=>hxU (hψ hh)),mul_zero,mul_zero]
  rw [hl,hr]
  exact h ψ hψ

lemma dirichlet_hasLocalWeakDerivative {Ω U : Set (CoordinateSpace n)}
    (u : dirichletSobolev Ω) (i : Fin n) :
    HasLocalWeakDerivative U (u.1 0) (u.1 i.succ) i := by
  intro ψ _
  have hh := dirichletSobolev_integral_by_parts u i ψ
  linarith

/-- Rows other than the normal row are the actual gradients of the
constructed tangential derivatives. The normal off-diagonal row is
recovered by true weak mixed-partial commutation. -/
def nonNormalHessian (q : Fin n)
    (J : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (x : CoordinateSpace n) (k i : Fin n) : ℝ :=
  if k=q then J x i q else J x k i

lemma continuousOn_nonNormalHessian {U : Set (CoordinateSpace n)} (q : Fin n)
    {J : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hJ : ∀ k i,ContinuousOn (fun x=>J x k i) U) :
    ∀ k i,ContinuousOn (fun x=>nonNormalHessian q J x k i) U := by
  intro k i
  by_cases hk : k=q
  · simpa only [nonNormalHessian,if_pos hk] using hJ i q
  · simpa only [nonNormalHessian,if_neg hk] using hJ k i

/-- Every non-normal second weak derivative is proved from genuine H₀¹
jets and their actual almost-everywhere representatives. No Hessian or
classical derivative of the normal component is supplied. -/
theorem nonNormalHessian_weak_derivatives {Ω Ω' U : Set (CoordinateSpace n)}
    (q : Fin n) (u : dirichletSobolev Ω)
    (W : ∀ k : Fin n,k≠q → dirichletSobolev Ω')
    {G : CoordinateSpace n → CoordinateSpace n}
    {J : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hG : ∀ k,∀ᵐ x∂volume,x∈U → G x k=u.1 k.succ x)
    (hW : ∀ k (hk:k≠q),∀ᵐ x∂volume,x∈U → (W k hk).1 0 x=u.1 k.succ x)
    (hJ : ∀ k (hk:k≠q) i,∀ᵐ x∂volume,x∈U → J x k i=(W k hk).1 i.succ x) :
    ∀ i k, i≠q ∨ k≠q →
      HasLocalWeakDerivative U (fun x=>G x k) (fun x=>nonNormalHessian q J x k i) i := by
  intro i k hik
  by_cases hk : k=q
  · subst k
    have hi : i≠q := hik.resolve_right (not_not.mpr rfl)
    have hraw : HasLocalWeakDerivative U (u.1 q.succ) ((W i hi).1 q.succ) i := by
      intro ψ hψ
      have hh := weak_mixed_partial_commutation u (W i hi) i q (hW i hi) ψ hψ
      linarith
    apply hraw.congr_ae (hG q)
    simpa only [nonNormalHessian,if_pos rfl] using hJ i hi q
  · apply (dirichlet_hasLocalWeakDerivative (U:=U) (W k hk) i).congr_ae
    · filter_upwards [hG k,hW k hk] with x hx hy hxU
      exact (hx hxU).trans (hy hxU).symm
    · simpa only [nonNormalHessian,if_neg hk] using hJ k hk i

end GaussianTilt.MomentMapLinearDirichlet
