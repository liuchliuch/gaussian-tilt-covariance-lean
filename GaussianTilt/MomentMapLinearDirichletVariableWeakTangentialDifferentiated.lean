import GaussianTilt.MomentMapLinearDirichletVariableWeakTangentialLoad

/-! # Actual mixed weak derivatives and differentiated compact-test equations -/
noncomputable section
open Set MeasureTheory Filter Matrix
open scoped Topology ContDiff ENNReal BigOperators
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin
variable {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 1000

lemma dirichletSobolev_integral_by_parts {Ω:Set (CoordinateSpace n)}
    (u:dirichletSobolev Ω) (i:Fin n) (g:smoothCompactCore n) :
    (∫ x,u.1 i.succ x*g.1 x)= -(∫ x,u.1 0 x*coordinateDerivative i g.1 x) := by
  have hh := dirichletSobolev_integration_by_parts u i g
  simpa only [inner_Lp_smoothCompactToL2] using hh

/-- The newly constructed weak tangential derivative has the genuine
commuting mixed weak derivatives, locally on the region of value agreement. -/
theorem weak_mixed_partial_commutation {Ω Ω' U:Set (CoordinateSpace n)}
    (u:dirichletSobolev Ω) (w:dirichletSobolev Ω') (a k:Fin n)
    (hval:∀ᵐ x∂volume,x∈U → w.1 0 x=u.1 a.succ x)
    (g:smoothCompactCore n) (hg:tsupport g.1⊆U) :
    (∫ x,w.1 k.succ x*g.1 x)= -(∫ x,u.1 k.succ x*coordinateDerivative a g.1 x) := by
  have hw := dirichletSobolev_integral_by_parts w k g
  have he : (∫ x,w.1 0 x*coordinateDerivative k g.1 x)=∫ x,u.1 a.succ x*coordinateDerivative k g.1 x := by
    apply integral_congr_ae
    filter_upwards [hval] with x hx
    by_cases hxU:x∈U
    · rw [hx hxU]
    · have hd : coordinateDerivative k g.1 x=0 :=
        image_eq_zero_of_notMem_tsupport (fun hh=>hxU (hg (coordinateDerivative_tsupport_subset g.1 k hh)))
      rw [hd,mul_zero,mul_zero]
  have hua := dirichletSobolev_integral_by_parts u a (smoothCompactDerivative k g)
  have huk := dirichletSobolev_integral_by_parts u k (smoothCompactDerivative a g)
  change (∫ x,u.1 a.succ x*coordinateDerivative k g.1 x)=
    -(∫ x,u.1 0 x*coordinateDerivative a (coordinateDerivative k g.1) x) at hua
  change (∫ x,u.1 k.succ x*coordinateDerivative a g.1 x)=
    -(∫ x,u.1 0 x*coordinateDerivative k (coordinateDerivative a g.1) x) at huk
  rw [coordinateDerivative_commute (contDiff_infty.mp g.2.1 2) a k] at hua
  rw [hw,he,hua,neg_neg]
  linarith

/-- Product testing of the commuting mixed weak derivatives gives the
literal differentiated energy entry for a smooth coefficient. -/
lemma weak_differentiated_energy_entry {Ω Ω' U:Set (CoordinateSpace n)}
    (u:dirichletSobolev Ω) (w:dirichletSobolev Ω') (a i k:Fin n)
    (hval:∀ᵐ x∂volume,x∈U → w.1 0 x=u.1 a.succ x)
    {A:CoordinateSpace n → ℝ} (hA:ContDiff ℝ ∞ A)
    (ψ:smoothCompactCore n) (hψ:tsupport ψ.1⊆U) :
    (∫ x,A x*w.1 k.succ x*coordinateDerivative i ψ.1 x)=
      -(∫ x,coordinateDerivative a A x*u.1 k.succ x*coordinateDerivative i ψ.1 x)-
      ∫ x,A x*u.1 k.succ x*coordinateDerivative i (coordinateDerivative a ψ.1) x := by
  let g := smoothCompactMultiply hA (smoothCompactDerivative i ψ)
  have hgs : tsupport g.1⊆U :=
    tsupport_mul_subset_right.trans ((coordinateDerivative_tsupport_subset ψ.1 i).trans hψ)
  have hh := weak_mixed_partial_commutation u w a k hval g hgs
  have hi : Integrable (fun x=>coordinateDerivative a A x*u.1 k.succ x*coordinateDerivative i ψ.1 x) := by
    have hd : MemLp (fun x => coordinateDerivative a A x * coordinateDerivative i ψ.1 x) 2 (volume : Measure (CoordinateSpace n)) := smooth_compact_memLp
      ((smooth_coordinateDerivative hA a).mul (smooth_coordinateDerivative ψ.2.1 i))
      ((ψ.2.2.fderiv_apply (𝕜:=ℝ) (Pi.single i 1)).mul_left)
    convert (Lp.memLp (u.1 k.succ)).integrable_mul hd using 1 <;> ext x <;> dsimp only [Pi.mul_apply] <;> ring
  have hj : Integrable (fun x=>A x*u.1 k.succ x*coordinateDerivative i (coordinateDerivative a ψ.1) x) := by
    have hd : MemLp (fun x => A x * coordinateDerivative i (coordinateDerivative a ψ.1) x) 2 (volume : Measure (CoordinateSpace n)) := smooth_compact_memLp
      (hA.mul (smooth_coordinateDerivative (smooth_coordinateDerivative ψ.2.1 a) i))
      (((ψ.2.2.fderiv_apply (𝕜:=ℝ) (Pi.single a 1)).fderiv_apply (𝕜:=ℝ) (Pi.single i 1)).mul_left)
    convert (Lp.memLp (u.1 k.succ)).integrable_mul hd using 1 <;> ext x <;> dsimp only [Pi.mul_apply] <;> ring
  have hd (x:CoordinateSpace n) : coordinateDerivative a g.1 x=
      coordinateDerivative a A x*coordinateDerivative i ψ.1 x+
        A x*coordinateDerivative i (coordinateDerivative a ψ.1) x := by
    change coordinateDerivative a (fun y=>A y*coordinateDerivative i ψ.1 y) x=_
    rw [coordinateDerivative_mul (hA.differentiable (by simp))
      ((smooth_coordinateDerivative ψ.2.1 i).differentiable (by simp)),
      coordinateDerivative_commute (contDiff_infty.mp ψ.2.1 2) a i]
  have hL : (∫ x,w.1 k.succ x*g.1 x)=∫ x,A x*w.1 k.succ x*coordinateDerivative i ψ.1 x := by
    apply integral_congr_ae
    apply ae_of_all
    intro x
    change w.1 k.succ x*(A x*coordinateDerivative i ψ.1 x)=_
    ring
  have hR : (∫ x,u.1 k.succ x*coordinateDerivative a g.1 x)=
      (∫ x,coordinateDerivative a A x*u.1 k.succ x*coordinateDerivative i ψ.1 x)+
      ∫ x,A x*u.1 k.succ x*coordinateDerivative i (coordinateDerivative a ψ.1) x := by
    rw [← integral_add hi hj]
    apply integral_congr_ae
    apply ae_of_all
    intro x
    dsimp only
    rw [hd]
    ring
  rw [hL,hR] at hh
  linarith

end GaussianTilt.MomentMapLinearDirichlet
