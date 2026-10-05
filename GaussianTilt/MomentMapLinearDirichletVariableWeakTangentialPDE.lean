import GaussianTilt.MomentMapLinearDirichletVariableWeakTangentialDifferentiated

/-! # The literal differentiated divergence PDE from actual mixed weak derivatives -/
noncomputable section
open Set MeasureTheory Filter Matrix
open scoped Topology ContDiff ENNReal BigOperators
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin
variable {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 1000

lemma integrable_smooth_weight_weak_test (u:Lp ℝ 2 (volume:Measure (CoordinateSpace n)))
    {A:CoordinateSpace n → ℝ} (hA:ContDiff ℝ ∞ A) (ψ:smoothCompactCore n) :
    Integrable (fun x=>A x*u x*ψ.1 x) := by
  have hd : MemLp (fun x=>A x*ψ.1 x) 2 (volume:Measure (CoordinateSpace n)) :=
    smooth_compact_memLp (hA.mul ψ.2.1) ψ.2.2.mul_left
  convert (Lp.memLp u).integrable_mul hd using 1 <;> ext x <;> dsimp only [Pi.mul_apply] <;> ring

lemma integral_double_sum_weak (F:Fin n → Fin n → CoordinateSpace n → ℝ)
    (hF:∀ i k,Integrable (F i k)) :
    (∫ x,∑ i:Fin n,∑ k:Fin n,F i k x)=∑ i:Fin n,∑ k:Fin n,∫ x,F i k x := by
  rw [integral_finset_sum _ (fun i _=>integrable_finset_sum _ (fun k _=>hF i k))]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_finset_sum _ (fun k _=>hF i k)

/-- Testwise differentiation requires only the original equation tested
with the actual compact derivative of ψ and local value identification
of the constructed H¹ derivative. -/
theorem weak_differentiated_equation_of_test_equation {Ω Ω' U:Set (CoordinateSpace n)}
    (u:dirichletSobolev Ω) (w:dirichletSobolev Ω') (a:Fin n)
    (hval:∀ᵐ x∂volume,x∈U → w.1 0 x=u.1 a.succ x)
    (A:CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hA:∀ i k,ContDiff ℝ ∞ (fun x=>A x i k)) (f:CoordinateSpace n → ℝ)
    (ψ:smoothCompactCore n) (hψ:tsupport ψ.1⊆U)
    (heq:(∫ x,∑ i:Fin n,∑ k:Fin n,A x i k*u.1 k.succ x*coordinateDerivative i (coordinateDerivative a ψ.1) x)=
      ∫ x,f x*coordinateDerivative a ψ.1 x) :
    (∫ x,∑ i:Fin n,∑ k:Fin n,A x i k*w.1 k.succ x*coordinateDerivative i ψ.1 x)=
      -(∫ x,f x*coordinateDerivative a ψ.1 x)-
      ∫ x,∑ i:Fin n,∑ k:Fin n,coordinateDerivative a (fun y=>A y i k) x*u.1 k.succ x*coordinateDerivative i ψ.1 x := by
  have hIw (i k:Fin n) : Integrable (fun x=>A x i k*w.1 k.succ x*coordinateDerivative i ψ.1 x) :=
    integrable_smooth_weight_weak_test (w.1 k.succ) (hA i k) (smoothCompactDerivative i ψ)
  have hIc (i k:Fin n) : Integrable (fun x=>coordinateDerivative a (fun y=>A y i k) x*u.1 k.succ x*coordinateDerivative i ψ.1 x) :=
    integrable_smooth_weight_weak_test (u.1 k.succ) (smooth_coordinateDerivative (hA i k) a) (smoothCompactDerivative i ψ)
  have hIo (i k:Fin n) : Integrable (fun x=>A x i k*u.1 k.succ x*coordinateDerivative i (coordinateDerivative a ψ.1) x) :=
    integrable_smooth_weight_weak_test (u.1 k.succ) (hA i k) (smoothCompactDerivative i (smoothCompactDerivative a ψ))
  have he (i k:Fin n) := weak_differentiated_energy_entry u w a i k hval (hA i k) ψ hψ
  have hs := congrArg (fun F:Fin n → Fin n → ℝ=>∑ i:Fin n,∑ k:Fin n,F i k)
    (funext fun i=>funext fun k=>he i k)
  simp only [Finset.sum_sub_distrib,Finset.sum_neg_distrib] at hs
  rw [integral_double_sum_weak _ hIo] at heq
  rw [integral_double_sum_weak _ hIw,integral_double_sum_weak _ hIc]
  linarith

end GaussianTilt.MomentMapLinearDirichlet
