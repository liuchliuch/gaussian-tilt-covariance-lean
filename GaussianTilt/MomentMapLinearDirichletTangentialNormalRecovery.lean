import GaussianTilt.MomentMapLinearDirichletTangentialNormalFlux
import GaussianTilt.MomentMapLinearDirichletTangentialNormalJets

/-! # Full genuine C² recovery from two actual weak-gradient passes -/
noncomputable section
set_option maxHeartbeats 3000000
open MeasureTheory Set Filter Matrix
open scoped Topology ContDiff BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapRegularity GaussianTilt.HolderSpace
variable {n : ℕ}

/-- The full Hessian candidate: tangential rows are actual second weak
jets and the remaining row is recovered from the true normal flux. -/
def recoveredWeakHessian (q : Fin n)
    (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (G : CoordinateSpace n → CoordinateSpace n)
    (J : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ) (f : CoordinateSpace n→ℝ)
    (x : CoordinateSpace n) (k i : Fin n) : ℝ :=
  if k=q then recoveredNormalRow q A G (nonNormalHessian q J) f x i else J x k i

/-- Literal weak energy transfers to the continuous first-gradient
representative only on the actual compact test support. -/
lemma weak_divergence_continuous_gradient {Ω U : Set (CoordinateSpace n)}
    (u : dirichletSobolev Ω)
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    {G : CoordinateSpace n → CoordinateSpace n} {f : CoordinateSpace n→ℝ}
    (hG : ∀ k,∀ᵐ x∂volume,x∈U → G x k=u.1 k.succ x)
    (hweak : ∀ ψ : smoothCompactCore n,tsupport ψ.1⊆U →
      (∫ x,∑ i : Fin n,∑ k : Fin n,A x i k*u.1 k.succ x*coordinateDerivative i ψ.1 x)=∫ x,f x*ψ.1 x) :
    ∀ ψ : smoothCompactCore n,tsupport ψ.1⊆U →
      (∫ x,∑ i : Fin n,∑ k : Fin n,A x i k*G x k*coordinateDerivative i ψ.1 x)=∫ x,f x*ψ.1 x := by
  intro ψ hψ
  rw [← hweak ψ hψ]
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr hG] with x hx
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  by_cases hxU : x∈U
  · rw [hx k hxU]
  · have hd : coordinateDerivative i ψ.1 x=0 := image_eq_zero_of_notMem_tsupport
        (fun hh=>hxU (hψ (coordinateDerivative_tsupport_subset ψ.1 i hh)))
    rw [hd,mul_zero,mul_zero]

/-- Each row of the recovered Hessian is an actual Fréchet derivative.
Inputs are only the original H₀¹ jet and the two continuous AE gradient
representatives furnished by the two weak Campanato passes. -/
theorem recoveredWeakHessian_hasFDerivAt
    {Ω Ω' U : Set (CoordinateSpace n)} (hU : IsOpen U)
    (q : Fin n) (u : dirichletSobolev Ω)
    (W : ∀ k : Fin n,k≠q → dirichletSobolev Ω')
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    {G : CoordinateSpace n → CoordinateSpace n}
    {J : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {f : CoordinateSpace n→ℝ}
    (hA : ∀ i k,ContDiffOn ℝ ∞ (fun x=>A x i k) U)
    (hGc : ∀ k,ContinuousOn (fun x=>G x k) U)
    (hJc : ∀ k i,ContinuousOn (fun x=>J x k i) U) (hf : ContinuousOn f U)
    (hG : ∀ k,∀ᵐ x∂volume,x∈U → G x k=u.1 k.succ x)
    (hW : ∀ k (hk:k≠q),∀ᵐ x∂volume,x∈U → (W k hk).1 0 x=u.1 k.succ x)
    (hJ : ∀ k (hk:k≠q) i,∀ᵐ x∂volume,x∈U → J x k i=(W k hk).1 i.succ x)
    (hweak : ∀ ψ : smoothCompactCore n,tsupport ψ.1⊆U →
      (∫ x,∑ i : Fin n,∑ k : Fin n,A x i k*u.1 k.succ x*coordinateDerivative i ψ.1 x)=∫ x,f x*ψ.1 x)
    (hneq : ∀ x∈U,A x q q≠0) :
    ∀ k x,x∈U → HasFDerivAt (fun y=>G y k) (coordinateCovector (recoveredWeakHessian q A G J f x k)) x := by
  have hknown := nonNormalHessian_weak_derivatives q u W hG hW hJ
  have hHc := continuousOn_nonNormalHessian q hJc
  have heq := weak_divergence_continuous_gradient u hG hweak
  intro k x hx
  by_cases hk : k=q
  · subst k
    have hr : recoveredWeakHessian q A G J f x q=recoveredNormalRow q A G (nonNormalHessian q J) f x := by
      funext i
      simp [recoveredWeakHessian]
    rw [hr]
    exact normal_component_hasFDerivAt_of_nonNormalWeakDerivatives hU q hA hGc hHc hf hknown heq hneq hx
  · have hw : ∀ i : Fin n,∀ ψ : smoothCompactCore n,tsupport ψ.1⊆U →
        (∫ y,G y k*coordinateDerivative i ψ.1 y)= -(∫ y,J y k i*ψ.1 y) := by
      intro i
      simpa only [HasLocalWeakDerivative,nonNormalHessian,if_neg hk] using hknown i k (Or.inr hk)
    have hd := (contDiffOn_one_of_continuous_coordinate_weak_components hU (hGc k)
      (continuousOn_pi.mpr (hJc k)) hw).2 x hx
    have hr : recoveredWeakHessian q A G J f x k=J x k := by
      funext i
      simp only [recoveredWeakHessian,if_neg hk]
    rw [hr]
    exact hd

lemma continuousOn_recoveredWeakHessian {S : Set (CoordinateSpace n)} (q : Fin n)
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    {G : CoordinateSpace n → CoordinateSpace n}
    {J : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {f : CoordinateSpace n→ℝ}
    (hA : ∀ i k,ContinuousOn (fun x=>A x i k) S)
    (hAD : ∀ i k l,ContinuousOn (coordinateDerivative l (fun x=>A x i k)) S)
    (hG : ∀ k,ContinuousOn (fun x=>G x k) S)
    (hJ : ∀ k i,ContinuousOn (fun x=>J x k i) S) (hf : ContinuousOn f S)
    (hneq : ∀ x∈S,A x q q≠0) :
    ∀ k i,ContinuousOn (fun x=>recoveredWeakHessian q A G J f x k i) S := by
  have hH := continuousOn_nonNormalHessian q hJ
  have hN : ContinuousOn (nonNormalDivergence q A G (nonNormalHessian q J)) S := by
    apply continuousOn_finset_sum
    intro p _
    exact ((hAD p.1 p.2 p.1).mul (hG p.2)).add ((hA p.1 p.2).mul (hH p.2 p.1))
  have hF (i : Fin n) : ContinuousOn (fun x=>normalFluxGradient q A G (nonNormalHessian q J) f x i) S := by
    by_cases hi : i=q
    · simpa only [normalFluxGradient,if_pos hi] using hf.neg.sub hN
    · simpa only [normalFluxGradient,if_neg hi] using
        ((hAD q q i).mul (hG q)).add ((hA q q).mul (hH q i))
  intro k i
  by_cases hk : k=q
  · simp only [recoveredWeakHessian,if_pos hk,recoveredNormalRow]
    exact ((hF i).sub ((hAD q q i).mul (hG q))).div (hA q q) hneq
  · simpa only [recoveredWeakHessian,if_neg hk] using hJ k i

/-- The complete actual C² upgrade, including the unknown normal-normal
entry, derived from genuine weak jets rather than a Hessian premise. -/
theorem contDiffOn_two_of_tangential_weak_gradient_representatives
    {Ω Ω' U : Set (CoordinateSpace n)} (hU : IsOpen U)
    (q : Fin n) (u : dirichletSobolev Ω)
    (W : ∀ k : Fin n,k≠q → dirichletSobolev Ω')
    {v : CoordinateSpace n→ℝ} {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    {G : CoordinateSpace n → CoordinateSpace n}
    {J : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {f : CoordinateSpace n→ℝ}
    (hv : ContinuousOn v U) (hval : ∀ᵐ x∂volume,x∈U → v x=u.1 0 x)
    (hA : ∀ i k,ContDiffOn ℝ ∞ (fun x=>A x i k) U)
    (hGc : ∀ k,ContinuousOn (fun x=>G x k) U)
    (hJc : ∀ k i,ContinuousOn (fun x=>J x k i) U) (hf : ContinuousOn f U)
    (hG : ∀ k,∀ᵐ x∂volume,x∈U → G x k=u.1 k.succ x)
    (hW : ∀ k (hk:k≠q),∀ᵐ x∂volume,x∈U → (W k hk).1 0 x=u.1 k.succ x)
    (hJ : ∀ k (hk:k≠q) i,∀ᵐ x∂volume,x∈U → J x k i=(W k hk).1 i.succ x)
    (hweak : ∀ ψ : smoothCompactCore n,tsupport ψ.1⊆U →
      (∫ x,∑ i : Fin n,∑ k : Fin n,A x i k*u.1 k.succ x*coordinateDerivative i ψ.1 x)=∫ x,f x*ψ.1 x)
    (hneq : ∀ x∈U,A x q q≠0) :
    ContDiffOn ℝ 2 v U ∧
      (∀ x∈U,HasFDerivAt v (coordinateCovector (G x)) x) ∧
      ∀ k x,x∈U → HasFDerivAt (fun y=>G y k) (coordinateCovector (recoveredWeakHessian q A G J f x k)) x := by
  have hDrows := recoveredWeakHessian_hasFDerivAt hU q u W hA hGc hJc hf hG hW hJ hweak hneq
  have hHc := continuousOn_recoveredWeakHessian q (fun i k=>(hA i k).continuousOn)
    (fun i k l=>continuousOn_coordinateDerivative_local hU (hA i k) l) hGc hJc hf hneq
  have hg1 : ContDiffOn ℝ 1 G U := by
    apply contDiffOn_pi.mpr
    intro k
    rw [show (1:WithTop ℕ∞)=0+1 from rfl,contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨fun x hx=>(hDrows k x hx).differentiableAt.differentiableWithinAt,by simp,?_⟩
    rw [contDiffOn_zero]
    exact ((coordinateCovector (n:=n)).continuous.comp_continuousOn
      (continuousOn_pi.mpr (hHc k))).congr (fun x hx=>(hDrows k x hx).fderiv)
  have hfirst : ∀ i,HasLocalWeakDerivative U v (fun x=>G x i) i := fun i=>
    (dirichlet_hasLocalWeakDerivative (U:=U) u i).congr_ae hval (hG i)
  have hDv := (contDiffOn_one_of_continuous_coordinate_weak_components hU hv
    (continuousOn_pi.mpr hGc) hfirst).2
  refine ⟨?_,hDv,hDrows⟩
  rw [show (2:WithTop ℕ∞)=1+1 from rfl,contDiffOn_succ_iff_fderiv_of_isOpen hU]
  refine ⟨fun x hx=>(hDv x hx).differentiableAt.differentiableWithinAt,by simp,?_⟩
  exact ((coordinateCovector (n:=n)).contDiff.comp_contDiffOn hg1).congr (fun x hx=>(hDv x hx).fderiv)

end GaussianTilt.MomentMapLinearDirichlet
