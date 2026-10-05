import GaussianTilt.MomentMapLinearDirichletVariableWeakPhysicalHolder

/-! # Constructed Hölder vector equations for the two actual weak-boundary passes -/
noncomputable section
open Set MeasureTheory Filter Matrix
open scoped Topology ContDiff ENNReal BigOperators Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapSchauder
variable {n : ℕ}
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 1000

/-- From the actual first-derivative representative, construct the true
Hölder vector equation for a tangential H¹ derivative. The coefficient
bounds needed for the L² products are derived from smoothness and compactness. -/
theorem exists_holder_tangential_vector_equation {Ω Ω' U S V:Set (CoordinateSpace n)}
    (hU:IsOpen U) (hV:IsOpen V) (hS:IsCompact S) (hc:Convex ℝ S) (hUS:U⊆S) (hSV:S⊆V)
    (u:dirichletSobolev Ω) (w:dirichletSobolev Ω') (a:Fin n)
    (hwval:∀ᵐ x∂volume,x∈U → w.1 0 x=u.1 a.succ x)
    (A:CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hA:∀ i k,ContDiffOn ℝ ∞ (fun x=>A x i k) V)
    (hAm:∀ i k,AEStronglyMeasurable (fun x=>A x i k) volume)
    {K:ℝ} (hK:0≤K) (hAb:∀ i k,∀ᵐ x∂volume,|A x i k|≤K)
    (f:Lp ℝ 2 (volume:Measure (CoordinateSpace n)))
    (heq:∀ψ:smoothCompactCore n,tsupport ψ.1⊆U →
      (∫ x,∑ i:Fin n,∑ k:Fin n,A x i k*u.1 k.succ x*coordinateDerivative i ψ.1 x)=∫ x,f x*ψ.1 x)
    {f₀:CoordinateSpace n → ℝ} {q:CoordinateSpace n → CoordinateSpace n}
    (hf:∀ᵐ x∂volume,x∈U → f x=f₀ x)
    (hq:∀ k,∀ᵐ x∂volume,x∈U → u.1 k.succ x=q x k)
    {α γ β:ℝ} (hβ:0≤β) (hβ1:β≤1) (hβα:β≤α) (hβγ:β≤γ)
    (hfH:BoundedHolderOn α f₀ S) (hqH:∀ k,BoundedHolderOn γ (fun x=>q x k) S) :
    ∃ G:Fin n → Lp ℝ 2 (volume:Measure (CoordinateSpace n)),
    ∃ g:CoordinateSpace n → CoordinateSpace n,
      BoundedHolderOn β g S ∧ (∀ i,∀ᵐ x∂volume,x∈U → G i x=g x i) ∧
      (∀ x i,g x i= -(if i=a then f₀ x else 0)-
        ∑ k:Fin n,coordinateDerivative a (fun y=>A y i k) x*q x k) ∧
      ∀ v:dirichletSobolev U,variableJetEnergy A hAm hK hAb w.1 v.1=variableScalarVectorLoad U 0 G v := by
  let D:CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ := fun x i k=>coordinateDerivative a (fun y=>A y i k) x
  have hDH (i k:Fin n) : BoundedHolderOn β (fun x=>D x i k) S :=
    boundedHolderOn_coefficient_derivatives hV hS hc hSV hA hβ hβ1 a i k
  have hDM : BoundedHolderOn β D S :=
    BoundedHolderOn.pi (fun i=>BoundedHolderOn.pi (hDH i))
  obtain ⟨L,hL,hLb,hLH⟩ := hDM
  have hD (x:CoordinateSpace n) (hx:x∈U) (i k:Fin n) : |D x i k|≤L :=
    ((norm_le_pi_norm (D x i) k).trans (norm_le_pi_norm (D x) i)).trans (hLb x (hUS hx))
  obtain ⟨G,hG,hGeq⟩ := exists_differentiated_vector_equation hU u w a hwval A
    (fun i k=>(hA i k).mono (hUS.trans hSV)) hAm hK hL hAb hD f heq
  obtain ⟨g,hg,hgAE,hgval⟩ := differentiated_vector_load_holder_representative a u.1 f D G hG hf hq
    hβ hβα hβγ hfH hqH hDH
  exact ⟨G,g,hg,hgAE,hgval,hGeq⟩

/-- After the first genuine C² boundary recovery, continuity of the actual
within-domain derivative rows gives Lipschitz first derivatives. Therefore
the differentiated vector load recovers the original scalar-data exponent,
without assuming a Lipschitz gradient or a quantitative Hessian bound. -/
theorem exists_original_exponent_tangential_vector_equation {Ω Ω' U S V:Set (CoordinateSpace n)}
    (hU:IsOpen U) (hV:IsOpen V) (hS:IsCompact S) (hc:Convex ℝ S) (hUS:U⊆S) (hSV:S⊆V)
    (u:dirichletSobolev Ω) (w:dirichletSobolev Ω') (a:Fin n)
    (hwval:∀ᵐ x∂volume,x∈U → w.1 0 x=u.1 a.succ x)
    (A:CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hA:∀ i k,ContDiffOn ℝ ∞ (fun x=>A x i k) V)
    (hAm:∀ i k,AEStronglyMeasurable (fun x=>A x i k) volume)
    {K:ℝ} (hK:0≤K) (hAb:∀ i k,∀ᵐ x∂volume,|A x i k|≤K)
    (f:Lp ℝ 2 (volume:Measure (CoordinateSpace n)))
    (heq:∀ψ:smoothCompactCore n,tsupport ψ.1⊆U →
      (∫ x,∑ i:Fin n,∑ k:Fin n,A x i k*u.1 k.succ x*coordinateDerivative i ψ.1 x)=∫ x,f x*ψ.1 x)
    {f₀:CoordinateSpace n → ℝ} {q:CoordinateSpace n → CoordinateSpace n}
    (hf:∀ᵐ x∂volume,x∈U → f x=f₀ x)
    (hq:∀ k,∀ᵐ x∂volume,x∈U → u.1 k.succ x=q x k)
    (Dq:Fin n → CoordinateSpace n → CoordinateSpace n →L[ℝ] ℝ)
    (hqder:∀ k,∀ x∈S,HasFDerivWithinAt (fun y=>q y k) (Dq k x) S x)
    (hDq:∀ k,ContinuousOn (Dq k) S)
    {α:ℝ} (hα:0≤α) (hα1:α≤1) (hfH:BoundedHolderOn α f₀ S) :
    ∃ G:Fin n → Lp ℝ 2 (volume:Measure (CoordinateSpace n)),
    ∃ g:CoordinateSpace n → CoordinateSpace n,
      BoundedHolderOn α g S ∧ (∀ i,∀ᵐ x∂volume,x∈U → G i x=g x i) ∧
      (∀ x i,g x i= -(if i=a then f₀ x else 0)-
        ∑ k:Fin n,coordinateDerivative a (fun y=>A y i k) x*q x k) ∧
      ∀ v:dirichletSobolev U,variableJetEnergy A hAm hK hAb w.1 v.1=variableScalarVectorLoad U 0 G v := by
  have hqH (k:Fin n) : BoundedHolderOn α (fun x=>q x k) S :=
    boundedHolderOn_of_continuous_within_derivative hS hc (hqder k) (hDq k) hα hα1
  exact exists_holder_tangential_vector_equation hU hV hS hc hUS hSV u w a hwval A hA hAm hK hAb f heq hf hq
    hα hα1 le_rfl le_rfl hfH hqH

end GaussianTilt.MomentMapLinearDirichlet
