import GaussianTilt.MomentMapSchauderGlobalBoundaryLocal
import GaussianTilt.MomentMapSchauderGlobalInteriorLocal
import GaussianTilt.MomentMapSchauderGlobalNormAbsorption

/-! # Genuine global Schauder estimate on smooth convex domains

The local interior and curved-boundary estimates are proved for actual
compatible jets. A compact cover and literal norm absorption yield one
constant for an entire compact coefficient family.
-/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 3200000
open Set Filter Matrix
open scoped Topology ContDiff Gradient
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic GaussianTilt.HolderSpace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

lemma exists_nonzero_basis_derivative {w : KernelSpace n → ℝ} {a : KernelSpace n}
    (hg : gradient w a≠0) : ∃ q : Fin n, fderiv ℝ w a (EuclideanSpace.basisFun (Fin n) ℝ q)≠0 := by
  classical
  by_contra he
  push_neg at he
  have hD : fderiv ℝ w a=0 := by
    have hL : (fderiv ℝ w a).toLinearMap=0 := by
      apply (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext
      intro i
      exact he i
    ext x
    exact LinearMap.congr_fun hL x
  apply hg
  simp only [gradient,hD,map_zero]

structure EllipticJetDatum (I : Type*) {S : Set (KernelSpace n)} (hS : Convex ℝ S) (α : ℝ) where
  parameter : I
  jet : zeroBoundary (KernelSpace n) ℝ hS α
  forcing : KernelSpace n → ℝ
  valueBound : ℝ
  forcingBound : ℝ
  holderBound : ℝ

def EllipticJetDatum.Valid {I : Type*} {S : Set (KernelSpace n)} {hS : Convex ℝ S} {α : ℝ}
    (P : Set I) (A : I → KernelSpace n → Matrix (Fin n) (Fin n) ℝ) (g : EllipticJetDatum I hS α) : Prop :=
  g.parameter ∈ P ∧ 0 ≤ g.valueBound ∧ 0 ≤ g.forcingBound ∧ 0 ≤ g.holderBound ∧
  (∀ x : S, |value S ℝ α (jetValue (KernelSpace n) ℝ hS α g.jet.1) x| ≤ g.valueBound) ∧
  (∀ x ∈ S, |g.forcing x| ≤ g.forcingBound) ∧
  (∀ x ∈ S, ∀ y ∈ S, |g.forcing x-g.forcing y| ≤ g.holderBound*‖x-y‖^α) ∧
  (∀ x ∈ interior S, euclideanEllipticOperator (A g.parameter x)
    (extendValue α (jetValue (KernelSpace n) ℝ hS α g.jet.1)) x=g.forcing x)

/-- The full, uniform C²,α a priori estimate on the actual smooth body.
The coefficient family has only its genuine Cα modulus; every test
function is an arbitrary compatible zero-boundary C²,α jet. -/
theorem exists_smooth_domain_global_schauder_estimate [NeZero n]
    {I : Type*} [TopologicalSpace I] {P : Set I} (hP : IsCompact P)
    {S₀ A₀ : Set (KernelSpace n)} (d : SmoothInnerDomain S₀ A₀)
    {α M K : ℝ} (hα : 0 < α) (hα1 : α < 1) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (A : I → KernelSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hAt : ∀ a ∈ d.body, ContinuousOn (fun t => A t a) P)
    (hAp : ∀ t ∈ P, ∀ x ∈ d.body, (A t x).PosDef)
    (hAs : ∀ t ∈ P, ∀ x ∈ d.body, (A t x).IsSymm)
    (hAb : ∀ t ∈ P, ∀ x ∈ d.body, ∀ i k, |A t x i k| ≤ M)
    (hAH : ∀ t ∈ P, ∀ x ∈ d.body, ∀ y ∈ d.body, ∀ i k, |A t x i k-A t y i k| ≤ K*‖x-y‖^α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ P, ∀ J : zeroBoundary (KernelSpace n) ℝ d.convex_body α,
      ∀ (f : KernelSpace n → ℝ) (U F H : ℝ), 0 ≤ U → 0 ≤ F → 0 ≤ H →
      (∀ x : d.body, |value d.body ℝ α (jetValue (KernelSpace n) ℝ d.convex_body α J.1) x| ≤ U) →
      (∀ x ∈ d.body, |f x| ≤ F) →
      (∀ x ∈ d.body, ∀ y ∈ d.body, |f x-f y| ≤ H*‖x-y‖^α) →
      (∀ x ∈ interior d.body, euclideanEllipticOperator (A t x)
        (extendValue α (jetValue (KernelSpace n) ℝ d.convex_body α J.1)) x=f x) →
      ‖J‖ ≤ C*(U+F+H) := by
  have hint : (interior d.body).Nonempty := by rw [d.interior_body]; exact d.negative_nonempty
  let Γ := EllipticJetDatum I d.convex_body α
  let valid : Γ → Prop := EllipticJetDatum.Valid P A
  let data : Γ → ℝ := fun g => g.valueBound+g.forcingBound+g.holderBound
  have hdata : ∀ g, valid g → 0 ≤ data g := by
    intro g hg
    exact add_nonneg (add_nonneg hg.2.1 hg.2.2.1) hg.2.2.2.1
  have hvalue : ∀ g, valid g → ∀ x : d.body,
      |value d.body ℝ α (jetValue (KernelSpace n) ℝ d.convex_body α g.jet.1) x| ≤ data g := by
    intro g hg x
    have hh := hg.2.2.2.2.1 x
    dsimp only [data]
    linarith [hg.2.2.1,hg.2.2.2.1]
  have hlocal : ∀ a ∈ d.body, ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
      ∀ g : Γ, valid g →
      (∀ x ∈ d.body, dist x a < r →
        ‖extendValue α (jetSecond (KernelSpace n) ℝ d.convex_body α g.jet.1) x‖ ≤ C*data g+ε*‖g.jet.1‖) ∧
      (∀ x ∈ d.body, dist x a < r → ∀ y ∈ d.body, dist y a < r →
        ‖extendValue α (jetSecond (KernelSpace n) ℝ d.convex_body α g.jet.1) x-
          extendValue α (jetSecond (KernelSpace n) ℝ d.convex_body α g.jet.1) y‖ ≤
            (C*data g+ε*‖g.jet.1‖)*dist x y^α) := by
    intro a ha
    by_cases hai : a ∈ interior d.body
    · obtain ⟨r,hr,hest⟩ := exists_body_interior_local_estimate hP d.convex_body d.compact_sublevel.isClosed
        hα hα1 hK a hai A (hAt a ha) (fun t ht => hAp t ht a ha) hAs hAH
      refine ⟨r,hr,?_⟩
      intro ε hε
      obtain ⟨C,hC,hbound⟩ := hest ε hε
      refine ⟨C,hC.le,?_⟩
      intro g hg
      obtain ⟨ht,hU,hF,hH,hu,hf,hfH,heq⟩ := hg
      obtain ⟨hb,hh⟩ := hbound g.parameter ht g.jet.1 g.forcing g.valueBound g.forcingBound g.holderBound hU hF hH hu hf hfH heq
      exact ⟨fun x hx hxa => hb x ⟨hx,hxa⟩,fun x hx hxa y hy hya => by
        simpa only [dist_eq_norm] using hh x ⟨hx,hxa⟩ y ⟨hy,hya⟩⟩
    · have ha0 : d.defining a=0 := by
        have hale : d.defining a ≤ 0 := ha
        have hnot : ¬ d.defining a < 0 := by simpa only [d.interior_body,SmoothInnerDomain.domain,mem_setOf_eq] using hai
        exact le_antisymm hale (not_lt.mp hnot)
      obtain ⟨q,hq⟩ := exists_nonzero_basis_derivative (d.regular_level a ha0)
      obtain ⟨r,hr,hest⟩ := exists_smooth_domain_boundary_local_estimate hP d hα hα1 hM hK a ha0 q hq
        A (hAt a ha) (fun t ht => hAp t ht a ha) hAs hAb hAH
      refine ⟨r,hr,?_⟩
      intro ε hε
      obtain ⟨C,hC,hbound⟩ := hest ε hε
      refine ⟨C,hC.le,?_⟩
      intro g hg
      obtain ⟨ht,hU,hF,hH,hu,hf,hfH,heq⟩ := hg
      obtain ⟨hb,hh⟩ := hbound g.parameter ht g.jet g.forcing g.valueBound g.forcingBound g.holderBound hU hF hH hu hf hfH heq
      exact ⟨fun x hx hxa => hb x ⟨hx,hxa⟩,fun x hx hxa y hy hya => by
        simpa only [dist_eq_norm] using hh x ⟨hx,hxa⟩ y ⟨hy,hya⟩⟩
  obtain ⟨C,hC,hbound⟩ := exists_global_jet_norm_of_local_small_hessian d.convex_body d.compact_sublevel hint
    hα hα1.le (fun g : Γ => g.jet.1) valid data hdata hvalue hlocal
  refine ⟨C,hC,?_⟩
  intro t ht J f U F H hU hF hH hu hf hfH heq
  exact hbound ⟨t,J,f,U,F,H⟩ ⟨ht,hU,hF,hH,hu,hf,hfH,heq⟩

end GaussianTilt.MomentMapSchauder
