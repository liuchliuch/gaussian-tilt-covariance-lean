import GaussianTilt.MomentMapLinearDirichletTangentialNormalHolder
import GaussianTilt.MomentMapSchauderBoundedHolder

/-! # Compositional bounded Hölder normal recovery for both weak passes -/
noncomputable section
set_option maxHeartbeats 2000000
open Set Matrix
open scoped Topology BigOperators Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapRegularity GaussianTilt.MomentMapSchauder
variable {n : ℕ}

/-- Positive denominator division preserves the actual bounded Hölder
modulus, with the quotient estimate proved from literal differences. -/
lemma boundedHolderOn_div_positive {X : Type*} [NormedAddCommGroup X]
    {S : Set X} {f g : X→ℝ} {α δ : ℝ} (hδ : 0<δ)
    (hf : BoundedHolderOn α f S) (hg : BoundedHolderOn α g S)
    (hpos : ∀ x∈S,δ≤g x) : BoundedHolderOn α (fun x=>f x/g x) S := by
  obtain ⟨C,hC,hfb,hfh⟩ := hf
  obtain ⟨D,hD,hgb,hgh⟩ := hg
  let B := C/δ+C*D/δ^2
  have hB : 0≤B := by dsimp [B]; positivity
  have hCδ : C/δ≤B := le_add_of_nonneg_right (by positivity)
  refine ⟨B,hB,?_,?_⟩
  · intro x hx
    rw [Real.norm_eq_abs,abs_div,abs_of_pos (hδ.trans_le (hpos x hx))]
    exact ((div_le_div_of_nonneg_right (hfb x hx) (hδ.trans_le (hpos x hx)).le).trans
      (div_le_div_of_nonneg_left hC hδ (hpos x hx))).trans hCδ
  · intro x hx y hy
    have hp : 0≤‖x-y‖^α := Real.rpow_nonneg (norm_nonneg _) _
    have hh := quotient_difference_bound hδ (hpos x hx) (hpos y hy)
      (mul_nonneg hD hp) (mul_nonneg hC hp) hC (hfh x hx y hy) (hfb y hy) (hgh x hx y hy)
    change |f x/g x-f y/g y|≤B*‖x-y‖^α
    exact hh.trans_eq (by dsimp [B]; ring)

/-- A convenient exact-exponent wrapper consuming the actual Hölder
fields constructed by the two Campanato passes. -/
theorem boundedHolderOn_recoveredWeakHessian (q : Fin n) {S : Set (CoordinateSpace n)}
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {G : CoordinateSpace n → CoordinateSpace n}
    {J : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {f : CoordinateSpace n→ℝ} {α lam : ℝ}
    (hlam : 0<lam) (hell : ∀ x∈S,lam≤A x q q)
    (hA : ∀ i k,BoundedHolderOn α (fun x=>A x i k) S)
    (hD : ∀ i k l,BoundedHolderOn α (coordinateDerivative l (fun x=>A x i k)) S)
    (hG : ∀ k,BoundedHolderOn α (fun x=>G x k) S)
    (hJ : ∀ k i,BoundedHolderOn α (fun x=>J x k i) S) (hf : BoundedHolderOn α f S) :
    BoundedHolderOn α (recoveredWeakHessian q A G J f) S := by
  have hH (k i : Fin n) : BoundedHolderOn α (fun x=>nonNormalHessian q J x k i) S := by
    by_cases hk : k=q
    · simpa only [nonNormalHessian,if_pos hk] using hJ i q
    · simpa only [nonNormalHessian,if_neg hk] using hJ k i
  have hN : BoundedHolderOn α (nonNormalDivergence q A G (nonNormalHessian q J)) S :=
    BoundedHolderOn.finset_sum _ (fun p _=>((hD p.1 p.2 p.1).mul (hG p.2)).add ((hA p.1 p.2).mul (hH p.2 p.1)))
  have hF (i : Fin n) : BoundedHolderOn α (fun x=>normalFluxGradient q A G (nonNormalHessian q J) f x i) S := by
    by_cases hi : i=q
    · simpa only [normalFluxGradient,if_pos hi] using hf.neg.sub hN
    · simpa only [normalFluxGradient,if_neg hi] using
        ((hD q q i).mul (hG q)).add ((hA q q).mul (hH q i))
  have hR (i : Fin n) : BoundedHolderOn α (fun x=>recoveredNormalRow q A G (nonNormalHessian q J) f x i) S :=
    boundedHolderOn_div_positive hlam ((hF i).sub ((hD q q i).mul (hG q))) (hA q q) hell
  have hentry (k i : Fin n) : BoundedHolderOn α (fun x=>recoveredWeakHessian q A G J f x k i) S := by
    by_cases hk : k=q
    · simpa only [recoveredWeakHessian,if_pos hk] using hR i
    · simpa only [recoveredWeakHessian,if_neg hk] using hJ k i
  exact BoundedHolderOn.pi (fun k=>BoundedHolderOn.pi (hentry k))

end GaussianTilt.MomentMapLinearDirichlet
