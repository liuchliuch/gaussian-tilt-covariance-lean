import GaussianTilt.MomentMapLinearDirichletTangentialNormalHolder

/-! # The recovered fields are the literal classical Hessian and PDE -/
noncomputable section
set_option maxHeartbeats 2500000
open MeasureTheory Set Filter Matrix
open scoped Topology ContDiff BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapRegularity
variable {n : ℕ}

/-- True first and row derivatives identify the literal coordinate
Hessian, using local equality of the first derivative functions. -/
theorem coordinateHessian_eq_of_actual_coordinate_fields
    {U : Set (CoordinateSpace n)} (hU : IsOpen U) {v : CoordinateSpace n→ℝ}
    {G : CoordinateSpace n → CoordinateSpace n} {H : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hDv : ∀ x∈U,HasFDerivAt v (coordinateCovector (G x)) x)
    (hDG : ∀ k x,x∈U → HasFDerivAt (fun y=>G y k) (coordinateCovector (H x k)) x)
    {x : CoordinateSpace n} (hx : x∈U) : coordinateHessian v x=H x := by
  ext k i
  have he : coordinateDerivative k v=ᶠ[𝓝 x] (fun y=>G y k) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    change fderiv ℝ v y (Pi.single k 1)=_
    rw [(hDv y hy).fderiv,coordinateCovector_single]
  change coordinateDerivative i (coordinateDerivative k v) x=H x k i
  rw [coordinateDerivative_congr_nhds he]
  change fderiv ℝ (fun y=>G y k) x (Pi.single i 1)=_
  rw [(hDG k x hx).fderiv,coordinateCovector_single]

lemma recoveredWeakHessian_nonNormal (q k i : Fin n) (hki : i≠q ∨ k≠q)
    (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ) (G : CoordinateSpace n → CoordinateSpace n)
    (J : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ) (f : CoordinateSpace n→ℝ) (x : CoordinateSpace n)
    (ha : A x q q≠0) :
    recoveredWeakHessian q A G J f x k i=nonNormalHessian q J x k i := by
  by_cases hk : k=q
  · subst k
    have hi : i≠q := hki.resolve_right (not_not.mpr rfl)
    rw [recoveredWeakHessian_normal_off q i hi A G J f x ha]
    simp only [nonNormalHessian,ite_true]
  · rw [recoveredWeakHessian_tangent q k i hk]
    simp only [nonNormalHessian,if_neg hk]

/-- The constructed normal row satisfies the exact divergence equation
pointwise. This is finite algebra with the actual elliptic denominator. -/
theorem recoveredWeakHessian_divergence_identity (q : Fin n)
    (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ) (G : CoordinateSpace n → CoordinateSpace n)
    (J : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ) (f : CoordinateSpace n→ℝ) (x : CoordinateSpace n)
    (ha : A x q q≠0) :
    (∑ i : Fin n,∑ k : Fin n,
      (coordinateDerivative i (fun y=>A y i k) x*G x k+A x i k*recoveredWeakHessian q A G J f x k i))= -f x := by
  let T := Finset.univ.erase (q,q)
  let P := fun p : Fin n×Fin n=>coordinateDerivative p.1 (fun y=>A y p.1 p.2) x*G x p.2+
    A x p.1 p.2*recoveredWeakHessian q A G J f x p.2 p.1
  have hs : (∑ p∈T,P p)=nonNormalDivergence q A G (nonNormalHessian q J) x := by
    apply Finset.sum_congr rfl
    intro p hp
    have hpne : p≠(q,q) := (Finset.mem_erase.mp hp).1
    have hor : p.1≠q ∨ p.2≠q := by
      by_contra hn
      simp only [not_or,not_not] at hn
      exact hpne (Prod.ext hn.1 hn.2)
    dsimp only [P]
    rw [recoveredWeakHessian_nonNormal q p.2 p.1 hor A G J f x ha]
  have hsplit := Finset.sum_erase_add Finset.univ P (Finset.mem_univ (q,q))
  change (∑ p∈T,P p)+P (q,q)=∑ p,P p at hsplit
  have hnormal : P (q,q)= -f x-nonNormalDivergence q A G (nonNormalHessian q J) x := by
    dsimp [P]
    rw [recoveredWeakHessian_normal]
    field_simp
    ring
  have he : (∑ i : Fin n,∑ k : Fin n,
      (coordinateDerivative i (fun y=>A y i k) x*G x k+A x i k*recoveredWeakHessian q A G J f x k i))=
      ∑ p : Fin n×Fin n,P p := by simp only [Fintype.sum_prod_type,P]
  rw [he,← hsplit,hs,hnormal]
  ring

end GaussianTilt.MomentMapLinearDirichlet
