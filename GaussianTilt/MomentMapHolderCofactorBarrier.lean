import GaussianTilt.MomentMapHolderCofactorEllipticity
import GaussianTilt.MomentMapHolderEllipticQuadraticBarrier

/-! # Constructed uniform C⁰ inverse bounds along the actual cofactor homotopy -/
noncomputable section
set_option maxHeartbeats 1000000
open Set Matrix
open scoped Topology BigOperators
namespace GaussianTilt.HolderSpace
open GaussianTilt.Letwin GaussianTilt.MomentMapRegularity GaussianTilt.MomentMapSchauder
variable {n : ℕ}

lemma cofactorHomotopy_operator_eq {S : Set (Coord (n := n))} (hS : Convex ℝ S) (α : ℝ)
    (j : Jet Coord ℝ hS α) (t : ℝ) :
    ellipticDirichletHomotopy hS α (identityFields S α)
      (cofactorFields S α (hessianFields hS α j)) t =
        ellipticDirichletOperator hS α (cofactorHomotopyFields hS α j t) := by
  apply ContinuousLinearMap.ext
  intro k
  apply value_injective S ℝ α
  apply BoundedContinuousFunction.ext
  intro x
  rw [ellipticDirichletHomotopy_apply_value, ellipticDirichletOperator_apply_value,
    value_cofactorHomotopyFields, value_identityFields]
  congr 2
  ext i l
  simp only [Matrix.add_apply, Matrix.smul_apply, value_cofactorFields]
  rfl

/-- Compactness and genuine positive stored Hessians provide one actual
supremum inverse constant for all linear homotopy parameters and all data. -/
theorem exists_cofactorHomotopy_uniform_c0_inverse [NeZero n]
    {S : Set (Coord (n := n))} (hS : Convex ℝ S) (hSc : IsCompact S)
    {α : ℝ} (hα : 0 < α) (j : Jet Coord ℝ hS α)
    (hpd : ∀ x : S, (hessianMatrix hS α j x).PosDef) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc (0 : ℝ) 1, ∀ k : zeroBoundary Coord ℝ hS α,
      ‖value S ℝ α (jetValue Coord ℝ hS α k.1)‖ ≤ B *
        ‖ellipticDirichletHomotopy hS α (identityFields S α)
          (cofactorFields S α (hessianFields hS α j)) t k‖ := by
  classical
  let i : Fin n := Classical.arbitrary (Fin n)
  obtain ⟨R₀, hR₀⟩ := hSc.exists_bound_of_continuousOn (continuous_apply i).continuousOn
  let R := max R₀ 0
  have hR : 0 ≤ R := le_max_right _ _
  have hstrip : ∀ x ∈ S, |x i| ≤ R := fun x hx => (hR₀ x hx).trans (le_max_left _ _)
  obtain ⟨lam, Λ, hlam, hΛ, hell⟩ := exists_cofactorHomotopy_uniform_ellipticity hS hSc α j hpd
  refine ⟨R^2/(2*lam), by positivity, ?_⟩
  intro t ht k
  let A := cofactorHomotopyFields hS α j t
  have hAmat (x : S) : coefficientExtension α A x =
      (1-t) • (1 : Matrix (Fin n) (Fin n) ℝ) + t • (hessianMatrix hS α j x).adjugate := by
    rw [coefficientExtension_mem]
    exact value_cofactorHomotopyFields hS α j t x
  have hAp (x : Coord) (hx : x ∈ interior S) : (coefficientExtension α A x).PosDef := by
    rw [hAmat ⟨x, interior_subset hx⟩]
    exact posDef_identity_homotopy (posDef_adjugate (hpd ⟨x, interior_subset hx⟩)) ht
  have hdiag (x : Coord) (hx : x ∈ interior S) : lam ≤ coefficientExtension α A x i i := by
    rw [hAmat ⟨x, interior_subset hx⟩]
    have hb := (hell t ht ⟨x, interior_subset hx⟩ (EuclideanSpace.basisFun (Fin n) ℝ i)).1
    simpa [euclideanQuadratic, EuclideanSpace.basisFun_apply, Matrix.mulVec, dotProduct, Pi.single_apply] using hb
  have hb := ellipticDirichletOperator_value_norm_le_quadratic hS hSc hα A hAp i hlam hR hdiag hstrip k
  rw [cofactorHomotopy_operator_eq]
  exact hb

end GaussianTilt.HolderSpace
