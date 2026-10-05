import GaussianTilt.MomentMapClassicalDirichletSchurContinuity
import GaussianTilt.MomentMapClassicalDirichletNormalCoordinates

/-! # Actual normal-normal Hölder recovery in the original coordinates -/
noncomputable section
open Set Matrix
open scoped BigOperators
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

lemma coordinate_normalBlockMatrix_det {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.IsSymm) (j : Fin n) (β : {i : Fin n // i ≠ j} → ℝ) :
    (normalBlockMatrix (coordinateTangentBlock H j β)
      (fun a : {i : Fin n // i ≠ j} => H a j-β a*H j j) (H j j)).det = H.det := by
  rw [coordinateTangentBlock_eq hH]
  have hb : (fun a : {i : Fin n // i ≠ j} => H a j-β a*H j j) =
      (fun a : {i : Fin n // i ≠ j} => H a j) - (H j j) • β := by
    ext a
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    ring
  rw [hb,normalBlockMatrix_tangential_det]
  change (normalBlockMatrix (fun a b : {i : Fin n // i ≠ j} => H a b)
    (fun a => H a j) (H j j)).det = H.det
  exact normalBlockMatrix_coordinate_det hH j

/-- The normal-normal modulus is derived in the original coordinate chart.
The determinant-preserving tangent shear is an actual proved identity. -/
theorem coordinate_normal_hessian_holder
    {X : Type*} [PseudoMetricSpace X] {S : Set X}
    (j : Fin n) {H : X → Matrix (Fin n) (Fin n) ℝ}
    {β : X → {i : Fin n // i ≠ j} → ℝ} {δ I K M F L α : ℝ}
    (hδ : 0 < δ) (hI : 0 ≤ I) (hK : 0 ≤ K) (hM : 0 ≤ M) (hF : 0 ≤ F) (hL : 0 ≤ L)
    (hsym : ∀ x ∈ S, (H x).IsSymm)
    (hp : ∀ x ∈ S, (coordinateTangentBlock (H x) j (β x)).PosDef)
    (hd : ∀ x ∈ S, δ ≤ (coordinateTangentBlock (H x) j (β x)).det)
    (hA : ∀ x ∈ S, ∀ a b, |coordinateTangentBlock (H x) j (β x) a b| ≤ M)
    (hInv : ∀ x ∈ S, ∀ a b, |(coordinateTangentBlock (H x) j (β x))⁻¹ a b| ≤ I)
    (hb : ∀ x ∈ S, ∀ a : {i : Fin n // i ≠ j}, |H x a j-β x a*H x j j| ≤ K)
    (hdet : ∀ x ∈ S, |(H x).det| ≤ F)
    (hAH : ∀ x ∈ S, ∀ y ∈ S, ∀ a b,
      |coordinateTangentBlock (H x) j (β x) a b-coordinateTangentBlock (H y) j (β y) a b| ≤ L*dist x y^α)
    (hbH : ∀ x ∈ S, ∀ y ∈ S, ∀ a : {i : Fin n // i ≠ j},
      |(H x a j-β x a*H x j j)-(H y a j-β y a*H y j j)| ≤ L*dist x y^α)
    (hfH : ∀ x ∈ S, ∀ y ∈ S, |(H x).det-(H y).det| ≤ L*dist x y^α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ S, ∀ y ∈ S, |H x j j-H y j j| ≤ C*dist x y^α := by
  apply normalBlockMatrix_normal_holder hδ hI hK hM hF hL hp hd hA hInv hb
  · intro x hx
    rw [coordinate_normalBlockMatrix_det (hsym x hx)]
    exact hdet x hx
  · exact hAH
  · exact hbH
  · intro x hx y hy
    rw [coordinate_normalBlockMatrix_det (hsym x hx),coordinate_normalBlockMatrix_det (hsym y hy)]
    exact hfH x hx y hy

end GaussianTilt.MomentMapRegularity
