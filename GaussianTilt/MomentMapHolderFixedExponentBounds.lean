import GaussianTilt.MomentMapHolderJetBounds

/-! # Actual fixed Hölder jet norm from bounded fields and a stronger Hessian modulus -/
noncomputable section
set_option maxHeartbeats 1000000
open Set
open scoped Topology BoundedContinuousFunction
namespace GaussianTilt.HolderSpace
variable {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [MetricSpace X]

lemma holder_bound_of_bounded_and_higher_holder
    (f : X → F) {δ γ B H : ℝ} (hδ : 0 ≤ δ) (hδγ : δ ≤ γ) (hB : 0 ≤ B) (hH : 0 ≤ H)
    (hb : ∀ x, ‖f x‖ ≤ B) (hh : ∀ x y, ‖f x-f y‖ ≤ H*dist x y^γ) :
    ∀ x y, ‖f x-f y‖ ≤ max H (2*B)*dist x y^δ := by
  intro x y
  by_cases hd : dist x y ≤ 1
  · have hp := Real.rpow_le_rpow_of_exponent_ge' dist_nonneg hd hδ hδγ
    exact (hh x y).trans ((mul_le_mul_of_nonneg_left hp hH).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg dist_nonneg _)))
  · have hnorm : ‖f x-f y‖ ≤ 2*B := (norm_sub_le _ _).trans (by linarith [hb x, hb y])
    have hp := Real.one_le_rpow (le_of_not_ge hd) hδ
    exact hnorm.trans ((le_mul_of_one_le_right (by positivity : 0 ≤ 2*B) hp).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg dist_nonneg _)))

/-- Both lower-order moduli follow from the true within-domain derivatives.
A stronger Hessian exponent can then be lowered to the fixed Banach exponent
using the actual supremum bound; no compact-embedding shortcut is used. -/
theorem jet_norm_le_of_bounded_fields_and_higher_hessian
    {S : Set E} (hS : Convex ℝ S) {δ γ U G H C : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδγ : δ ≤ γ)
    (hU : 0 ≤ U) (hG : 0 ≤ G) (hH : 0 ≤ H) (hC : 0 ≤ C)
    (j : Jet E F hS δ)
    (hu : ∀ x : S, ‖value S F δ (jetValue E F hS δ j) x‖ ≤ U)
    (hD : ∀ x : S, ‖value S (E →L[ℝ] F) δ (jetFirst E F hS δ j) x‖ ≤ G)
    (hHH : ∀ x : S, ‖value S (E →L[ℝ] E →L[ℝ] F) δ (jetSecond E F hS δ j) x‖ ≤ H)
    (hholder : ∀ x y : S,
      ‖value S (E →L[ℝ] E →L[ℝ] F) δ (jetSecond E F hS δ j) x -
        value S (E →L[ℝ] E →L[ℝ] F) δ (jetSecond E F hS δ j) y‖ ≤ C*dist x y^γ) :
    ‖j‖ ≤ 2*(U+G+H+C+1) := by
  let b := value S F δ (jetValue E F hS δ j)
  let D := value S (E →L[ℝ] F) δ (jetFirst E F hS δ j)
  let Q := value S (E →L[ℝ] E →L[ℝ] F) δ (jetSecond E F hS δ j)
  let K := 2*(U+G+H+C+1)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hbn : ‖b‖ ≤ U := (BoundedContinuousFunction.norm_le hU).mpr hu
  have hDn : ‖D‖ ≤ G := (BoundedContinuousFunction.norm_le hG).mpr hD
  have hbLip (x y : S) : ‖b x-b y‖ ≤ G*dist x y := by
    have hm := hS.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun x hx => jet_hasFDerivWithinAt hS hδ j hx)
      (fun x hx => by rw [extendValue_mem δ _ hx]; exact hD ⟨x,hx⟩) y.2 x.2
    simpa only [b, D, extendValue_mem δ _ x.2, extendValue_mem δ _ y.2, Subtype.dist_eq, dist_eq_norm] using hm
  have hDLip (x y : S) : ‖D x-D y‖ ≤ H*dist x y := by
    have hm := hS.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun x hx => jet_first_hasFDerivWithinAt hS hδ j hx)
      (fun x hx => by rw [extendValue_mem δ _ hx]; exact hHH ⟨x,hx⟩) y.2 x.2
    simpa only [b, D, extendValue_mem δ _ x.2, extendValue_mem δ _ y.2, Subtype.dist_eq, dist_eq_norm] using hm
  have huNorm : ‖jetValue E F hS δ j‖ ≤ K := by
    apply norm_le_of_value_bounds hK _ (fun x => (hu x).trans (by dsimp [K]; linarith))
    intro x y
    have hh := holder_bound_of_bounded_lipschitz S b hδ.le hδ1 hG hbLip x y
    exact hh.trans (mul_le_mul_of_nonneg_right (max_le (by dsimp [K]; linarith) (by dsimp [K]; linarith))
      (Real.rpow_nonneg dist_nonneg _))
  have hDNorm : ‖jetFirst E F hS δ j‖ ≤ K := by
    apply norm_le_of_value_bounds hK _ (fun x => (hD x).trans (by dsimp [K]; linarith))
    intro x y
    have hh := holder_bound_of_bounded_lipschitz S D hδ.le hδ1 hH hDLip x y
    exact hh.trans (mul_le_mul_of_nonneg_right (max_le (by dsimp [K]; linarith) (by dsimp [K]; linarith))
      (Real.rpow_nonneg dist_nonneg _))
  have hQNorm : ‖jetSecond E F hS δ j‖ ≤ K := by
    apply norm_le_of_value_bounds hK _ (fun x => (hHH x).trans (by dsimp [K]; linarith))
    intro x y
    have hh := holder_bound_of_bounded_and_higher_holder Q hδ.le hδγ hH hC hHH hholder x y
    exact hh.trans (mul_le_mul_of_nonneg_right (max_le (by dsimp [K]; linarith) (by dsimp [K]; linarith))
      (Real.rpow_nonneg dist_nonneg _))
  exact norm_jet_le_of_field_norms hS j huNorm hDNorm hQNorm

end GaussianTilt.HolderSpace
