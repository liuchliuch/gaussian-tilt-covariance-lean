import GaussianTilt.MomentMapSchauderInteriorJetInterpolation
import GaussianTilt.MomentMapHolderFixedExponentBounds

/-! # Homogeneous global norm control from values and the actual Hessian norm -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 2200000
open Set
open scoped Topology BoundedContinuousFunction
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.HolderSpace GaussianTilt.MomentMapElliptic
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Both lower-order moduli follow from the true within-domain derivatives.
A stronger Hessian exponent can then be lowered to the fixed Banach exponent
using the actual supremum bound; no compact-embedding shortcut is used. -/
theorem jet_norm_le_of_bounded_fields_homogeneous
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
    ‖j‖ ≤ 2*(U+G+H+C) := by
  let b := value S F δ (jetValue E F hS δ j)
  let D := value S (E →L[ℝ] F) δ (jetFirst E F hS δ j)
  let Q := value S (E →L[ℝ] E →L[ℝ] F) δ (jetSecond E F hS δ j)
  let K := 2*(U+G+H+C)
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



/-- A fixed interior ball and the true gradient FTC control all lower
fields on a compact convex body. The constant precedes the unknown jet,
and the estimate is homogeneous even when the data vanish. -/
theorem exists_global_jet_norm_bound {n : ℕ} {S : Set (KernelSpace n)}
    (hS : Convex ℝ S) (hSc : IsCompact S) (hint : (interior S).Nonempty)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (J : Jet (KernelSpace n) ℝ hS α) (U : ℝ), 0 ≤ U →
      (∀ x : S, |value S ℝ α (jetValue (KernelSpace n) ℝ hS α J) x| ≤ U) →
      ‖J‖ ≤ C*(U+‖jetSecond (KernelSpace n) ℝ hS α J‖) := by
  obtain ⟨a,ha⟩ := hint
  obtain ⟨R,hR,hball⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds ha)
  have hballS : Metric.closedBall a (R/2) ⊆ S :=
    ((Metric.closedBall_subset_ball (by linarith : R/2 < R)).trans hball).trans interior_subset
  obtain ⟨M0,hM0⟩ := hSc.exists_bound_of_continuousOn ((continuous_id.sub continuous_const).continuousOn :
    ContinuousOn (fun x : KernelSpace n => x-a) S)
  let M := max M0 0
  have hM : 0 ≤ M := le_max_right _ _
  let r := R/4
  have hr : 0 < r := by dsimp [r]; positivity
  let K := 1/r+r^α*r+M+1
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨2*(K+3),by positivity,?_⟩
  intro J U hU hu
  let D := jetFirst (KernelSpace n) ℝ hS α J
  let H := jetSecond (KernelSpace n) ℝ hS α J
  let Q := ‖H‖
  have hQ : 0 ≤ Q := norm_nonneg _
  let x : S := ⟨a,interior_subset ha⟩
  have hx : ‖(x : KernelSpace n)-a‖ ≤ (R/2)/2 := by simp only [x,sub_self,norm_zero]; positivity
  have hcenter := (interior_jet_derivative_interpolation hS hSc.isClosed ⟨a,ha⟩ (half_pos hR) hα hU
    hballS J hu hr (by dsimp [r]; linarith) x hx).1
  have hDb : ∀ y : S, ‖value S (KernelSpace n →L[ℝ] ℝ) α D y‖ ≤ K*(U+Q) := by
    intro y
    have hftc := (jet_ftc (KernelSpace n) ℝ hS α J x y).2
    have hs := segmentIntegralLinear_norm_bound hS α x y H
    have hs' : ‖value S (KernelSpace n →L[ℝ] ℝ) α D y-value S (KernelSpace n →L[ℝ] ℝ) α D x‖ ≤
        ‖(y : KernelSpace n)-x‖*Q := by
      rw [hftc]
      exact hs
    have hdist : ‖(y : KernelSpace n)-x‖ ≤ M := (hM0 y y.2).trans (le_max_left _ _)
    have hd := hs'.trans (mul_le_mul_of_nonneg_right hdist hQ)
    have htri : ‖value S (KernelSpace n →L[ℝ] ℝ) α D y‖ ≤
        ‖value S (KernelSpace n →L[ℝ] ℝ) α D y-value S (KernelSpace n →L[ℝ] ℝ) α D x‖+
        ‖value S (KernelSpace n →L[ℝ] ℝ) α D x‖ := by
      simpa only [sub_add_cancel] using norm_add_le
        (value S (KernelSpace n →L[ℝ] ℝ) α D y-value S (KernelSpace n →L[ℝ] ℝ) α D x)
        (value S (KernelSpace n →L[ℝ] ℝ) α D x)
    have hb : ‖value S (KernelSpace n →L[ℝ] ℝ) α D y‖ ≤ U/r+Q*r^α*r+M*Q := by
      dsimp only [D,H,Q] at hd ⊢
      linarith
    apply hb.trans
    have h1 : 1/r ≤ K := by
      dsimp [K]
      have hh : 0 ≤ r^α*r+M+1 := by positivity
      linarith
    have h2 : r^α*r+M ≤ K := by
      dsimp [K]
      have hh : 0 ≤ (1:ℝ)/r := by positivity
      linarith
    have h3 := mul_le_mul_of_nonneg_right h1 hU
    have h4 := mul_le_mul_of_nonneg_right h2 hQ
    calc
      U/r+Q*r^α*r+M*Q = (1/r)*U+(r^α*r+M)*Q := by ring
      _ ≤ K*U+K*Q := add_le_add h3 h4
      _ = K*(U+Q) := by ring
  have hnorm := jet_norm_le_of_bounded_fields_homogeneous hS hα hα1 le_rfl hU
    (show 0 ≤ K*(U+Q) by positivity) hQ hQ J
    (fun x => by simpa only [Real.norm_eq_abs] using hu x) hDb
    (fun x => norm_value_apply_le S _ α H x)
    (fun x y => norm_value_sub_le S _ α H x y)
  apply hnorm.trans
  have hcalc : 2*(U+K*(U+Q)+Q+Q) ≤ 2*(K+3)*(U+Q) := by nlinarith only [hU,hQ]
  exact hcalc

end GaussianTilt.MomentMapSchauder
