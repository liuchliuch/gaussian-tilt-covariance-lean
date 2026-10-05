import GaussianTilt.MomentMapClassicalDirichletBoundaryTangentIdentity

/-! # Compact positive determinant and inverse bounds for tangent blocks -/
noncomputable section
open Set Matrix
open scoped Topology ContDiff BigOperators Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

lemma exists_positive_det_and_inverse_bounds_on_compact
    {X ι : Type*} [TopologicalSpace X] [Fintype ι] [DecidableEq ι]
    {K : Set X} (hK : IsCompact K) {H : X → Matrix ι ι ℝ}
    (hc : ContinuousOn H K) (hp : ∀ x ∈ K, (H x).PosDef) :
    ∃ δ I : ℝ, 0 < δ ∧ 0 < I ∧ ∀ x ∈ K, δ ≤ (H x).det ∧ ∀ i j, |(H x)⁻¹ i j| ≤ I := by
  by_cases hne : K.Nonempty
  · have hdet : ContinuousOn (fun x => (H x).det) K :=
      continuous_id.matrix_det.comp_continuousOn hc
    obtain ⟨x,hx,hmin⟩ := hK.exists_isMinOn hne hdet
    have hinv : ContinuousOn (fun x => (H x)⁻¹) K := by
      intro y hy
      apply ContinuousAt.comp_continuousWithinAt _ (hc y hy)
      apply continuousAt_matrix_inv
      simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ (hp y hy).det_pos.ne'
    obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn hinv
    refine ⟨(H x).det,max M 1,(hp x hx).det_pos,zero_lt_one.trans_le (le_max_right _ _),?_⟩
    intro y hy
    refine ⟨hmin hy, fun i j => ?_⟩
    exact (Matrix.norm_entry_le_entrywise_sup_norm ((H y)⁻¹) (i:=i) (j:=j)).trans
      ((hM y hy).trans (le_max_left _ _))
  · refine ⟨1,1,by norm_num,by norm_num,?_⟩
    intro x hx
    exact (hne ⟨x,hx⟩).elim

/-- The scaled tangent block is uniformly nonsingular on a compact chart
and a positive multiplier interval. All bounds are obtained from its true
matrix field, including when the parameter interval is empty. -/
theorem exists_scaled_chartTangentBlock_bounds {w : CoordinateSpace n → ℝ}
    (hw : ContDiff ℝ ∞ w) (p : BoundaryChartPatch w)
    (hH : ∀ y ∈ Metric.closedBall p.center p.radius, (coordinateHessian w y).PosDef)
    {a b : ℝ} (ha : 0 < a) :
    ∃ δ I : ℝ, 0 < δ ∧ 0 < I ∧ ∀ y ∈ Metric.closedBall p.center p.radius,
      ∀ lam ∈ Icc a b, δ ≤ (lam • chartTangentBlock w p.index y).det ∧
        ∀ i j, |(lam • chartTangentBlock w p.index y)⁻¹ i j| ≤ I := by
  let K := Metric.closedBall p.center p.radius ×ˢ Icc a b
  let H := fun z : CoordinateSpace n × ℝ => z.2 • chartTangentBlock w p.index z.1
  have hK : IsCompact K := (isCompact_closedBall _ _).prod isCompact_Icc
  have hc : ContinuousOn H K := by
    exact continuous_snd.continuousOn.smul
      ((continuousOn_chartTangentBlock hw p).comp continuous_fst.continuousOn (fun _ h => h.1))
  have hp : ∀ z ∈ K, (H z).PosDef := fun z hz =>
    (chartTangentBlock_posDef (hH z.1 hz.1) p.index).smul (ha.trans_le hz.2.1)
  obtain ⟨δ,I,hδ,hI,hbound⟩ := exists_positive_det_and_inverse_bounds_on_compact hK hc hp
  exact ⟨δ,I,hδ,hI,fun y hy lam hlam => hbound (y,lam) ⟨hy,hlam⟩⟩

lemma exists_scaled_chartTangentBlock_entry_bound {w : CoordinateSpace n → ℝ}
    (hw : ContDiff ℝ ∞ w) (p : BoundaryChartPatch w) (a b : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ y ∈ Metric.closedBall p.center p.radius,
      ∀ lam ∈ Icc a b, ∀ i j, |(lam • chartTangentBlock w p.index y) i j| ≤ C := by
  let K := Metric.closedBall p.center p.radius ×ˢ Icc a b
  let H := fun z : CoordinateSpace n × ℝ => z.2 • chartTangentBlock w p.index z.1
  have hK : IsCompact K := (isCompact_closedBall _ _).prod isCompact_Icc
  have hc : ContinuousOn H K := continuous_snd.continuousOn.smul
    ((continuousOn_chartTangentBlock hw p).comp continuous_fst.continuousOn (fun _ h => h.1))
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨max M 1,zero_lt_one.trans_le (le_max_right _ _),?_⟩
  intro y hy lam hlam i j
  exact (Matrix.norm_entry_le_entrywise_sup_norm (H (y,lam)) (i:=i) (j:=j)).trans
    ((hM (y,lam) ⟨hy,hlam⟩).trans (le_max_left _ _))

namespace SmoothInnerDomain
variable {S A : Set (E n)} (d : SmoothInnerDomain S A)

lemma scaled_coordinate_tangent_block_bounds (p : BoundaryChartPatch d.coordinateDefining)
    {a b : ℝ} (ha : 0 < a) :
    ∃ δ I : ℝ, 0 < δ ∧ 0 < I ∧ ∀ y ∈ Metric.closedBall p.center p.radius,
      ∀ lam ∈ Icc a b, δ ≤ (lam • chartTangentBlock d.coordinateDefining p.index y).det ∧
        ∀ i j, |(lam • chartTangentBlock d.coordinateDefining p.index y)⁻¹ i j| ≤ I :=
  exists_scaled_chartTangentBlock_bounds d.coordinateDefining_smooth p
    (fun y _ => d.coordinateDefining_hessian_posDef y) ha

lemma scaled_coordinate_tangent_block_entry_bound (p : BoundaryChartPatch d.coordinateDefining)
    (a b : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ y ∈ Metric.closedBall p.center p.radius,
      ∀ lam ∈ Icc a b, ∀ i j, |(lam • chartTangentBlock d.coordinateDefining p.index y) i j| ≤ C :=
  exists_scaled_chartTangentBlock_entry_bound d.coordinateDefining_smooth p a b

/-- Uniform control of the actual unknown tangential block. The only
solution inputs are zero boundary data, C² regularity and the proved scaled
barriers; the multiplier and all block bounds are derived here. -/
theorem actual_coordinate_tangent_block_bounds (p : BoundaryChartPatch d.coordinateDefining)
    {a b : ℝ} (ha : 0 < a) :
    ∃ δ I C : ℝ, 0 < δ ∧ 0 < I ∧ 0 < C ∧
      ∀ (u : CoordinateSpace n → ℝ) (y : CoordinateSpace n),
      y ∈ Metric.closedBall p.center p.radius → d.coordinateDefining y = 0 →
      ContDiffAt ℝ 2 u y →
      (∀ z ∈ frontier {x | d.coordinateDefining x ≤ 0}, u z = 0) →
      (∀ z ∈ {x | d.coordinateDefining x ≤ 0}, b*d.coordinateDefining z ≤ u z ∧ u z ≤ a*d.coordinateDefining z) →
      (adaptedTangentBlock u d.coordinateDefining p.index y).PosDef ∧
      δ ≤ (adaptedTangentBlock u d.coordinateDefining p.index y).det ∧
      (∀ i j, |(adaptedTangentBlock u d.coordinateDefining p.index y)⁻¹ i j| ≤ I) ∧
      (∀ i j, |adaptedTangentBlock u d.coordinateDefining p.index y i j| ≤ C) := by
  obtain ⟨δ,I,hδ,hI,hInv⟩ := d.scaled_coordinate_tangent_block_bounds p (b:=b) ha
  obtain ⟨C,hC,hentry⟩ := d.scaled_coordinate_tangent_block_entry_bound p a b
  refine ⟨δ,I,C,hδ,hI,hC,?_⟩
  intro u y hyp hy hu hzero hbar
  have hyb : y ∈ frontier {x | d.coordinateDefining x ≤ 0} := by rw [d.coordinate_body_frontier]; exact hy
  have hj := p.derivative_ne_zero hyp
  let e := (coordinateDerivative p.index d.coordinateDefining y)⁻¹ •
    (Pi.single p.index 1 : CoordinateSpace n)
  have he : fderiv ℝ d.coordinateDefining y e = 1 := by
    simp only [e,map_smul,smul_eq_mul]
    exact inv_mul_cancel₀ hj
  have hw : ContDiffAt ℝ 2 d.coordinateDefining y := (contDiff_infty.mp d.coordinateDefining_smooth 2).contDiffAt
  have hlevel : ∀ᶠ z in 𝓝 y, d.coordinateDefining z = d.coordinateDefining y → u z = u y := by
    apply Filter.Eventually.of_forall
    intro z hz
    have hzb : z ∈ frontier {x | d.coordinateDefining x ≤ 0} := by rw [d.coordinate_body_frontier]; exact hz.trans hy
    rw [hzero z hzb,hzero y hyb]
  have hl := normal_multiplier_bounds_of_barriers (hu.differentiableAt (by norm_num))
    (hw.differentiableAt (by norm_num)) he (hzero y hyb) hy
    (Filter.Eventually.of_forall (fun z hz => hbar z (show d.coordinateDefining z ≤ 0 from hz.le)))
  have hblock := adaptedTangentBlock_eq_scalar_defining hu hw hj he hlevel
  rw [hblock]
  exact ⟨(chartTangentBlock_posDef (d.coordinateDefining_hessian_posDef y) p.index).smul (ha.trans_le hl.1),
    (hInv y hyp _ hl).1,(hInv y hyp _ hl).2,hentry y hyp _ hl⟩

end SmoothInnerDomain
end GaussianTilt.MomentMapRegularity
