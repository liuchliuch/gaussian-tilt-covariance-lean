import GaussianTilt.MomentMapClassicalDirichletIntrinsicFirstOrder
import GaussianTilt.MomentMapClassicalDirichletBoundaryTangentBounds
import GaussianTilt.MomentMapClassicalDirichletNormalCoordinates

/-! # Genuine tangential Hessian bounds for intrinsic Dirichlet jets -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 500000
open Set Filter Matrix
open scoped Topology ContDiff BigOperators
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin GaussianTilt.HolderSpace
variable {n : ℕ}

lemma coordinateTangentBlock_apply_chart
    (H : Matrix (Fin n) (Fin n) ℝ) (w : CoordinateSpace n → ℝ) (j : Fin n)
    (x : CoordinateSpace n) (a b : TangentIndex j) :
    coordinateTangentBlock H j (fun l => boundaryChartCoefficient w j l x) a b =
      chartTangentVector w j a x ⬝ᵥ (H *ᵥ chartTangentVector w j b x) := by
  simp only [chartTangentVector,Matrix.mulVec_sub,Matrix.mulVec_smul,sub_dotProduct,
    smul_dotProduct,dotProduct_sub,dotProduct_smul,Matrix.mulVec_single_one,
    single_dotProduct,one_mul,Matrix.col_apply,smul_eq_mul,coordinateTangentBlock]
  ring

namespace SmoothInnerDomain
variable {S A : Set (E n)} (d : SmoothInnerDomain S A)

/-- The actual intrinsic tangent block equals a positive scalar multiple of
the fixed defining block. This uses within-domain boundary jets throughout. -/
theorem intrinsic_tangent_block_eq_scalar_defining {α a b : ℝ} (hα : 0 < α)
    (j : zeroBoundary (CoordinateSpace n) ℝ d.coordinate_body_convex α)
    (p : BoundaryChartPatch d.coordinateDefining) {x : CoordinateSpace n}
    (hxp : x ∈ Metric.closedBall p.center p.radius) (hx0 : d.coordinateDefining x = 0)
    (hbar : ∀ y ∈ {z | d.coordinateDefining z ≤ 0},
      b*d.coordinateDefining y ≤ intrinsicValue d.coordinate_body_convex α j.1 y ∧
      intrinsicValue d.coordinate_body_convex α j.1 y ≤ a*d.coordinateDefining y) :
    ∃ lam : ℝ, a ≤ lam ∧ lam ≤ b ∧
      coordinateTangentBlock (intrinsicHessian d.coordinate_body_convex α j.1 x) p.index
        (fun l => boundaryChartCoefficient d.coordinateDefining p.index l x) =
        lam • chartTangentBlock d.coordinateDefining p.index x := by
  have hxb : x ∈ frontier {y | d.coordinateDefining y ≤ 0} := by rwa [d.coordinate_body_frontier]
  have hxs := d.coordinate_body_compact.isClosed.frontier_subset hxb
  obtain ⟨lam,hla,hlb,hfirst,hsecond⟩ := d.intrinsic_boundary_jet_data hα j hxb hbar
  have hw : ContDiffAt ℝ 2 d.coordinateDefining x := (contDiff_infty.mp d.coordinateDefining_smooth 2).contDiffAt
  refine ⟨lam,hla,hlb,?_⟩
  ext a b
  rw [coordinateTangentBlock_apply_chart]
  have he := intrinsicHessian_eq_stored d.coordinate_body_convex α j.1 ⟨x,hxs⟩
  change intrinsicHessian d.coordinate_body_convex α j.1 x = _ at he
  rw [he,← intrinsicSecond_bilinear_eq_reverse_hessian]
  rw [hsecond _ _ (chartTangentVector_tangent (p.derivative_ne_zero hxp) b)
    (chartTangentVector_tangent (p.derivative_ne_zero hxp) a)]
  rw [hw.isSymmSndFDerivAt (by norm_num) (chartTangentVector d.coordinateDefining p.index b x)
    (chartTangentVector d.coordinateDefining p.index a x)]
  rw [Matrix.smul_apply,chartTangentBlock_apply hw]
  rfl

/-- Uniform determinant, inverse and entry bounds for the actual intrinsic
tangential block, obtained from the fixed defining domain and the barriers. -/
theorem intrinsic_tangent_block_bounds {α a b : ℝ} (hα : 0 < α) (ha : 0 < a)
    (p : BoundaryChartPatch d.coordinateDefining) :
    ∃ δ I T : ℝ, 0 < δ ∧ 0 < I ∧ 0 < T ∧
      ∀ j : zeroBoundary (CoordinateSpace n) ℝ d.coordinate_body_convex α,
      ∀ x ∈ Metric.closedBall p.center p.radius, d.coordinateDefining x = 0 →
      (∀ y ∈ {z | d.coordinateDefining z ≤ 0},
        b*d.coordinateDefining y ≤ intrinsicValue d.coordinate_body_convex α j.1 y ∧
        intrinsicValue d.coordinate_body_convex α j.1 y ≤ a*d.coordinateDefining y) →
      let B := coordinateTangentBlock (intrinsicHessian d.coordinate_body_convex α j.1 x) p.index
        (fun l => boundaryChartCoefficient d.coordinateDefining p.index l x)
      B.PosDef ∧ δ ≤ B.det ∧ (∀ i l, |B⁻¹ i l| ≤ I) ∧ (∀ i l, |B i l| ≤ T) := by
  obtain ⟨δ,I,hδ,hI,hInv⟩ := d.scaled_coordinate_tangent_block_bounds p (b := b) ha
  obtain ⟨T,hT,hentry⟩ := d.scaled_coordinate_tangent_block_entry_bound p a b
  refine ⟨δ,I,T,hδ,hI,hT,?_⟩
  intro j x hxp hx0 hbar
  obtain ⟨lam,hla,hlb,he⟩ := d.intrinsic_tangent_block_eq_scalar_defining hα j p hxp hx0 hbar
  dsimp only
  rw [he]
  exact ⟨(chartTangentBlock_posDef (d.coordinateDefining_hessian_posDef x) p.index).smul (ha.trans_le hla),
    (hInv x hxp lam ⟨hla,hlb⟩).1,(hInv x hxp lam ⟨hla,hlb⟩).2,hentry x hxp lam ⟨hla,hlb⟩⟩

end SmoothInnerDomain
end GaussianTilt.MomentMapRegularity
