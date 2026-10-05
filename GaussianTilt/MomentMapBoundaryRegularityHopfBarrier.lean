import GaussianTilt.MomentMapBoundaryRegularityHopfCalculus

/-! # Actual annular comparison and quantitative normal-ray Hopf growth -/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

def coordinateClosedAnnulus (c : CoordinateSpace n) (r R : ℝ) : Set (CoordinateSpace n) :=
  {x | r ≤ ‖(coordinateEquiv n).symm x - (coordinateEquiv n).symm c‖ ∧
    ‖(coordinateEquiv n).symm x - (coordinateEquiv n).symm c‖ ≤ R}

lemma isCompact_coordinateClosedAnnulus (c : CoordinateSpace n) (r R : ℝ) :
    IsCompact (coordinateClosedAnnulus c r R) := by
  let e := coordinateEquiv n
  have he : coordinateClosedAnnulus c r R =
      e '' (Metric.closedBall (e.symm c) R ∩ {y | r ≤ ‖y-e.symm c‖}) := by
    ext x
    constructor
    · intro hx
      exact ⟨e.symm x, ⟨by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx.2, hx.1⟩, e.apply_symm_apply x⟩
    · rintro ⟨y,hy,rfl⟩
      constructor
      · simpa only [e.symm_apply_apply] using hy.2
      · simpa only [e.symm_apply_apply, Metric.mem_closedBall, dist_eq_norm] using hy.1
  rw [he]
  exact ((isCompact_closedBall _ _).inter_right
    (isClosed_le continuous_const ((continuous_id.sub continuous_const).norm))).image e.continuous

lemma coordinateClosedAnnulus_frontier_radii (c : CoordinateSpace n) (r R : ℝ)
    {x : CoordinateSpace n} (hx : x ∈ frontier (coordinateClosedAnnulus c r R)) :
    ‖(coordinateEquiv n).symm x - (coordinateEquiv n).symm c‖ = r ∨
      ‖(coordinateEquiv n).symm x - (coordinateEquiv n).symm c‖ = R := by
  have hxS := (isCompact_coordinateClosedAnnulus c r R).isClosed.frontier_subset hx
  by_contra hh
  push_neg at hh
  have hr : r < ‖(coordinateEquiv n).symm x - (coordinateEquiv n).symm c‖ := lt_of_le_of_ne hxS.1 hh.1.symm
  have hR : ‖(coordinateEquiv n).symm x - (coordinateEquiv n).symm c‖ < R := lt_of_le_of_ne hxS.2 hh.2
  have hn : Continuous (fun y : CoordinateSpace n => ‖(coordinateEquiv n).symm y - (coordinateEquiv n).symm c‖) :=
    ((coordinateEquiv n).symm.continuous.sub continuous_const).norm
  have hnear : coordinateClosedAnnulus c r R ∈ 𝓝 x := by
    filter_upwards [hn.continuousAt.eventually (eventually_gt_nhds hr),
      hn.continuousAt.eventually (eventually_lt_nhds hR)] with y hyr hyR
    exact ⟨hyr.le,hyR.le⟩
  exact hx.2 (mem_interior_iff_mem_nhds.mpr hnear)

/-- An explicit exponential barrier propagates a positive lower bound
from the inner sphere to the full annulus, including bounded forcing. -/
theorem hopf_annulus_lower_bound [NeZero n]
    (c : CoordinateSpace n) {r R a lam N m : ℝ}
    (hr : 0 ≤ r) (ha : 0 < a) (hlam : 0 ≤ lam) (hm : 0 ≤ m)
    (hsize : 2*N+1 ≤ 4*a*lam*r^2)
    {v : CoordinateSpace n → ℝ}
    (hvc : ContinuousOn v (coordinateClosedAnnulus c r R))
    (hv : ∀ y ∈ interior (coordinateClosedAnnulus c r R), ContDiffAt ℝ 2 v y)
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ y ∈ interior (coordinateClosedAnnulus c r R), (A y).PosDef)
    (hlo : ∀ y ∈ interior (coordinateClosedAnnulus c r R),
      lam * ‖(coordinateEquiv n).symm (y-c)‖^2 ≤ (y-c) ⬝ᵥ (A y *ᵥ (y-c)))
    (htrace : ∀ y ∈ interior (coordinateClosedAnnulus c r R), (A y).trace ≤ N)
    (hLv : ∀ y ∈ interior (coordinateClosedAnnulus c r R),
      linearizedMA (A y) v y ≤ m*a*Real.exp (-a*R^2))
    (hinner : ∀ y, ‖(coordinateEquiv n).symm y - (coordinateEquiv n).symm c‖ = r → m ≤ v y)
    (houter : ∀ y, ‖(coordinateEquiv n).symm y - (coordinateEquiv n).symm c‖ = R → 0 ≤ v y) :
    ∀ x ∈ coordinateClosedAnnulus c r R, m * hopfExponentialBarrier c a R x ≤ v x := by
  have hB := contDiff_infty.mp (contDiff_hopfExponentialBarrier c a R) 2
  have hh := classical_dirichlet_maximum_principle (f := fun z => m*hopfExponentialBarrier c a R z-v z)
    (isCompact_coordinateClosedAnnulus c r R)
    ((continuousOn_const.mul hB.continuous.continuousOn).sub hvc)
    (fun y hy => (contDiffAt_const.mul hB.contDiffAt).sub (hv y hy)) hA
  have hP : ∀ y ∈ interior (coordinateClosedAnnulus c r R),
      0 ≤ linearizedMA (A y) (fun z => m*hopfExponentialBarrier c a R z-v z) y := by
    intro y hy
    have hyS := interior_subset hy
    have hl := hopfExponentialBarrier_forcing_lower c y ha hr hlam (hlo y hy) (htrace y hy) hyS.1 hyS.2 hsize
    have hmL := mul_le_mul_of_nonneg_left hl hm
    rw [linearizedMA_sub_at _ (contDiffAt_const.mul hB.contDiffAt) (hv y hy),
      linearizedMA_const_mul_at _ hB.contDiffAt]
    nlinarith [hLv y hy]
  have hb : ∀ y ∈ frontier (coordinateClosedAnnulus c r R), m*hopfExponentialBarrier c a R y-v y ≤ 0 := by
    intro y hy
    rcases coordinateClosedAnnulus_frontier_radii c r R hy with hyr | hyR
    · have hB1 : hopfExponentialBarrier c a R y ≤ 1 := by
        rw [hopfExponentialBarrier_eq_norm, hyr]
        have he : Real.exp (-a*r^2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg r])
        linarith [Real.exp_pos (-a*R^2)]
      have hmb := mul_le_mul_of_nonneg_left hB1 hm
      linarith [hinner y hyr]
    · rw [hopfExponentialBarrier_eq_norm, hyR, sub_self, mul_zero]
      simpa only [zero_sub] using neg_nonpos.mpr (houter y hyR)
  intro x hx
  have he := hh hP hb x hx
  linarith

/-- The barrier has a quantitative linear lower bound on inward normal
rays. The constant is explicit and independent of the tested solution. -/
lemma hopf_exponential_normal_growth {a R t : ℝ} (ha : 0 ≤ a) (hR : 0 ≤ R)
    (ht : 0 ≤ t) (htR : t ≤ R) :
    a * R * Real.exp (-a*R^2) * t ≤
      Real.exp (-a*(R-t)^2) - Real.exp (-a*R^2) := by
  have hdiff : a*R*t ≤ a*(R^2-(R-t)^2) := by
    nlinarith [mul_nonneg ha (mul_nonneg ht (sub_nonneg.mpr htR))]
  have he := Real.add_one_le_exp (a*(R^2-(R-t)^2))
  have hm := mul_le_mul_of_nonneg_left (hdiff.trans (by linarith : a*(R^2-(R-t)^2) ≤
      Real.exp (a*(R^2-(R-t)^2))-1)) (Real.exp_pos (-a*R^2)).le
  have hexp : Real.exp (-a*R^2) * Real.exp (a*(R^2-(R-t)^2)) = Real.exp (-a*(R-t)^2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [mul_sub, hexp, mul_one] at hm
  nlinarith

end GaussianTilt.MomentMapRegularity
