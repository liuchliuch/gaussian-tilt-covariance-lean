import GaussianTilt.MomentMapSchauderGlobalBoundaryChart
import GaussianTilt.MomentMapSchauderBoundaryPatchGeometry

/-! # Actual physical neighborhoods and half-ball geometry of the boundary chart -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapLinearDirichlet
variable {n : ℕ}

lemma boundary_inverse_maps_halfball {w : KernelSpace n → ℝ} {a : KernelSpace n}
    {j : Fin n} {s : ℝ} (hs : 0 < s) (ha : w a=0)
    {ψ : KernelSpace n → KernelSpace n}
    (hlevel : ∀ z ∈ Metric.closedBall (0 : KernelSpace n) 1, w (ψ z)=w a-s*z j) :
    MapsTo ψ (flatClosedPatch j 1) {x | w x ≤ 0} := by
  intro z hz
  change w (ψ z) ≤ 0
  rw [hlevel z hz.1,ha,zero_sub]
  exact neg_nonpos.mpr (mul_nonneg hs.le hz.2)

lemma boundary_inverse_maps_interior {w : KernelSpace n → ℝ} {a : KernelSpace n}
    {j : Fin n} {s : ℝ} (hs : 0 < s) (ha : w a=0)
    {ψ : KernelSpace n → KernelSpace n}
    (hlevel : ∀ z ∈ Metric.closedBall (0 : KernelSpace n) 1, w (ψ z)=w a-s*z j)
    (hinterior : interior {x | w x ≤ 0}={x | w x < 0}) :
    MapsTo ψ (interior (flatClosedPatch j 1)) (interior {x | w x ≤ 0}) := by
  intro z hz
  rw [hinterior]
  change w (ψ z) < 0
  rw [hlevel z (interior_subset hz).1,ha,zero_sub]
  exact neg_neg_of_pos (mul_pos hs (flatClosedPatch_interior_normal_pos hz))

lemma boundary_inverse_plane_mem_frontier {w : KernelSpace n → ℝ}
    (hw : Continuous w) {a : KernelSpace n} {j : Fin n} {s : ℝ} (ha : w a=0)
    {ψ : KernelSpace n → KernelSpace n}
    (hlevel : ∀ z ∈ Metric.closedBall (0 : KernelSpace n) 1, w (ψ z)=w a-s*z j)
    (hinterior : interior {x | w x ≤ 0}={x | w x < 0})
    {z : KernelSpace n} (hz : z ∈ flatClosedPatch j 1) (hzj : z j=0) :
    ψ z ∈ frontier {x | w x ≤ 0} := by
  have he : w (ψ z)=0 := by rw [hlevel z hz.1,ha,hzj,mul_zero,sub_zero]
  rw [frontier,(isClosed_le hw continuous_const).closure_eq,hinterior]
  exact ⟨he.le,not_lt.mpr he.ge⟩

/-- A fixed positive physical radius is chosen before every small
absorption coefficient and unknown jet. Both closed and interior points
map into the genuine smaller half-ball. -/
theorem exists_physical_boundary_patch {w : KernelSpace n → ℝ} (hw : ContDiff ℝ ∞ w)
    (a : KernelSpace n) (j : Fin n)
    (hj : fderiv ℝ w a (EuclideanSpace.basisFun (Fin n) ℝ j)≠0)
    {s ρ : ℝ} (hs : 0 < s) (hρ : 0 < ρ) (ha : w a=0)
    (hinterior : interior {x | w x ≤ 0}={x | w x < 0}) :
    ∃ r : ℝ, 0 < r ∧
      Metric.closedBall a (2*r) ⊆ (regularLevelFlatteningChart hw a j hj).source ∧
      (∀ x ∈ Metric.closedBall a (2*r), ‖scaledFlatteningMap w a j s x‖ < ρ) ∧
      MapsTo (scaledFlatteningMap w a j s) ({x | w x ≤ 0} ∩ Metric.closedBall a (2*r)) (flatClosedPatch j ρ) ∧
      MapsTo (scaledFlatteningMap w a j s) (interior {x | w x ≤ 0} ∩ Metric.closedBall a (2*r)) (interior (flatClosedPatch j ρ)) := by
  let U := (regularLevelFlatteningChart hw a j hj).source ∩ (scaledFlatteningMap w a j s) ⁻¹' Metric.ball 0 ρ
  have hU : IsOpen U := (regularLevelFlatteningChart hw a j hj).open_source.inter
    (Metric.isOpen_ball.preimage (contDiff_scaledFlatteningMap hw a j s).continuous)
  have haU : a ∈ U := ⟨regularLevelFlatteningChart_source hw a j hj,
    by simpa only [mem_preimage,scaledFlatteningMap_self,Metric.mem_ball,dist_self] using hρ⟩
  obtain ⟨q,hq,hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds haU)
  let r := q/4
  have hr : 0 < r := by dsimp [r]; positivity
  have hb : Metric.closedBall a (2*r) ⊆ U :=
    (Metric.closedBall_subset_ball (by dsimp [r]; linarith : 2*r < q)).trans hball
  have hn : ∀ x ∈ Metric.closedBall a (2*r), ‖scaledFlatteningMap w a j s x‖ < ρ := by
    intro x hx
    simpa only [mem_preimage,Metric.mem_ball,dist_zero_right] using (hb hx).2
  refine ⟨r,hr,fun x hx => (hb hx).1,?_,?_,?_⟩
  · intro x hx
    simpa only [mem_preimage,Metric.mem_ball,dist_zero_right] using (hb hx).2
  · intro x hx
    refine ⟨by simpa only [Metric.mem_closedBall,dist_zero_right] using (hn x hx.2).le,?_⟩
    change 0 ≤ scaledFlatteningMap w a j s x j
    rw [scaledFlatteningMap_normal,ha,sub_zero]
    exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hs.le) hx.1)
  · intro x hx
    apply flatClosedPatch_mem_interior (hn x hx.2)
    rw [scaledFlatteningMap_normal,ha,sub_zero]
    have hxw : w x < 0 := by simpa only [hinterior,mem_setOf_eq] using hx.1
    exact neg_pos.mpr (mul_neg_of_pos_of_neg (inv_pos.mpr hs) hxw)

end GaussianTilt.MomentMapSchauder
