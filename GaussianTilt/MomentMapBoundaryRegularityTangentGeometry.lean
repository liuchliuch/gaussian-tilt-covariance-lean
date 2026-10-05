import GaussianTilt.MomentMapBoundaryRegularityCoreHarnack

/-! # Actual tangent-ball geometry for the normal growth argument -/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

lemma coordinateClosedAnnulus_interior_outer {c x : CoordinateSpace n} {r R : ℝ}
    (hR : 0 < R) (hx : x ∈ interior (coordinateClosedAnnulus c r R)) :
    ‖(coordinateEquiv n).symm x-(coordinateEquiv n).symm c‖ < R := by
  let e := coordinateEquiv n
  have hs : coordinateClosedAnnulus c r R ⊆ e '' Metric.closedBall (e.symm c) R := by
    intro y hy
    exact ⟨e.symm y, by simpa only [Metric.mem_closedBall, dist_eq_norm] using hy.2, e.apply_symm_apply y⟩
  have hi := interior_mono hs hx
  change x ∈ interior (e.toHomeomorph '' Metric.closedBall (e.symm c) R) at hi
  rw [← e.toHomeomorph.image_interior, interior_closedBall _ hR.ne'] at hi
  obtain ⟨y,hy,rfl⟩ := hi
  simpa only [e.symm_apply_apply, Metric.mem_ball, dist_eq_norm] using hy

def flatTangentCenter (j : Fin n) (z : CoordinateSpace n) : CoordinateSpace n :=
  z+(1/8:ℝ) • (Pi.single j 1 : CoordinateSpace n)

lemma flatTangentCenter_coordinate (j : Fin n) {z : CoordinateSpace n} (hz : z j=0) :
    flatTangentCenter j z j = 1/8 := by simp [flatTangentCenter, hz]

lemma flatTangentCenter_norm (j : Fin n) {z : CoordinateSpace n}
    (hz : ‖(coordinateEquiv n).symm z‖ ≤ 1/4) :
    ‖(coordinateEquiv n).symm (flatTangentCenter j z)‖ ≤ 3/8 := by
  have hn := norm_add_le ((coordinateEquiv n).symm z) ((1/8:ℝ) • (coordinateEquiv n).symm ((Pi.single j 1 : CoordinateSpace n)))
  rw [norm_smul, euclidean_coordinate_single_norm] at hn
  norm_num at hn
  change ‖(coordinateEquiv n).symm z+(1/8:ℝ) • (coordinateEquiv n).symm (Pi.single j 1)‖ ≤ ‖(coordinateEquiv n).symm z‖+1/8 at hn
  simp only [flatTangentCenter,map_add,map_smul]
  linarith

lemma flat_tangent_sphere_outer (j : Fin n) {z y : CoordinateSpace n}
    (hz0 : z j=0) (hz : ‖(coordinateEquiv n).symm z‖ ≤ 1/4)
    (hy : ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm (flatTangentCenter j z)‖ ≤ 1/8) :
    ‖(coordinateEquiv n).symm y‖ ≤ 1/2 ∧ 0 ≤ y j := by
  have hn := norm_add_le ((coordinateEquiv n).symm y-(coordinateEquiv n).symm (flatTangentCenter j z))
    ((coordinateEquiv n).symm (flatTangentCenter j z))
  rw [sub_add_cancel] at hn
  have hc := abs_coordinate_le_euclidean_norm (y-flatTangentCenter j z) j
  simp only [Pi.sub_apply,map_sub,flatTangentCenter_coordinate j hz0] at hc
  exact ⟨by linarith [flatTangentCenter_norm j hz], by linarith [(abs_le.mp hc).1]⟩

lemma flat_tangent_annulus_interior (j : Fin n) {z y : CoordinateSpace n}
    (hz0 : z j=0) (hz : ‖(coordinateEquiv n).symm z‖ ≤ 1/4)
    (hy : y ∈ interior (coordinateClosedAnnulus (flatTangentCenter j z) (1/16) (1/8))) :
    y ∈ flatHalfBall j := by
  have hdist := coordinateClosedAnnulus_interior_outer (by norm_num : (0:ℝ)<1/8) hy
  have hn := flat_tangent_sphere_outer j hz0 hz hdist.le
  have hc := abs_coordinate_le_euclidean_norm (y-flatTangentCenter j z) j
  simp only [Pi.sub_apply,map_sub,flatTangentCenter_coordinate j hz0] at hc
  exact ⟨by linarith [hn.1], by linarith [(abs_le.mp hc).1]⟩

lemma flat_tangent_inner_sphere_core (j : Fin n) {z y : CoordinateSpace n}
    (hz0 : z j=0) (hz : ‖(coordinateEquiv n).symm z‖ ≤ 1/4)
    (hy : ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm (flatTangentCenter j z)‖ = 1/16) :
    y ∈ flatInteriorCore j := by
  have hn := flat_tangent_sphere_outer j (y := y) hz0 hz (by linarith [hy])
  have hc := abs_coordinate_le_euclidean_norm (y-flatTangentCenter j z) j
  simp only [Pi.sub_apply,map_sub,flatTangentCenter_coordinate j hz0,hy] at hc
  exact ⟨hn.1, by linarith [(abs_le.mp hc).1]⟩

lemma flat_normal_projection (j : Fin n) {x : CoordinateSpace n}
    (hx : ‖(coordinateEquiv n).symm x‖ ≤ 1/8) :
    let z := x-x j • (Pi.single j 1 : CoordinateSpace n)
    z j=0 ∧ ‖(coordinateEquiv n).symm z‖ ≤ 1/4 ∧
      ‖(coordinateEquiv n).symm x-(coordinateEquiv n).symm (flatTangentCenter j z)‖ = |x j-1/8| := by
  dsimp only
  refine ⟨by simp, ?_, ?_⟩
  · rw [map_sub,map_smul]
    have hn := norm_sub_le ((coordinateEquiv n).symm x) (x j • (coordinateEquiv n).symm ((Pi.single j 1 : CoordinateSpace n)))
    rw [norm_smul,euclidean_coordinate_single_norm] at hn
    norm_num at hn
    change ‖(coordinateEquiv n).symm x-x j • (coordinateEquiv n).symm (Pi.single j 1)‖ ≤ ‖(coordinateEquiv n).symm x‖+|x j| at hn
    linarith [abs_coordinate_le_euclidean_norm x j]
  · rw [← map_sub]
    have he : x-flatTangentCenter j (x-x j • (Pi.single j 1 : CoordinateSpace n)) = (x j-1/8) • (Pi.single j 1 : CoordinateSpace n) := by
      dsimp [flatTangentCenter]
      module
    rw [he,map_smul,norm_smul,euclidean_coordinate_single_norm]
    simp

end GaussianTilt.MomentMapRegularity
