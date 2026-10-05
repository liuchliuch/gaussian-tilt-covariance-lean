import GaussianTilt.MomentMapBoundaryRegularityHarnackChain
import GaussianTilt.MomentMapBoundaryRegularityHopfBarrier

/-! # Explicit interior geometry for a flat boundary patch -/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

def flatHalfBall (j : Fin n) : Set (CoordinateSpace n) :=
  {x | ‖(coordinateEquiv n).symm x‖ < 1 ∧ 0 < x j}

def flatInteriorCore (j : Fin n) : Set (CoordinateSpace n) :=
  {x | ‖(coordinateEquiv n).symm x‖ ≤ 1/2 ∧ 1/16 ≤ x j}

def flatInteriorStrip (j : Fin n) : Set (CoordinateSpace n) :=
  {x | ‖(coordinateEquiv n).symm x‖ < 3/4 ∧ 1/32 < x j}

lemma abs_coordinate_le_euclidean_norm (x : CoordinateSpace n) (j : Fin n) :
    |x j| ≤ ‖(coordinateEquiv n).symm x‖ :=
  PiLp.norm_apply_le ((coordinateEquiv n).symm x) j

lemma euclidean_coordinate_single_norm (j : Fin n) (t : ℝ) :
    ‖(coordinateEquiv n).symm (Pi.single j t)‖ = |t| := by
  change ‖EuclideanSpace.single j t‖ = |t|
  simp

lemma flatInteriorCore_convex (j : Fin n) : Convex ℝ (flatInteriorCore j) := by
  intro x hx y hy a b ha hb hab
  constructor
  · have ht := norm_add_le (a • (coordinateEquiv n).symm x) (b • (coordinateEquiv n).symm y)
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb] at ht
    change ‖(coordinateEquiv n).symm (a • x+b • y)‖ ≤ 1/2
    rw [map_add,map_smul,map_smul]
    nlinarith [mul_le_mul_of_nonneg_left hx.1 ha,mul_le_mul_of_nonneg_left hy.1 hb]
  · change 1/16 ≤ a*x j+b*y j
    nlinarith [mul_le_mul_of_nonneg_left hx.2 ha,mul_le_mul_of_nonneg_left hy.2 hb]

lemma flatInteriorCore_tube (j : Fin n) {x y : CoordinateSpace n}
    (hx : x ∈ flatInteriorCore j) (hy : y ∈ flatInteriorCore j) :
    ∀ z ∈ segment ℝ x y, ∀ w,
      ‖(coordinateEquiv n).symm w-(coordinateEquiv n).symm z‖ < 2*(1/64:ℝ) → w ∈ flatInteriorStrip j := by
  intro z hz w hw
  have hzC := (flatInteriorCore_convex j).segment_subset hx hy hz
  have htri := norm_add_le ((coordinateEquiv n).symm w-(coordinateEquiv n).symm z) ((coordinateEquiv n).symm z)
  rw [sub_add_cancel] at htri
  have hcoord := abs_coordinate_le_euclidean_norm (w-z) j
  simp only [Pi.sub_apply,map_sub] at hcoord
  refine ⟨by change ‖(coordinateEquiv n).symm w‖ < 3/4; linarith [hzC.1], ?_⟩
  change 1/32 < w j
  have habs := (abs_le.mp hcoord).1
  linarith [hzC.2]

lemma flatInteriorStrip_subset (j : Fin n) : flatInteriorStrip j ⊆ flatHalfBall j := by
  intro x hx
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

lemma flat_corkscrew_mem_core (j : Fin n) : Pi.single j (1/4:ℝ) ∈ flatInteriorCore j := by
  constructor
  · rw [euclidean_coordinate_single_norm]
    norm_num
  · norm_num

lemma flat_core_distance_le_one (j : Fin n) {x y : CoordinateSpace n}
    (hx : x ∈ flatInteriorCore j) (hy : y ∈ flatInteriorCore j) :
    ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm x‖ ≤ 1 := by
  have ht := norm_sub_le ((coordinateEquiv n).symm y) ((coordinateEquiv n).symm x)
  linarith [hx.1,hy.1]

end GaussianTilt.MomentMapRegularity
