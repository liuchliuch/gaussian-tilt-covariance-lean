import GaussianTilt.MomentMapLinearDirichletTangentialDifferenceCutoff
import GaussianTilt.MomentMapBoundaryRegularityFlatGeometry

/-! # Actual geometric margins for tangential difference quotients -/
noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory Set Filter Matrix
open scoped Topology ContDiff BigOperators ENNReal NNReal Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapRegularity
variable {n : ℕ}

lemma euclidean_norm_coordinate_translate_le (x : CoordinateSpace n) (i : Fin n) (h : ℝ) :
    ‖(coordinateEquiv n).symm (x+h • (Pi.single i 1 : CoordinateSpace n))‖≤
      ‖(coordinateEquiv n).symm x‖+|h| := by
  rw [map_add,map_smul]
  simpa only [norm_smul,Real.norm_eq_abs,euclidean_coordinate_single_norm,abs_one,mul_one] using
    norm_add_le ((coordinateEquiv n).symm x) (h • (coordinateEquiv n).symm (Pi.single i 1))

lemma tangential_translate_coordinate (q i : Fin n) (hi : i≠q) (x : CoordinateSpace n) (h : ℝ) :
    (x+h • (Pi.single i 1 : CoordinateSpace n)) q=x q := by simp [Ne.symm hi]

lemma tangential_halfBall_shift_subset (q i : Fin n) (hi : i≠q) {r R h : ℝ}
    (hh : |h|<R-r) :
    (fun x : CoordinateSpace n=>x+((-h) • (Pi.single i 1 : CoordinateSpace n))) ⁻¹'
      coordinateHalfBall q r ⊆ coordinateHalfBall q R := by
  intro x hx
  have hb := euclidean_norm_coordinate_translate_le
    (x+((-h) • (Pi.single i 1 : CoordinateSpace n))) i h
  have he : x+((-h) • (Pi.single i 1 : CoordinateSpace n))+h • (Pi.single i 1 : CoordinateSpace n)=x := by
    rw [neg_smul]
    abel
  rw [he] at hb
  refine ⟨?_,?_⟩
  · change ‖(coordinateEquiv n).symm x‖<R
    have hn := hx.1
    change ‖(coordinateEquiv n).symm (x+((-h) • (Pi.single i 1 : CoordinateSpace n)))‖<r at hn
    linarith
  · simpa only [tangential_translate_coordinate q i hi x (-h)] using hx.2

lemma coordinate_translate_mem_outer_closedBall {r R h : ℝ} (hh : |h|<R-r)
    {x : CoordinateSpace n} (hx : x∈rawChartBall r) (i : Fin n) :
    x+h • (Pi.single i 1 : CoordinateSpace n) ∈ rawChartClosedBall R := by
  have hb := euclidean_norm_coordinate_translate_le x i h
  change ‖(coordinateEquiv n).symm x‖<r at hx
  change ‖(coordinateEquiv n).symm (x+h • (Pi.single i 1 : CoordinateSpace n))‖≤R
  linarith

/-- Local matrix Lipschitz data imply the actual coefficient quotient
bound on the smaller ball; no Lipschitz extension is assumed. -/
lemma local_matrix_difference_quotient_bound
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {L : ℝ≥0} {r R h : ℝ}
    (hL : LipschitzOnWith L A (rawChartClosedBall R)) (hrR : r<R)
    (hh0 : h≠0) (hh : |h|<R-r) {x : CoordinateSpace n} (hx : x∈rawChartBall r)
    (i p k : Fin n) :
    |h⁻¹*(A (x+h • (Pi.single i 1 : CoordinateSpace n)) p k-A x p k)|≤(L:ℝ) := by
  have hxR : x∈rawChartClosedBall R := (show ‖(coordinateEquiv n).symm x‖<r from hx).le.trans hrR.le
  have hyR := coordinate_translate_mem_outer_closedBall hh hx i
  have hl := hL.norm_sub_le hyR hxR
  have he : |A (x+h • (Pi.single i 1 : CoordinateSpace n)) p k-A x p k| ≤
      ‖A (x+h • (Pi.single i 1 : CoordinateSpace n))-A x‖ := by
    exact (norm_le_pi_norm ((A (x+h • (Pi.single i 1 : CoordinateSpace n))-A x) p) k).trans
      (norm_le_pi_norm (A (x+h • (Pi.single i 1 : CoordinateSpace n))-A x) p)
  have hstep : ‖x+h • (Pi.single i 1 : CoordinateSpace n)-x‖=|h| := by
    rw [add_sub_cancel_left,norm_smul,Pi.norm_single,norm_one,mul_one,Real.norm_eq_abs]
  rw [hstep] at hl
  rw [abs_mul,abs_inv]
  calc
    _ ≤ |h|⁻¹*((L:ℝ)*|h|) := mul_le_mul_of_nonneg_left (he.trans hl) (inv_nonneg.mpr (abs_nonneg _))
    _ = _ := by field_simp

end GaussianTilt.MomentMapLinearDirichlet
