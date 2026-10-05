import GaussianTilt.MomentMapRegularityConstantDensityInterior
import GaussianTilt.MomentMapRegularityConstantDensityGeometry
import GaussianTilt.MomentMapRegularityAffineHessian

/-!
# Normalized smooth constant-density Hessian estimates

The lower-order gradient input in Pogorelov's calculation is derived from
the actual Alexandrov mass and boundary geometry on a larger section. No
first- or second-derivative bound is assumed in the resulting estimate.
-/
noncomputable section
open Matrix MeasureTheory Filter Set
open scoped BigOperators Topology Gradient NNReal ENNReal ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

/-- The explicit bound produced by the two nested positive-depth sections. -/
def sectionInteriorHessianBound (n : ℕ) (D M δ : ℝ) : ℝ :=
  (((n : ℝ) + sectionDepthGradientBound n D M δ) *
    Real.exp ((sectionDepthGradientBound n D M δ)^2 / 2)) / δ

lemma coordinateHessian_add_const (f : CoordinateSpace n → ℝ) (c : ℝ)
    (x : CoordinateSpace n) : coordinateHessian (fun y => f y + c) x = coordinateHessian f x := by
  simpa only [sub_neg_eq_add] using coordinateHessian_sub_const f (-c) x

lemma coordinateDerivative_add_const (f : CoordinateSpace n → ℝ) (c : ℝ)
    (x : CoordinateSpace n) (i : Fin n) :
    coordinateDerivative i (fun y => f y + c) x = coordinateDerivative i f x := by
  simp only [coordinateDerivative, fderiv_add_const]

lemma smooth_posDef_not_localMax {f : CoordinateSpace n → ℝ}
    {x : CoordinateSpace n} (hf : ContDiffAt ℝ 2 f x) (hH : (coordinateHessian f x).PosDef)
    (i : Fin n) : ¬ IsLocalMax f x := by
  intro hm
  have hneg := neg_hessian_posSemidef_of_isLocalMax_at hf hm
  have hp := coordinateHessian_diagonal_pos hH i
  have hn := hneg.2 (Pi.single i 1)
  have hnon : coordinateHessian f x i i ≤ 0 := by
    simpa [star_trivial, Matrix.neg_mulVec, dotProduct_neg, Matrix.mulVec_single_one,
      single_dotProduct, Matrix.col] using hn
  linarith

/-- A fully quantitative interior Hessian estimate for smooth unit-density
solutions. The only mass input is a bound on the literal bounded-domain
Alexandrov image. All gradient and Hessian bounds are conclusions. -/
theorem smooth_constant_density_hessian_bound_at_depth [NeZero n]
    {u : E n → ℝ} (hu : ContDiff ℝ ∞ u) {S : Set (E n)} (hS : IsCompact S)
    (hc : ConvexOn ℝ S u) (hb : ∀ y ∈ frontier S, u y = 0)
    (hH : ∀ y ∈ interior S,
      (coordinateHessian (coordinatePullback u) (coordinateEquiv n y)).PosDef)
    (hMA : ∀ y ∈ interior S,
      (coordinateHessian (coordinatePullback u) (coordinateEquiv n y)).det = 1)
    {D M δ : ℝ} (hD : 0 ≤ D) (hdiam : Metric.diam S ≤ D) (hM : 0 ≤ M) (hδ : 0 < δ)
    (hmass : volume (subgradientImageOn S u (interior S)) ≤ ENNReal.ofReal M)
    {x : E n} (hx : x ∈ S) (hdepth : 2 * δ ≤ -u x) (i j : Fin n) :
    |coordinateHessian (coordinatePullback u) (coordinateEquiv n x) i j| ≤
      sectionInteriorHessianBound n D M δ := by
  let e := coordinateEquiv n
  let U := coordinatePullback u
  let C := e '' S
  let T := C ∩ {y | U y ≤ -δ}
  let f := fun y => U y + δ
  let G := sectionDepthGradientBound n D M δ
  have hG : 0 < G := sectionDepthGradientBound_pos hD hM hδ
  have hU : ContDiff ℝ ∞ U := hu.comp e.symm.contDiff
  have hf : ContDiff ℝ ∞ f := hU.add contDiff_const
  have hUC : Continuous U := hU.continuous
  have hC : IsCompact C := hS.image e.continuous
  have hT : IsCompact T := hC.inter_right (isClosed_le hUC continuous_const)
  have hsource {y : CoordinateSpace n} (hy : y ∈ C) : e.symm y ∈ S := by
    obtain ⟨z, hz, rfl⟩ := hy
    simpa using hz
  have hinterior {y : CoordinateSpace n} (hy : y ∈ C) (huy : U y < 0) :
      e.symm y ∈ interior S := by
    by_contra hnot
    have hz := hb (e.symm y) ⟨subset_closure (hsource hy), hnot⟩
    change u (e.symm y) < 0 at huy
    linarith
  have hTintS {y : CoordinateSpace n} (hy : y ∈ T) : e.symm y ∈ interior S :=
    hinterior hy.1 (by have := hy.2; change U y ≤ -δ at this; linarith)
  have hTintC {y : CoordinateSpace n} (hy : y ∈ T) : y ∈ interior C := by
    change y ∈ interior (e.toHomeomorph '' S)
    rw [← e.toHomeomorph.image_interior]
    exact ⟨e.symm y, hTintS hy, e.apply_symm_apply y⟩
  have hTfH {y : CoordinateSpace n} (hy : y ∈ T) : (coordinateHessian f y).PosDef := by
    dsimp [f]
    rw [coordinateHessian_add_const]
    simpa [e] using hH (e.symm y) (hTintS hy)
  have hTfMA {y : CoordinateSpace n} (hy : y ∈ T) : (coordinateHessian f y).det = 1 := by
    dsimp [f]
    rw [coordinateHessian_add_const]
    simpa [e] using hMA (e.symm y) (hTintS hy)
  have hstrictInterior {y : CoordinateSpace n} (hy : y ∈ C) (hyC : y ∈ interior C)
      (huy : U y < -δ) : y ∈ interior T := by
    apply mem_interior.mpr
    refine ⟨interior C ∩ {z | U z < -δ}, ?_, ?_, ⟨hyC, huy⟩⟩
    · intro z hz
      have hzu : U z < -δ := hz.2
      exact ⟨interior_subset hz.1, hzu.le⟩
    · exact isOpen_interior.inter (isOpen_lt hUC continuous_const)
  have hzero : ∀ y ∈ frontier T, f y = 0 := by
    intro y hy
    have hyT : y ∈ T := hT.isClosed.frontier_subset hy
    have hyle : U y ≤ -δ := hyT.2
    have hyeq : U y = -δ := by
      by_contra hne
      have hylt : U y < -δ := lt_of_le_of_ne hyle hne
      exact hy.2 (hstrictInterior hyT.1 (hTintC hyT) hylt)
    dsimp [f]
    linarith
  have hneg : ∀ y ∈ interior T, f y < 0 := by
    intro y hy
    have hyT := interior_subset hy
    have hyle : U y ≤ -δ := hyT.2
    have hne : f y ≠ 0 := by
      intro heq
      have hm : IsLocalMax f y := by
        filter_upwards [mem_interior_iff_mem_nhds.mp hy] with z hz
        have hzU : U z ≤ -δ := hz.2
        change U z + δ ≤ f y
        rw [heq]
        linarith
      exact smooth_posDef_not_localMax (contDiff_infty.mp hf 2).contDiffAt
        (hTfH hyT) i hm
    change U y + δ < 0
    have hn : U y + δ ≠ 0 := hne
    exact lt_of_le_of_ne (by linarith) hn
  have hDu : ∀ y ∈ T, ∀ k : Fin n, |coordinateDerivative k f y| ≤ G := by
    intro y hy k
    have hgrad := gradient_bound_at_alexandrov_depth hS hc hu.continuous.continuousOn hb
      hD hdiam hM hδ hmass (hsource hy.1)
      (by have := hy.2; change u (e.symm y) ≤ -δ at this; linarith)
      (hu.differentiable (by simp) _)
    dsimp [f]
    rw [coordinateDerivative_add_const]
    change |coordinateGradient (coordinatePullback u) y k| ≤ G
    rw [coordinateGradient_pullback (hu.differentiable (by simp))]
    have hcoord : |gradient u (e.symm y) k| ≤ ‖gradient u (e.symm y)‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (gradient u (e.symm y)) k
    exact hcoord.trans hgrad
  have hxC : e x ∈ C := ⟨x, hx, rfl⟩
  have hxU : U (e x) = u x := by simp [U, coordinatePullback, e]
  have hxSi : x ∈ interior S := by
    have hu0 : U (e x) < 0 := by rw [hxU]; linarith
    simpa using hinterior hxC hu0
  have hxCi : e x ∈ interior C := by
    change e x ∈ interior (e.toHomeomorph '' S)
    rw [← e.toHomeomorph.image_interior]
    exact ⟨x, hxSi, rfl⟩
  have hxT : e x ∈ interior T := hstrictInterior hxC hxCi (by rw [hxU]; linarith)
  have hh := pogorelov_hessian_entry_bound_at_depth hf hT hzero hneg
    (fun y hy => hTfH (interior_subset hy)) (fun y hy => hTfMA (interior_subset hy))
    hG.le hδ hDu hxT (by dsimp [f]; rw [hxU]; linarith) i j
  simpa only [f, coordinateHessian_add_const, sectionInteriorHessianBound, G] using hh

end GaussianTilt.MomentMapRegularity
