import GaussianTilt.MomentMapRegularitySecondOrderBoundaryModulus
import GaussianTilt.MomentMapRegularityInteriorBalance
import GaussianTilt.MomentMapRegularityBallHessian

/-!
# Quantitative interior separation and gradient bounds from Alexandrov mass

The actual bounded-domain maximum principle keeps positive-depth sublevel
sets away from the boundary. Supporting-plane geometry then supplies the
lower-order gradient bound used by the genuine Pogorelov estimate.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology Gradient NNReal ENNReal
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

/-- The boundary power coefficient with a prescribed diameter and mass bound. -/
def sectionBoundaryCoefficient (n : ℕ) (D M : ℝ) : ℝ :=
  2 * ((n : ℝ) + 1) ^ (n - 1) * D ^ (n - 1) * M

/-- A coarse uniform absolute bound on the zero-boundary potential. -/
def sectionAbsoluteBound (n : ℕ) (D M : ℝ) : ℝ :=
  2 * ((n : ℝ) + 1) ^ (n - 1) * D ^ n * M + 1

def sectionDepthRadius (n : ℕ) (D M δ : ℝ) : ℝ :=
  δ ^ n / (sectionBoundaryCoefficient n D M + 1)

def sectionDepthGradientBound (n : ℕ) (D M δ : ℝ) : ℝ :=
  2 * sectionAbsoluteBound n D M / sectionDepthRadius n D M δ

lemma sectionBoundaryCoefficient_nonneg {D M : ℝ} (hD : 0 ≤ D) (hM : 0 ≤ M) :
    0 ≤ sectionBoundaryCoefficient n D M := by unfold sectionBoundaryCoefficient; positivity

lemma sectionAbsoluteBound_pos {D M : ℝ} (hD : 0 ≤ D) (hM : 0 ≤ M) :
    0 < sectionAbsoluteBound n D M := by unfold sectionAbsoluteBound; positivity

lemma sectionDepthRadius_pos {D M δ : ℝ} (hD : 0 ≤ D) (hM : 0 ≤ M) (hδ : 0 < δ) :
    0 < sectionDepthRadius n D M δ := by
  have hB := sectionBoundaryCoefficient_nonneg (n := n) hD hM
  unfold sectionDepthRadius
  positivity

lemma sectionDepthGradientBound_pos {D M δ : ℝ} (hD : 0 ≤ D) (hM : 0 ≤ M) (hδ : 0 < δ) :
    0 < sectionDepthGradientBound n D M δ := by
  unfold sectionDepthGradientBound
  exact div_pos (mul_pos (by norm_num) (sectionAbsoluteBound_pos hD hM))
    (sectionDepthRadius_pos hD hM hδ)

/-- Actual convexity and actual differentiability give the supporting slope
on the original domain; no convex extension is needed. -/
lemma supportsOn_gradient_of_convexOn {S : Set (E n)} {u : E n → ℝ}
    (hu : ConvexOn ℝ S u) {x : E n} (hx : x ∈ S) (hd : DifferentiableAt ℝ u x) :
    SupportsOn S u (gradient u x) x := by
  intro y hy
  let l : ℝ →ᵃ[ℝ] E n := AffineMap.lineMap x y
  have hc : ConvexOn ℝ (l ⁻¹' S) (u ∘ l) := hu.comp_affineMap l
  have h0 : (0 : ℝ) ∈ l ⁻¹' S := by simpa [l] using hx
  have h1 : (1 : ℝ) ∈ l ⁻¹' S := by simpa [l] using hy
  have hd' : HasDerivAt (u ∘ l) (inner ℝ (gradient u x) (y - x)) 0 := by
    have hdu : HasFDerivAt u (InnerProductSpace.toDual ℝ (E n) (gradient u x)) (l 0) := by
      simpa [l] using hd.hasGradientAt.hasFDerivAt
    exact hdu.comp_hasDerivAt 0 (by simpa [l] using
      (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := (0 : ℝ))))
  have hs := hc.le_slope_of_hasDerivAt h0 h1 (by norm_num) hd'
  have hs' : inner ℝ (gradient u x) (y - x) ≤ u y - u x := by
    simpa [l, slope_def_field] using hs
  linarith

/-- Every positive-depth point contains a quantitative ball in the actual
domain. The radius follows from the actual Alexandrov boundary estimate. -/
theorem closedBall_subset_of_alexandrov_depth [NeZero n] {S : Set (E n)}
    (hS : IsCompact S) {u : E n → ℝ} (hu : ConvexOn ℝ S u) (huc : ContinuousOn u S)
    (hb : ∀ x ∈ frontier S, u x = 0) {D M δ : ℝ}
    (hD : 0 ≤ D) (hdiam : Metric.diam S ≤ D) (hM : 0 ≤ M) (hδ : 0 < δ)
    (hmass : volume (subgradientImageOn S u (interior S)) ≤ ENNReal.ofReal M)
    {x : E n} (hx : x ∈ S) (hdepth : δ ≤ -u x) :
    Metric.closedBall x (sectionDepthRadius n D M δ) ⊆ S := by
  have hp := alexandrovOn_boundary_power_bound hS hu huc hb hM hmass x hx
  have hB := sectionBoundaryCoefficient_nonneg (n := n) hD hM
  have hdist : 0 ≤ Metric.infDist x (frontier S) := Metric.infDist_nonneg
  have hpow : δ ^ n ≤ |u x| ^ n := pow_le_pow_left₀ hδ.le
    (hdepth.trans (neg_le_abs _)) n
  have hdiamPow := pow_le_pow_left₀ Metric.diam_nonneg hdiam (n - 1)
  have hcoeff : 2 * ((n : ℝ) + 1) ^ (n - 1) * Metric.diam S ^ (n - 1) * M ≤
      sectionBoundaryCoefficient n D M := by
    unfold sectionBoundaryCoefficient
    gcongr
  have hdepth' : δ ^ n ≤ sectionBoundaryCoefficient n D M * Metric.infDist x (frontier S) :=
    hpow.trans (hp.trans (mul_le_mul_of_nonneg_right hcoeff hdist))
  have hr : sectionDepthRadius n D M δ ≤ Metric.infDist x (frontier S) := by
    apply (div_le_iff₀ (by positivity : 0 < sectionBoundaryCoefficient n D M + 1)).mpr
    nlinarith
  exact (Metric.closedBall_subset_closedBall hr).trans (closedBall_infDist_frontier_subset hS hx)

/-- Lower-order gradient control at positive depth is derived from finite
Alexandrov mass and the domain diameter, before any Hessian bound is used. -/
theorem gradient_bound_at_alexandrov_depth [NeZero n] {S : Set (E n)}
    (hS : IsCompact S) {u : E n → ℝ} (hu : ConvexOn ℝ S u) (huc : ContinuousOn u S)
    (hb : ∀ x ∈ frontier S, u x = 0) {D M δ : ℝ}
    (hD : 0 ≤ D) (hdiam : Metric.diam S ≤ D) (hM : 0 ≤ M) (hδ : 0 < δ)
    (hmass : volume (subgradientImageOn S u (interior S)) ≤ ENNReal.ofReal M)
    {x : E n} (hx : x ∈ S) (hdepth : δ ≤ -u x) (hd : DifferentiableAt ℝ u x) :
    ‖gradient u x‖ ≤ sectionDepthGradientBound n D M δ := by
  apply supportsOn_norm_bound (supportsOn_gradient_of_convexOn hu hx hd)
    (sectionDepthRadius_pos hD hM hδ) (sectionAbsoluteBound_pos hD hM).le
    (closedBall_subset_of_alexandrov_depth hS hu huc hb hD hdiam hM hδ hmass hx hdepth)
  intro y hy
  apply (alexandrovOn_uniform_abs_bound hS hu huc hb hM hmass y hy).trans
  unfold sectionAbsoluteBound
  gcongr

end GaussianTilt.MomentMapRegularity
