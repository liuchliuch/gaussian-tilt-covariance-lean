import GaussianTilt.MomentMapRegularityInteriorSections
import GaussianTilt.MomentMapRegularityLocalizationAffine
import GaussianTilt.MomentMapAffineNormalization

/-!
# Quantitative centering of normalized Monge--Ampère sections

The genuine Aleksandrov maximum principle and the genuine lower-depth
estimate force the minimum point of every normalized section away from its
boundary. The common affine density scale cancels. This is an actual
section-balance estimate, prior to any engulfing or Hölder theorem.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators Gradient NNReal ENNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

/-- An explicit coefficient for the quantitative centering estimate. -/
def sectionCenterCoefficient (n : ℕ) (R Lam : ℝ) : ℝ :=
  4 ^ n * (2 * ((n : ℝ) + 1) ^ (n - 1) * (2 * R) ^ (n - 1)) *
    Lam * volume.real (Metric.closedBall (0 : E n) R)

lemma sectionCenterCoefficient_pos {R Lam : ℝ} (hR : 0 < R) (hLam : 0 < Lam) :
    0 < sectionCenterCoefficient n R Lam := by
  have hv : 0 < volume (Metric.closedBall (0 : E n) R) :=
    (Metric.isOpen_ball.measure_pos volume
      ⟨0, Metric.mem_ball_self hR⟩).trans_le (measure_mono Metric.ball_subset_closedBall)
  have hvreal : 0 < volume.real (Metric.closedBall (0 : E n) R) :=
    ENNReal.toReal_pos hv.ne' (isCompact_closedBall (0 : E n) R).measure_lt_top.ne
  dsimp [sectionCenterCoefficient]
  positivity

/-- Quantitative centering: the density ratio controls how close the
minimum point can be to the boundary of a normalized section. The height
and the affine density scale cancel rather than being assumed controlled. -/
theorem normalized_section_center_distance [NeZero n] {u : E n → ℝ}
    (hu : ConvexOn ℝ univ u) {S : Set (E n)} (hS : IsCompact S)
    (hSc : Convex ℝ S) (hball : Metric.closedBall (0 : E n) 1 ⊆ S)
    {R : ℝ} (hR : 0 < R) (hSball : S ⊆ Metric.closedBall (0 : E n) R)
    {x : E n} (hx : x ∈ interior S) {H q lam Lam : ℝ}
    (hH : 0 < H) (hq : 0 < q) (hlam : 0 ≤ lam) (hLam : 0 ≤ Lam)
    (hmin : u x = -H) (hbound : ∀ y ∈ S, -H ≤ u y ∧ u y ≤ 0)
    (hboundary : ∀ y ∈ frontier S, 0 ≤ u y)
    (hmassLower : ENNReal.ofReal (q * lam) * volume (Metric.closedBall (0 : E n) (1 / 2)) ≤
      volume (subgradientImage u (Metric.closedBall (0 : E n) (1 / 2))))
    (hmassUpper : volume (subgradientImage u S) ≤ ENNReal.ofReal (q * Lam) * volume S) :
    lam ≤ sectionCenterCoefficient n R Lam * Metric.infDist x (frontier S) := by
  have hlow := alexandrov_normalized_depth_lower hball (mul_nonneg hq.le hlam) hbound hmassLower
  have hmax := alexandrov_maximum_principle_real hu hS hSc hx
    (a := 0) (by rw [hmin]; linarith) hboundary
  simp only [hmin, sub_neg_eq_add, zero_add] at hmax
  have hdiam : Metric.diam S ≤ 2 * R := Metric.diam_le_of_subset_closedBall hR.le hSball
  have hpow : Metric.diam S ^ (n - 1) ≤ (2 * R) ^ (n - 1) :=
    pow_le_pow_left₀ Metric.diam_nonneg hdiam _
  have hmass : volume (subgradientImage u (interior S)) ≤
      ENNReal.ofReal (q * Lam) * volume (Metric.closedBall (0 : E n) R) :=
    (measure_mono (alexandrov_subgradientImage_mono u interior_subset)).trans
      (hmassUpper.trans (mul_le_mul_left' (measure_mono hSball) _))
  have hmassReal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (isCompact_closedBall (0 : E n) R).measure_lt_top.ne) hmass
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg hq.le hLam)] at hmassReal
  let A := 2 * ((n : ℝ) + 1) ^ (n - 1)
  let d := Metric.infDist x (frontier S)
  let V := volume.real (Metric.closedBall (0 : E n) R)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hd : 0 ≤ d := Metric.infDist_nonneg
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have hcoeff : A * d * Metric.diam S ^ (n - 1) ≤ A * d * (2 * R) ^ (n - 1) :=
    mul_le_mul_of_nonneg_left hpow (mul_nonneg hA hd)
  have hup : H ^ n ≤ (A * d * (2 * R) ^ (n - 1)) * (q * Lam * V) := by
    exact hmax.trans (mul_le_mul hcoeff hmassReal ENNReal.toReal_nonneg
      (mul_nonneg (mul_nonneg hA hd) (by positivity)))
  have hfinal : q * lam ≤ q * (sectionCenterCoefficient n R Lam * d) := by
    calc
      q * lam ≤ 4 ^ n * H ^ n := hlow
      _ ≤ 4 ^ n * ((A * d * (2 * R) ^ (n - 1)) * (q * Lam * V)) :=
        mul_le_mul_of_nonneg_left hup (by positivity)
      _ = _ := by dsimp [sectionCenterCoefficient, A, V]; ring
  exact (mul_le_mul_left hq).mp hfinal

/-- For a compact body, the closed ball of radius equal to the distance
to its frontier stays in the body. This is derived from the actual nearest
complement point rather than a geometric ball-containment assumption. -/
lemma closedBall_infDist_frontier_subset [NeZero n] {S : Set (E n)}
    (hS : IsCompact S) {x : E n} (hx : x ∈ S) :
    Metric.closedBall x (Metric.infDist x (frontier S)) ⊆ S := by
  obtain ⟨z, hz, he⟩ := hS.exists_mem_frontier_infDist_compl_eq_dist hx
  have hle : Metric.infDist x (frontier S) ≤ Metric.infDist x Sᶜ := by
    rw [he]
    exact Metric.infDist_le_dist_of_mem hz
  exact (Metric.closedBall_subset_closedBall hle).trans
    ((Metric.closedBall_infDist_compl_subset_closure hx).trans_eq hS.isClosed.closure_eq)

/-- The actual minimum point has a definite ball inside the normalized
section. Its radius depends only on the normalized outer radius and the
original Alexandrov density ratio, not on the affine determinant or height. -/
theorem normalized_section_contains_center_ball [NeZero n] {u : E n → ℝ}
    (hu : ConvexOn ℝ univ u) {S : Set (E n)} (hS : IsCompact S)
    (hSc : Convex ℝ S) (hball : Metric.closedBall (0 : E n) 1 ⊆ S)
    {R : ℝ} (hR : 0 < R) (hSball : S ⊆ Metric.closedBall (0 : E n) R)
    {x : E n} (hx : x ∈ interior S) {H q lam Lam : ℝ}
    (hH : 0 < H) (hq : 0 < q) (hlam : 0 < lam) (hLam : 0 < Lam)
    (hmin : u x = -H) (hbound : ∀ y ∈ S, -H ≤ u y ∧ u y ≤ 0)
    (hboundary : ∀ y ∈ frontier S, 0 ≤ u y)
    (hmassLower : ENNReal.ofReal (q * lam) * volume (Metric.closedBall (0 : E n) (1 / 2)) ≤
      volume (subgradientImage u (Metric.closedBall (0 : E n) (1 / 2))))
    (hmassUpper : volume (subgradientImage u S) ≤ ENNReal.ofReal (q * Lam) * volume S) :
    Metric.closedBall x (lam / sectionCenterCoefficient n R Lam) ⊆ S := by
  have hdist := normalized_section_center_distance hu hS hSc hball hR hSball hx
    hH hq hlam.le hLam.le hmin hbound hboundary hmassLower hmassUpper
  have hC := sectionCenterCoefficient_pos (n := n) hR hLam
  apply (Metric.closedBall_subset_closedBall ?_).trans
    (closedBall_infDist_frontier_subset hS (interior_subset hx))
  exact (div_le_iff₀ hC).mpr (by simpa [mul_comm] using hdist)

/-- Quantitative affine-invariant balance follows from the genuine inner
ball around the minimum point and the normalized outer ball. -/
lemma reflected_contraction_mem_of_center_ball {S : Set (E n)} {x y : E n}
    {R ρ θ : ℝ} (hR : 0 < R) (hθ : 0 ≤ θ) (hθρ : θ * (2 * R) ≤ ρ)
    (hSball : S ⊆ Metric.closedBall (0 : E n) R)
    (hcenter : Metric.closedBall x ρ ⊆ S) (hx : x ∈ S) (hy : y ∈ S) :
    x - θ • (y - x) ∈ S := by
  apply hcenter
  rw [Metric.mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg hθ]
  have hxR : ‖x‖ ≤ R := by simpa using hSball hx
  have hyR : ‖y‖ ≤ R := by simpa using hSball hy
  have hnorm : ‖y - x‖ ≤ 2 * R := (norm_sub_le y x).trans (by linarith)
  exact (mul_le_mul_of_nonneg_left hnorm hθ).trans hθρ

end GaussianTilt.MomentMapRegularity
