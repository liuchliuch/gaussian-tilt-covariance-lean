import GaussianTilt.MomentMapRegularityLocalizationSections
import GaussianTilt.MomentMapAlexandrovMaximum

/-! # Relative-width form of the Aleksandrov maximum principle

A point close to the upper side of a thin slab has small relative depth.
The bound is affine-geometric: one fixed lower-side point gives a lower
bound on the norm of the slab functional after any affine normalization.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators Gradient NNReal ENNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

/-- An actual narrow cap in one linear direction yields a relative-width
maximum estimate. This avoids any assumption about the nearest boundary
point or the orientation of an affine-normalized section. -/
theorem alexandrov_relative_width_maximum_principle [NeZero n] {u : E n → ℝ}
    (hu : ConvexOn ℝ univ u) {S : Set (E n)} (hS : IsCompact S)
    {x z v : E n} (hx : x ∈ S) {a b D ℓ : ℝ}
    (hb : 0 < b) (hD : 0 < D) (hℓ : 0 < ℓ)
    (hdepth : u x < a) (hboundary : ∀ y ∈ frontier S, a ≤ u y)
    (hupper : ∀ y ∈ frontier S, inner ℝ v (y - x) ≤ b)
    (hlower : inner ℝ v (z - x) ≤ -ℓ) (hzD : ‖z - x‖ ≤ D)
    (hdiam : ∀ y ∈ frontier S, ‖y - x‖ ≤ D) :
    ENNReal.ofReal ((a - u x) ^ n) ≤
      ENNReal.ofReal (2 * ((n : ℝ) + 1) ^ (n - 1) * (b / ℓ) * D ^ n) *
        volume (subgradientImage u (interior S)) := by
  have hℓv : ℓ ≤ ‖v‖ * D := by
    calc
      ℓ ≤ -inner ℝ v (z - x) := by linarith
      _ ≤ |inner ℝ v (z - x)| := neg_le_abs _
      _ ≤ ‖v‖ * ‖z - x‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖v‖ * D := mul_le_mul_of_nonneg_left hzD (norm_nonneg _)
  have hv : 0 < ‖v‖ := by nlinarith [norm_nonneg v]
  let w := ‖v‖⁻¹ • v
  have hw : ‖w‖ = 1 := by
    simp [w, norm_smul, hv.ne']
  obtain ⟨e, i₀, hei⟩ := alexandrov_exists_basis_vector hw
  have hc : Continuous u := continuousOn_univ.mp (hu.continuousOn isOpen_univ)
  have hbd : 0 < b / ‖v‖ := div_pos hb hv
  have hvol := alexandrov_anisotropic_volume_le hu hc hS hx e i₀ hbd hD hdepth hboundary
    (fun y hy => ?_) (fun y hy i => ?_)
  · let H := a - u x
    let d := b / ‖v‖
    let C := 2 * ((n : ℝ) + 1) ^ (n - 1) * d * D ^ (n - 1)
    have hH : 0 ≤ H := (sub_pos.mpr hdepth).le
    have hC : 0 ≤ C := by dsimp [C, d]; positivity
    have hN : (n : ℝ) + 1 ≠ 0 := by positivity
    have hp (r : ℝ) : r ^ n = r * r ^ (n - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n))]
      rw [pow_succ, mul_comm]
    have he : H ^ n = C * (H / (2 * d) * (H / (((n : ℝ) + 1) * D)) ^ (n - 1)) := by
      rw [hp]
      dsimp [C]
      rw [div_pow, mul_pow]
      field_simp [show d ≠ 0 from hbd.ne', hD.ne', hN]
    have hmax : ENNReal.ofReal (H ^ n) ≤
        ENNReal.ofReal C * volume (subgradientImage u (interior S)) := by
      rw [he, ENNReal.ofReal_mul hC, ENNReal.ofReal_mul (by positivity : 0 ≤ H / (2 * d)),
        ENNReal.ofReal_pow (by positivity : 0 ≤ H / (((n : ℝ) + 1) * D))]
      simpa only [Fintype.card_fin] using mul_le_mul_left' hvol (ENNReal.ofReal C)
    have hdle : d ≤ b * D / ℓ := by
      dsimp [d]
      apply (div_le_div_iff₀ hv hℓ).mpr
      nlinarith
    have hCle : C ≤ 2 * ((n : ℝ) + 1) ^ (n - 1) * (b / ℓ) * D ^ n := by
      calc
        C ≤ 2 * ((n : ℝ) + 1) ^ (n - 1) * (b * D / ℓ) * D ^ (n - 1) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hdle (by positivity)) (by positivity)
        _ = _ := by rw [hp D]; ring
    exact hmax.trans (mul_le_mul_right' (ENNReal.ofReal_le_ofReal hCle) _)
  · rw [e.repr_apply_apply, hei]
    dsimp [w]
    rw [real_inner_smul_left]
    calc
      ‖v‖⁻¹ * inner ℝ v (y - x) ≤ ‖v‖⁻¹ * b :=
        mul_le_mul_of_nonneg_left (hupper y hy) (inv_nonneg.mpr hv.le)
      _ = b / ‖v‖ := by ring
  · calc
      |e.repr (y - x) i| = |inner ℝ (e i) (y - x)| := by rw [e.repr_apply_apply]
      _ ≤ ‖e i‖ * ‖y - x‖ := abs_real_inner_le_norm _ _
      _ = ‖y - x‖ := by rw [e.orthonormal.norm_eq_one, one_mul]
      _ ≤ D := hdiam y hy

/-- Ordinary-real form of the relative-width estimate; finiteness is a
consequence of compactness of the full subgradient image. -/
theorem alexandrov_relative_width_maximum_principle_real [NeZero n] {u : E n → ℝ}
    (hu : ConvexOn ℝ univ u) {S : Set (E n)} (hS : IsCompact S)
    {x z v : E n} (hx : x ∈ S) {a b D ℓ : ℝ}
    (hb : 0 < b) (hD : 0 < D) (hℓ : 0 < ℓ)
    (hdepth : u x < a) (hboundary : ∀ y ∈ frontier S, a ≤ u y)
    (hupper : ∀ y ∈ frontier S, inner ℝ v (y - x) ≤ b)
    (hlower : inner ℝ v (z - x) ≤ -ℓ) (hzD : ‖z - x‖ ≤ D)
    (hdiam : ∀ y ∈ frontier S, ‖y - x‖ ≤ D) :
    (a - u x) ^ n ≤
      (2 * ((n : ℝ) + 1) ^ (n - 1) * (b / ℓ) * D ^ n) *
        volume.real (subgradientImage u (interior S)) := by
  have hc : Continuous u := continuousOn_univ.mp (hu.continuousOn isOpen_univ)
  have hfinite : volume (subgradientImage u (interior S)) ≠ ⊤ :=
    ne_top_of_le_ne_top (alexandrov_isCompact_subgradientImage hc hS).measure_lt_top.ne
      (measure_mono (alexandrov_subgradientImage_mono u interior_subset))
  have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite)
    (alexandrov_relative_width_maximum_principle hu hS hx hb hD hℓ hdepth hboundary hupper hlower hzD hdiam)
  have hH : 0 ≤ a - u x := (sub_pos.mpr hdepth).le
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ (a - u x) ^ n),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * ((n : ℝ) + 1) ^ (n - 1) * (b / ℓ) * D ^ n),
    Measure.real] using hh

/-- The quantitative contradiction underlying localization after affine
normalization. Common density scale q cancels, so only the original
lower/upper density ratio matters. All analytic bounds are the two literal
subgradient-volume inequalities on the normalized section and half ball. -/
theorem normalized_relative_width_obstruction [NeZero n] {u : E n → ℝ}
    (hu : ConvexOn ℝ univ u) {S : Set (E n)} (hS : IsCompact S)
    (hball : Metric.closedBall (0 : E n) 1 ⊆ S)
    {R : ℝ} (hR : 0 < R) (hSball : S ⊆ Metric.closedBall (0 : E n) R)
    {x z v : E n} (hx : x ∈ S) (hz : z ∈ S)
    {b ℓ H κ q lam Lam : ℝ} (hb : 0 < b) (hℓ : 0 < ℓ)
    (hκ : 0 ≤ κ) (hq : 0 < q) (hlam : 0 ≤ lam) (hLam : 0 ≤ Lam)
    (hbound : ∀ y ∈ S, -H ≤ u y ∧ u y ≤ 0)
    (hdepth : u x < 0) (hH : H ≤ κ * (-u x))
    (hboundary : ∀ y ∈ frontier S, 0 ≤ u y)
    (hupper : ∀ y ∈ S, inner ℝ v (y - x) ≤ b)
    (hlower : inner ℝ v (z - x) ≤ -ℓ)
    (hmassLower : ENNReal.ofReal (q * lam) * volume (Metric.closedBall (0 : E n) (1 / 2)) ≤
      volume (subgradientImage u (Metric.closedBall (0 : E n) (1 / 2))))
    (hmassUpper : volume (subgradientImage u S) ≤ ENNReal.ofReal (q * Lam) * volume S) :
    lam ≤ 4 ^ n * κ ^ n *
      (2 * ((n : ℝ) + 1) ^ (n - 1) * (b / ℓ) * (2 * R) ^ n) *
        Lam * volume.real (Metric.closedBall (0 : E n) R) := by
  have hdist (y : E n) (hy : y ∈ S) : ‖y - x‖ ≤ 2 * R := by
    have hyR : ‖y‖ ≤ R := by simpa using hSball hy
    have hxR : ‖x‖ ≤ R := by simpa using hSball hx
    exact (norm_sub_le y x).trans (by linarith)
  have hmax := alexandrov_relative_width_maximum_principle_real hu hS hx hb
    (by positivity : 0 < 2 * R) hℓ hdepth hboundary
    (fun y hy => hupper y (hS.isClosed.frontier_subset hy)) hlower (hdist z hz)
    (fun y hy => hdist y (hS.isClosed.frontier_subset hy))
  simp only [zero_sub] at hmax
  let C := 2 * ((n : ℝ) + 1) ^ (n - 1) * (b / ℓ) * (2 * R) ^ n
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hν : volume (subgradientImage u (interior S)) ≤
      ENNReal.ofReal (q * Lam) * volume (Metric.closedBall (0 : E n) R) := by
    exact (measure_mono (alexandrov_subgradientImage_mono u interior_subset)).trans
      (hmassUpper.trans (mul_le_mul_left' (measure_mono hSball) _))
  have hνreal := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (isCompact_closedBall (0 : E n) R).measure_lt_top.ne) hν
  have hqLam : 0 ≤ q * Lam := mul_nonneg hq.le hLam
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hqLam] at hνreal
  have hpowUpper : (-u x) ^ n ≤ C * (q * Lam * volume.real (Metric.closedBall (0 : E n) R)) :=
    hmax.trans (mul_le_mul_of_nonneg_left hνreal hC)
  have hmin := alexandrov_normalized_depth_lower hball (mul_nonneg hq.le hlam) hbound hmassLower
  have hHnonneg : 0 ≤ H := by have h := hbound x hx; linarith [h.1, h.2]
  have hpow : H ^ n ≤ κ ^ n * (-u x) ^ n := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hHnonneg hH n
  have hcombined : q * lam ≤ q * (4 ^ n * κ ^ n * C * Lam *
      volume.real (Metric.closedBall (0 : E n) R)) := by
    calc
      q * lam ≤ 4 ^ n * H ^ n := hmin
      _ ≤ 4 ^ n * (κ ^ n * (-u x) ^ n) := mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = (4 ^ n * κ ^ n) * (-u x) ^ n := by ring
      _ ≤ (4 ^ n * κ ^ n) *
          (C * (q * Lam * volume.real (Metric.closedBall (0 : E n) R))) :=
        mul_le_mul_of_nonneg_left hpowUpper (by positivity)
      _ = _ := by ring
  exact (mul_le_mul_left hq).mp hcombined

end GaussianTilt.MomentMapRegularity
