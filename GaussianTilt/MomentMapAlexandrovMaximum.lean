import GaussianTilt.MomentMapRegularityLocalization

/-!
# Aleksandrov cone geometry and maximum estimates

All subgradient images in this file are the literal global supporting-plane
images defined in `MomentMapRegularityLocalization`. Supporting slopes are
constructed by compact minimization; no Aleksandrov or regularity theorem is
assumed. The coordinate boxes below give actual Lebesgue lower bounds.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators NNReal ENNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

/-- An affine tilt of a finite convex function remains convex. -/
lemma alexandrov_convex_tilt {u : E n → ℝ} (hu : ConvexOn ℝ univ u) (p : E n) :
    ConvexOn ℝ univ (fun y => u y - inner ℝ p y) := by
  exact hu.sub ((innerSL ℝ p).toLinearMap.concaveOn convex_univ)

/-- A plane strictly below the boundary values, passing through one point
of a compact set, can be slid downward to touch the interior. The resulting
slope is a genuine global subgradient of the original convex function. -/
theorem alexandrov_slope_mem_subgradientImage {u : E n → ℝ}
    (hu : ConvexOn ℝ univ u) (huc : Continuous u)
    {S : Set (E n)} (hS : IsCompact S) {x p : E n} (hx : x ∈ S)
    (hb : ∀ y ∈ frontier S, u x + inner ℝ p (y - x) < u y) :
    p ∈ subgradientImage u (interior S) := by
  let F := fun y => u y - inner ℝ p y
  have hF : Continuous F := huc.sub (continuous_const.inner continuous_id)
  obtain ⟨z, hz, hmin⟩ := hS.exists_isMinOn ⟨x, hx⟩ hF.continuousOn
  have hzi : z ∈ interior S := by
    by_contra hzi
    have hzb : z ∈ frontier S := ⟨subset_closure hz, hzi⟩
    have hh := hb z hzb
    have hm := hmin hx
    dsimp [F] at hm
    rw [inner_sub_right] at hh
    linarith
  refine ⟨z, hzi, ?_⟩
  have hm := IsMinOn.of_isLocalMin_of_convex_univ
    (hmin.isLocalMin (mem_interior_iff_mem_nhds.mp hzi)) (alexandrov_convex_tilt hu p)
  intro y
  have h := hm y
  change u z - inner ℝ p z ≤ u y - inner ℝ p y at h
  rw [inner_sub_right]
  linarith

/-- The strict polar of the boundary, scaled by the depth, consists of
actual slopes touching the interior. Boundary values need only be bounded
below; equality on the boundary is not needed. -/
theorem alexandrov_polar_subset_subgradientImage {u : E n → ℝ}
    (hu : ConvexOn ℝ univ u) (huc : Continuous u)
    {S : Set (E n)} (hS : IsCompact S) {x : E n} (hx : x ∈ S)
    {a : ℝ} (hb : ∀ y ∈ frontier S, a ≤ u y) :
    {p | ∀ y ∈ frontier S, inner ℝ p (y - x) < a - u x} ⊆
      subgradientImage u (interior S) := by
  intro p hp
  apply alexandrov_slope_mem_subgradientImage hu huc hS hx
  intro y hy
  have hh := hp y hy
  have hy' := hb y hy
  linarith

/-- The elementary isotropic cone estimate, before the anisotropic
boundary-distance refinement: a slope ball of radius depth / radius touches
the interior of the domain. -/
theorem alexandrov_ball_subset_subgradientImage {u : E n → ℝ}
    (hu : ConvexOn ℝ univ u) (huc : Continuous u)
    {S : Set (E n)} (hS : IsCompact S) {x : E n} (hx : x ∈ S)
    {a D : ℝ} (hD : 0 < D) (_hdepth : u x < a)
    (hb : ∀ y ∈ frontier S, a ≤ u y)
    (hdiam : ∀ y ∈ frontier S, ‖y - x‖ ≤ D) :
    Metric.ball (0 : E n) ((a - u x) / D) ⊆ subgradientImage u (interior S) := by
  apply Set.Subset.trans ?_ (alexandrov_polar_subset_subgradientImage hu huc hS hx hb)
  intro p hp y hy
  have hp' : ‖p‖ < (a - u x) / D := by simpa using hp
  calc
    inner ℝ p (y - x) ≤ ‖p‖ * ‖y - x‖ := real_inner_le_norm _ _
    _ ≤ ‖p‖ * D := mul_le_mul_of_nonneg_left (hdiam y hy) (norm_nonneg _)
    _ < a - u x := (lt_div_iff₀ hD).mp hp'

/-- A genuine Lebesgue-volume estimate for literal subgradient images.
The factor is the exact Euclidean unit-ball volume. -/
theorem alexandrov_ball_volume_le [NeZero n] {u : E n → ℝ}
    (hu : ConvexOn ℝ univ u) (huc : Continuous u)
    {S : Set (E n)} (hS : IsCompact S) {x : E n} (hx : x ∈ S)
    {a D : ℝ} (hD : 0 < D) (hdepth : u x < a)
    (hb : ∀ y ∈ frontier S, a ≤ u y)
    (hdiam : ∀ y ∈ frontier S, ‖y - x‖ ≤ D) :
    ENNReal.ofReal ((a - u x) / D) ^ n *
      ENNReal.ofReal (Real.sqrt Real.pi ^ n / Real.Gamma ((n : ℝ) / 2 + 1)) ≤
      volume (subgradientImage u (interior S)) := by
  have hm := measure_mono (μ := volume) (alexandrov_ball_subset_subgradientImage hu huc hS hx hD hdepth hb hdiam)
  simpa [EuclideanSpace.volume_ball, E, Reference.Space] using hm

/-- An open rectangular set of slopes in an arbitrary orthonormal frame. -/
def alexandrovSlopeBox {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (E n)) (l r : ι → ℝ) : Set (E n) :=
  {p | ∀ i, l i < b.repr p i ∧ b.repr p i < r i}

/-- Lebesgue volume of a slope box is the product of its side lengths.
The orthonormal change of coordinates is proved measure preserving. -/
theorem alexandrov_volume_slopeBox {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (E n)) (l r : ι → ℝ) :
    volume (alexandrovSlopeBox b l r) = ∏ i, ENNReal.ofReal (r i - l i) := by
  have hm := (PiLp.volume_preserving_ofLp ι).comp b.measurePreserving_repr
  have he : alexandrovSlopeBox b l r =
      (fun p => WithLp.ofLp (b.repr p)) ⁻¹' (Set.pi univ (fun i => Ioo (l i) (r i))) := by
    ext p
    simp [alexandrovSlopeBox]
  rw [he]
  exact (hm.measure_preimage (MeasurableSet.pi (Set.to_countable univ)
    (fun _ _ => measurableSet_Ioo)).nullMeasurableSet).trans Real.volume_pi_Ioo

/-- The scalar product is the sum of products in any orthonormal frame. -/
lemma alexandrov_inner_eq_sum {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (E n)) (p y : E n) :
    inner ℝ p y = ∑ i, b.repr p i * b.repr y i := by
  rw [← b.sum_inner_mul_inner p y]
  apply Finset.sum_congr rfl
  intro i _
  simp only [b.repr_apply_apply, real_inner_comm p]

/-- A one-sided slope interval in one direction and symmetric intervals
in all other directions form an explicit box in the polar cone. -/
theorem alexandrov_anisotropic_box_subset {ι : Type*} [Fintype ι] [DecidableEq ι]
    {u : E n → ℝ} (hu : ConvexOn ℝ univ u) (huc : Continuous u)
    {S : Set (E n)} (hS : IsCompact S) {x : E n} (hx : x ∈ S)
    (b : OrthonormalBasis ι ℝ (E n)) (i₀ : ι)
    {a d D : ℝ} (hd : 0 < d) (hD : 0 < D) (hdepth : u x < a)
    (hb : ∀ y ∈ frontier S, a ≤ u y)
    (hwidth : ∀ y ∈ frontier S, b.repr (y - x) i₀ ≤ d)
    (hdiam : ∀ y ∈ frontier S, ∀ i, |b.repr (y - x) i| ≤ D) :
    alexandrovSlopeBox b
      (fun i => if i = i₀ then 0 else -(a - u x) / (2 * (Fintype.card ι + 1) * D))
      (fun i => if i = i₀ then (a - u x) / (2 * d)
        else (a - u x) / (2 * (Fintype.card ι + 1) * D)) ⊆
      subgradientImage u (interior S) := by
  apply Set.Subset.trans ?_ (alexandrov_polar_subset_subgradientImage hu huc hS hx hb)
  intro p hp y hy
  let H := a - u x
  let N : ℝ := Fintype.card ι
  let r := H / (2 * (N + 1) * D)
  have hH : 0 < H := sub_pos.mpr hdepth
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hr : 0 < r := by dsimp [r]; positivity
  have hp₀ : 0 < b.repr p i₀ ∧ b.repr p i₀ < H / (2 * d) := by
    simpa [alexandrovSlopeBox, H] using hp i₀
  have hmain : b.repr p i₀ * b.repr (y - x) i₀ < H / 2 := by
    calc
      _ ≤ b.repr p i₀ * d := mul_le_mul_of_nonneg_left (hwidth y hy) hp₀.1.le
      _ < (H / (2 * d)) * d := mul_lt_mul_of_pos_right hp₀.2 hd
      _ = H / 2 := by field_simp
  have hsmall (i : ι) (hi : i ≠ i₀) :
      b.repr p i * b.repr (y - x) i ≤ r * D := by
    have hpi : |b.repr p i| < r := by
      rw [abs_lt]
      have hi' := hp i
      simp only [if_neg hi] at hi'
      change -H / (2 * (N + 1) * D) < b.repr p i ∧ b.repr p i < r at hi'
      simpa only [neg_div] using hi' 
    calc
      _ ≤ |b.repr p i * b.repr (y - x) i| := le_abs_self _
      _ = |b.repr p i| * |b.repr (y - x) i| := abs_mul _ _
      _ ≤ r * D := mul_le_mul hpi.le (hdiam y hy i) (abs_nonneg _) hr.le
  have hsum : (∑ i ∈ Finset.univ.erase i₀, b.repr p i * b.repr (y - x) i) ≤ H / 2 := by
    calc
      _ ≤ ∑ _i ∈ Finset.univ.erase i₀, r * D := by
        apply Finset.sum_le_sum
        intro i hi
        exact hsmall i (Finset.mem_erase.mp hi).1
      _ ≤ ∑ _i : ι, r * D := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.erase_subset _ _) (fun _ _ _ => by positivity)
      _ = N * (r * D) := by simp [N]
      _ ≤ H / 2 := by
        dsimp [r]
        have hpos : 0 < 2 * (N + 1) * D := by positivity
        field_simp
        nlinarith
  rw [alexandrov_inner_eq_sum b,
    ← Finset.sum_erase_add _ _ (Finset.mem_univ i₀)]
  change _ < H
  linarith

/-- An explicit anisotropic Aleksandrov lower bound. Its distinguished
factor is inverse-linear in the one-sided width, rather than a full power
of the diameter. -/
theorem alexandrov_anisotropic_volume_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {u : E n → ℝ} (hu : ConvexOn ℝ univ u) (huc : Continuous u)
    {S : Set (E n)} (hS : IsCompact S) {x : E n} (hx : x ∈ S)
    (b : OrthonormalBasis ι ℝ (E n)) (i₀ : ι)
    {a d D : ℝ} (hd : 0 < d) (hD : 0 < D) (hdepth : u x < a)
    (hb : ∀ y ∈ frontier S, a ≤ u y)
    (hwidth : ∀ y ∈ frontier S, b.repr (y - x) i₀ ≤ d)
    (hdiam : ∀ y ∈ frontier S, ∀ i, |b.repr (y - x) i| ≤ D) :
    ENNReal.ofReal ((a - u x) / (2 * d)) *
      ENNReal.ofReal ((a - u x) / ((Fintype.card ι + 1) * D)) ^ (Fintype.card ι - 1) ≤
      volume (subgradientImage u (interior S)) := by
  have hm := measure_mono (μ := volume)
    (alexandrov_anisotropic_box_subset hu huc hS hx b i₀ hd hD hdepth hb hwidth hdiam)
  rw [alexandrov_volume_slopeBox] at hm
  convert hm using 1
  symm
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i₀)]
  simp only [ite_true, sub_zero]
  congr 1
  calc
    _ = ∏ i ∈ Finset.univ.erase i₀,
        ENNReal.ofReal ((a - u x) / ((Fintype.card ι + 1) * D)) := by
      apply Finset.prod_congr rfl
      intro i hi
      simp only [if_neg (Finset.mem_erase.mp hi).1]
      congr 1
      field_simp; ring
    _ = _ := by simp

/-- A unit vector can be made a coordinate vector of a full orthonormal
frame. This is an actual basis extension, not an assumed normalization. -/
lemma alexandrov_exists_basis_vector {v : E n} (hv : ‖v‖ = 1) :
    ∃ (b : OrthonormalBasis (Fin n) ℝ (E n)) (i : Fin n), b i = v := by
  classical
  have hon : Orthonormal ℝ (fun z : ({v} : Set (E n)) => (z : E n)) := by
    constructor
    · intro z
      simpa only [Set.mem_singleton_iff.mp z.property] using hv
    · intro z w hzw
      exact (hzw (Subtype.ext (by simpa using z.property.trans w.property.symm))).elim
  obtain ⟨s, b, hvs, hb⟩ := hon.exists_orthonormalBasis_extension
  let i : s := ⟨v, hvs (by simp)⟩
  have hcard : Fintype.card s = n := by
    rw [← Module.finrank_eq_card_basis b.toBasis]
    simp [E, Reference.Space]
  let e : s ≃ Fin n := (Fintype.equivFin s).trans (finCongr hcard)
  refine ⟨b.reindex e, e i, ?_⟩
  simp only [OrthonormalBasis.reindex_apply, Equiv.symm_apply_apply]
  exact congrFun hb i

/-- Every boundary point of a convex body admits a supporting unit normal.
The proof uses geometric Hahn--Banach and Riesz representation. -/
theorem alexandrov_boundary_unit_normal {S : Set (E n)} (hSc : Convex ℝ S)
    {x z : E n} (hx : x ∈ interior S) (hz : z ∈ frontier S) :
    ∃ v : E n, ‖v‖ = 1 ∧ ∀ y ∈ S, inner ℝ v (y - z) ≤ 0 := by
  obtain ⟨f, hf⟩ := geometric_hahn_banach_point_open hSc.interior isOpen_interior hz.2
  let q := (InnerProductSpace.toDual ℝ (E n)).symm f
  have hq (w : E n) : inner ℝ q w = f w := by
    change (InnerProductSpace.toDual ℝ (E n)) q w = f w
    simp [q]
  have hqn : q ≠ 0 := by
    intro hq0
    have hh := hf x hx
    rw [← hq x, ← hq z, hq0] at hh
    simp at hh
  have hqp : 0 < ‖q‖ := norm_pos_iff.mpr hqn
  have hfS : ∀ y ∈ S, f z ≤ f y := by
    have hh : closure (interior S) ⊆ {y | f z ≤ f y} :=
      closure_minimal (fun y hy => (hf y hy).le)
        (isClosed_le continuous_const f.continuous)
    rw [hSc.closure_interior_eq_closure_of_nonempty_interior ⟨x, hx⟩] at hh
    exact fun y hy => hh (subset_closure hy)
  refine ⟨-(‖q‖⁻¹ • q), ?_, ?_⟩
  · simp [norm_smul, hqp.ne']
  · intro y hy
    rw [inner_neg_left, inner_smul_left, hq, map_sub]
    exact neg_nonpos.mpr (mul_nonneg (inv_nonneg.mpr hqp.le) (sub_nonneg.mpr (hfS y hy)))

/-- The nearest boundary point supplies an actual coordinate direction
whose one-sided width is at most the distance to the boundary. -/
theorem alexandrov_exists_thin_frame [NeZero n] {S : Set (E n)}
    (hS : IsCompact S) (hSc : Convex ℝ S) {x : E n} (hx : x ∈ interior S) :
    0 < Metric.infDist x (frontier S) ∧
      ∃ (b : OrthonormalBasis (Fin n) ℝ (E n)) (i₀ : Fin n),
        ∀ y ∈ S, b.repr (y - x) i₀ ≤ Metric.infDist x (frontier S) := by
  have hfront : (frontier S).Nonempty := nonempty_frontier_iff.mpr
    ⟨⟨x, interior_subset hx⟩, hS.ne_univ⟩
  have hδ : 0 < Metric.infDist x (frontier S) :=
    (Metric.infDist_pos_iff_notMem_closure hfront).mp (by
      rw [isClosed_frontier.closure_eq]
      exact fun hh => hh.2 hx)
  obtain ⟨z, hz, hdist⟩ := isClosed_frontier.exists_infDist_eq_dist hfront x
  obtain ⟨v, hv, hs⟩ := alexandrov_boundary_unit_normal hSc hx hz
  obtain ⟨b, i₀, hbi⟩ := alexandrov_exists_basis_vector hv
  refine ⟨hδ, b, i₀, ?_⟩
  intro y hy
  rw [b.repr_apply_apply, hbi]
  calc
    inner ℝ v (y - x) = inner ℝ v (y - z) + inner ℝ v (z - x) := by
      rw [← inner_add_right]
      congr 1
      module
    _ ≤ inner ℝ v (z - x) := by linarith [hs y hy]
    _ ≤ ‖v‖ * ‖z - x‖ := real_inner_le_norm _ _
    _ = Metric.infDist x (frontier S) := by rw [hv, one_mul, hdist, dist_eq_norm, norm_sub_rev]

/-- The distance-to-boundary Aleksandrov estimate in inverse form. The
only hypotheses are finite convexity, a compact convex body, a strict
interior depth, and lower boundary values. All geometry and slope-volume
estimates have been derived above. -/
theorem alexandrov_boundaryDistance_volume_le [NeZero n] {u : E n → ℝ}
    (hu : ConvexOn ℝ univ u) {S : Set (E n)} (hS : IsCompact S)
    (hSc : Convex ℝ S) {x : E n} (hx : x ∈ interior S)
    {a : ℝ} (hdepth : u x < a) (hb : ∀ y ∈ frontier S, a ≤ u y) :
    ENNReal.ofReal ((a - u x) / (2 * Metric.infDist x (frontier S))) *
      ENNReal.ofReal ((a - u x) / (((n : ℝ) + 1) * Metric.diam S)) ^ (n - 1) ≤
      volume (subgradientImage u (interior S)) := by
  classical
  obtain ⟨hδ, b, i₀, hthin⟩ := alexandrov_exists_thin_frame hS hSc hx
  have hfront : (frontier S).Nonempty := nonempty_frontier_iff.mpr
    ⟨⟨x, interior_subset hx⟩, hS.ne_univ⟩
  obtain ⟨z, hz⟩ := hfront
  have hD : 0 < Metric.diam S := lt_of_lt_of_le hδ
    ((Metric.infDist_le_dist_of_mem hz).trans
      (Metric.dist_le_diam_of_mem hS.isBounded (interior_subset hx) (hS.isClosed.frontier_subset hz)))
  have hc : Continuous u := continuousOn_univ.mp (hu.continuousOn isOpen_univ)
  have hh := alexandrov_anisotropic_volume_le hu hc hS (interior_subset hx) b i₀ hδ hD hdepth hb
    (fun y hy => hthin y (hS.isClosed.frontier_subset hy)) (fun y hy i => ?_)
  · simpa [two_mul] using hh
  · calc
      |b.repr (y - x) i| = |inner ℝ (b i) (y - x)| := by rw [b.repr_apply_apply]
      _ ≤ ‖b i‖ * ‖y - x‖ := abs_real_inner_le_norm _ _
      _ = ‖y - x‖ := by rw [b.orthonormal.norm_eq_one, one_mul]
      _ ≤ Metric.diam S := by
        rw [← dist_eq_norm]
        exact Metric.dist_le_diam_of_mem hS.isBounded (hS.isClosed.frontier_subset hy) (interior_subset hx)

/-- Aleksandrov's maximum principle with an explicit dimension constant:
`depth^n ≤ 2(n+1)^(n−1) distance_to_boundary diameter^(n−1) MA(S)`.
Here `MA(S)` is the actual Lebesgue measure of the literal subgradient
image. The extended-real statement also handles infinite image volume. -/
theorem alexandrov_maximum_principle [NeZero n] {u : E n → ℝ}
    (hu : ConvexOn ℝ univ u) {S : Set (E n)} (hS : IsCompact S)
    (hSc : Convex ℝ S) {x : E n} (hx : x ∈ interior S)
    {a : ℝ} (hdepth : u x < a) (hb : ∀ y ∈ frontier S, a ≤ u y) :
    ENNReal.ofReal ((a - u x) ^ n) ≤
      ENNReal.ofReal (2 * ((n : ℝ) + 1) ^ (n - 1) *
        Metric.infDist x (frontier S) * Metric.diam S ^ (n - 1)) *
      volume (subgradientImage u (interior S)) := by
  have hvol := alexandrov_boundaryDistance_volume_le hu hS hSc hx hdepth hb
  have hδ := (alexandrov_exists_thin_frame hS hSc hx).1
  have hfront : (frontier S).Nonempty := nonempty_frontier_iff.mpr
    ⟨⟨x, interior_subset hx⟩, hS.ne_univ⟩
  obtain ⟨z, hz⟩ := hfront
  have hD : 0 < Metric.diam S := lt_of_lt_of_le hδ
    ((Metric.infDist_le_dist_of_mem hz).trans
      (Metric.dist_le_diam_of_mem hS.isBounded (interior_subset hx) (hS.isClosed.frontier_subset hz)))
  let H := a - u x
  let d := Metric.infDist x (frontier S)
  let D := Metric.diam S
  let C := 2 * ((n : ℝ) + 1) ^ (n - 1) * d * D ^ (n - 1)
  have hH : 0 ≤ H := (sub_pos.mpr hdepth).le
  have hC : 0 ≤ C := by dsimp [C, d, D]; positivity
  have hN : (n : ℝ) + 1 ≠ 0 := by positivity
  have hp : H ^ n = H * H ^ (n - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n))]
    rw [pow_succ, mul_comm]
  have he : H ^ n = C * (H / (2 * d) * (H / (((n : ℝ) + 1) * D)) ^ (n - 1)) := by
    rw [hp]
    dsimp [C]
    rw [div_pow, mul_pow]
    field_simp [show d ≠ 0 from hδ.ne', show D ≠ 0 from hD.ne', hN]
  change ENNReal.ofReal (H ^ n) ≤ ENNReal.ofReal C * _
  rw [he, ENNReal.ofReal_mul hC, ENNReal.ofReal_mul (by positivity : 0 ≤ H / (2 * d)),
    ENNReal.ofReal_pow (by positivity : 0 ≤ H / (((n : ℝ) + 1) * D))]
  exact mul_le_mul_left' hvol _

/-- A supporting slope is bounded by the oscillation on an actual ball.
This holds even at nondifferentiability points. -/
lemma alexandrov_support_norm_le {u : E n → ℝ} {p x : E n}
    (hp : SupportsAt u p x) {r m a : ℝ} (hr : 0 < r)
    (hlow : m ≤ u x) (hup : ∀ y ∈ Metric.closedBall x r, u y ≤ a) :
    ‖p‖ ≤ (a - m) / r := by
  have hma : m ≤ a := hlow.trans (hup x (Metric.mem_closedBall_self hr.le))
  by_cases hp0 : p = 0
  · subst p
    simpa using div_nonneg (sub_nonneg.mpr hma) hr.le
  have hpn : 0 < ‖p‖ := norm_pos_iff.mpr hp0
  let y := x + (r / ‖p‖) • p
  have hy : y ∈ Metric.closedBall x r := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    dsimp [y]
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos hr hpn), div_mul_cancel₀ _ hpn.ne']
  have hs := hp y
  have hu := hup y hy
  have hi : inner ℝ p (y - x) = r * ‖p‖ := by
    dsimp [y]
    rw [add_sub_cancel_left, inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  rw [hi] at hs
  apply (le_div_iff₀ hr).mpr
  nlinarith

/-- A genuine oscillation bound on a buffer around a source set confines
its entire literal subgradient image to a Euclidean ball. -/
theorem alexandrov_subgradientImage_subset_closedBall {u : E n → ℝ}
    {A : Set (E n)} {r m a : ℝ} (hr : 0 < r)
    (hlow : ∀ x ∈ A, m ≤ u x)
    (hup : ∀ x ∈ A, ∀ y ∈ Metric.closedBall x r, u y ≤ a) :
    subgradientImage u A ⊆ Metric.closedBall (0 : E n) ((a - m) / r) := by
  rintro p ⟨x, hx, hp⟩
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    alexandrov_support_norm_le hp hr (hlow x hx) (hup x hx)

/-- Every finite continuous convex potential has compact subgradient
images on compact source sets, even without a global Lipschitz bound. -/
theorem alexandrov_isCompact_subgradientImage {u : E n → ℝ}
    (huc : Continuous u) {A : Set (E n)} (hA : IsCompact A) :
    IsCompact (subgradientImage u A) := by
  obtain ⟨R, hR⟩ := hA.isBounded.subset_closedBall (0 : E n)
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : E n) (R + 1)).exists_bound_of_continuousOn
    huc.continuousOn
  have hbuffer : ∀ x ∈ A, Metric.closedBall x 1 ⊆ Metric.closedBall (0 : E n) (R + 1) := by
    intro x hx
    apply Metric.closedBall_subset_closedBall'
    have hh := hR hx
    rw [Metric.mem_closedBall] at hh
    linarith
  have hsub : subgradientImage u A ⊆ Metric.closedBall (0 : E n) (2 * M) := by
    have hh := alexandrov_subgradientImage_subset_closedBall (u := u) (A := A)
      (r := 1) (m := -M) (a := M) (by norm_num)
      (fun x hx => ?_) (fun x hx y hy => ?_)
    · simpa [two_mul] using hh
    · have hb := hM x (hbuffer x hx (Metric.mem_closedBall_self (by norm_num)))
      rw [Real.norm_eq_abs] at hb
      exact (neg_le_neg hb).trans (neg_abs_le _)
    · have hb := hM y (hbuffer x hx hy)
      rw [Real.norm_eq_abs] at hb
      exact (le_abs_self _).trans hb
  let G := (A ×ˢ Metric.closedBall (0 : E n) (2 * M)) ∩
    {z : E n × E n | SupportsAt u z.2 z.1}
  have hG : IsCompact G := (hA.prod (isCompact_closedBall 0 (2 * M))).inter_right
    (isClosed_supportsAt_graph huc)
  have he : subgradientImage u A = Prod.snd '' G := by
    ext p
    constructor
    · rintro ⟨x, hx, hs⟩
      exact ⟨(x, p), ⟨⟨hx, hsub ⟨x, hx, hs⟩⟩, hs⟩, rfl⟩
    · rintro ⟨⟨x, p⟩, ⟨⟨hx, _⟩, hs⟩, rfl⟩
      exact ⟨x, hx, hs⟩
  rw [he]
  exact hG.image continuous_snd

lemma alexandrov_subgradientImage_mono (u : E n → ℝ) {A B : Set (E n)} (hAB : A ⊆ B) :
    subgradientImage u A ⊆ subgradientImage u B := by
  rintro p ⟨x, hx, hp⟩
  exact ⟨x, hAB hx, hp⟩

/-- Ordinary-real form of the maximum principle. Finiteness of the actual
subgradient image is proved from compactness and continuity, not assumed. -/
theorem alexandrov_maximum_principle_real [NeZero n] {u : E n → ℝ}
    (hu : ConvexOn ℝ univ u) {S : Set (E n)} (hS : IsCompact S)
    (hSc : Convex ℝ S) {x : E n} (hx : x ∈ interior S)
    {a : ℝ} (hdepth : u x < a) (hb : ∀ y ∈ frontier S, a ≤ u y) :
    (a - u x) ^ n ≤
      (2 * ((n : ℝ) + 1) ^ (n - 1) *
        Metric.infDist x (frontier S) * Metric.diam S ^ (n - 1)) *
      volume.real (subgradientImage u (interior S)) := by
  have hc : Continuous u := continuousOn_univ.mp (hu.continuousOn isOpen_univ)
  have hfinite : volume (subgradientImage u (interior S)) ≠ ⊤ :=
    ne_top_of_le_ne_top (alexandrov_isCompact_subgradientImage hc hS).measure_lt_top.ne
      (measure_mono (alexandrov_subgradientImage_mono u interior_subset))
  have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite)
    (alexandrov_maximum_principle hu hS hSc hx hdepth hb)
  have hH : 0 ≤ a - u x := (sub_pos.mpr hdepth).le
  have hd : 0 ≤ Metric.infDist x (frontier S) := Metric.infDist_nonneg
  have hD : 0 ≤ Metric.diam S := Metric.diam_nonneg
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ (a - u x) ^ n),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * ((n : ℝ) + 1) ^ (n - 1) *
      Metric.infDist x (frontier S) * Metric.diam S ^ (n - 1)), Measure.real] using hh

/-- Affine tilts translate literal supporting slopes. -/
lemma alexandrov_support_affine_tilt_iff (u : E n → ℝ) (p q x : E n) (c : ℝ) :
    SupportsAt (fun y => u y - inner ℝ p y - c) q x ↔ SupportsAt u (q + p) x := by
  constructor <;> intro h y <;> have hh := h y
  · simp only [inner_sub_right, inner_add_left] at hh ⊢
    linarith
  · simp only [inner_sub_right, inner_add_left] at hh ⊢
    linarith

/-- The actual Alexandrov mass is unchanged by subtracting an affine
function; this is Lebesgue translation invariance of the slope image. -/
theorem alexandrov_volume_affine_tilt (u : E n → ℝ) (p : E n) (c : ℝ) (A : Set (E n)) :
    volume (subgradientImage (fun y => u y - inner ℝ p y - c) A) =
      volume (subgradientImage u A) := by
  have he : subgradientImage (fun y => u y - inner ℝ p y - c) A =
      (fun q => q + p) ⁻¹' subgradientImage u A := by
    ext q
    simp only [subgradientImage, mem_setOf_eq, mem_preimage,
      alexandrov_support_affine_tilt_iff]
  rw [he, measure_preimage_add_right]

/-- A normalized convex section has a definite minimum depth when its
actual Alexandrov mass has a positive lower density on the inner half ball.
The conclusion is polynomial, so no root convention is required. -/
theorem alexandrov_normalized_depth_lower [NeZero n] {u : E n → ℝ}
    {S : Set (E n)} (hball : Metric.closedBall (0 : E n) 1 ⊆ S)
    {H lam : ℝ} (hlam : 0 ≤ lam) (hbound : ∀ x ∈ S, -H ≤ u x ∧ u x ≤ 0)
    (hmass : ENNReal.ofReal lam * volume (Metric.closedBall (0 : E n) (1 / 2)) ≤
      volume (subgradientImage u (Metric.closedBall (0 : E n) (1 / 2)))) :
    lam ≤ 4 ^ n * H ^ n := by
  have h0 := hbound 0 (hball (Metric.mem_closedBall_self (by norm_num)))
  have hH : 0 ≤ H := by linarith [h0.1, h0.2]
  have hbuffer : ∀ x ∈ Metric.closedBall (0 : E n) (1 / 2),
      Metric.closedBall x (1 / 2) ⊆ S := by
    intro x hx
    apply Set.Subset.trans ?_ hball
    apply Metric.closedBall_subset_closedBall'
    rw [Metric.mem_closedBall] at hx
    linarith
  have hsub : subgradientImage u (Metric.closedBall (0 : E n) (1 / 2)) ⊆
      Metric.closedBall (0 : E n) (2 * H) := by
    have hh := alexandrov_subgradientImage_subset_closedBall (u := u)
      (A := Metric.closedBall (0 : E n) (1 / 2)) (r := 1 / 2) (m := -H) (a := 0)
      (by norm_num)
      (fun x hx => (hbound x (hball (Metric.closedBall_subset_closedBall (by norm_num) hx))).1)
      (fun x hx y hy => (hbound y (hbuffer x hx hy)).2)
    simpa [div_eq_mul_inv, mul_comm] using hh
  have hh := hmass.trans (measure_mono hsub)
  rw [volume.addHaar_closedBall (0 : E n) (by norm_num : (0 : ℝ) ≤ 1 / 2),
    volume.addHaar_closedBall (0 : E n) (by positivity : 0 ≤ 2 * H)] at hh
  have hpos : volume (Metric.ball (0 : E n) 1) ≠ 0 :=
    (Metric.isOpen_ball.measure_pos volume ⟨0, Metric.mem_ball_self (by norm_num)⟩).ne'
  have hfin : volume (Metric.ball (0 : E n) 1) ≠ ⊤ :=
    ne_top_of_le_ne_top (isCompact_closedBall (0 : E n) 1).measure_lt_top.ne
      (measure_mono Metric.ball_subset_closedBall)
  rw [← mul_assoc, ENNReal.mul_le_mul_right hpos hfin,
    ← ENNReal.ofReal_mul hlam] at hh
  have hh' : lam * (1 / 2 : ℝ) ^ n ≤ (2 * H) ^ n := by
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
    simpa [E, Reference.Space] using hh
  have hm := mul_le_mul_of_nonneg_right hh' (by positivity : 0 ≤ (2 : ℝ) ^ n)
  calc
    lam = (lam * (1 / 2 : ℝ) ^ n) * 2 ^ n := by
      rw [mul_assoc, ← mul_pow]
      norm_num
    _ ≤ (2 * H) ^ n * 2 ^ n := hm
    _ = 4 ^ n * H ^ n := by rw [mul_pow, mul_assoc, mul_comm (H ^ n), ← mul_assoc, ← mul_pow]; norm_num

/-- Direct section form of the genuine maximum principle. Compactness of
the affine sublevel section is the only section hypothesis; boundary
values, interior membership, convexity and affine invariance of the
Alexandrov mass are all discharged here. -/
theorem alexandrov_section_maximum_principle [NeZero n] {u : E n → ℝ}
    (hu : ConvexOn ℝ univ u) (p : E n) (a : ℝ)
    (hS : IsCompact {y | u y - inner ℝ p y ≤ a}) {x : E n}
    (hx : u x - inner ℝ p x < a) :
    ENNReal.ofReal ((a - (u x - inner ℝ p x)) ^ n) ≤
      ENNReal.ofReal (2 * ((n : ℝ) + 1) ^ (n - 1) *
        Metric.infDist x (frontier {y | u y - inner ℝ p y ≤ a}) *
        Metric.diam {y | u y - inner ℝ p y ≤ a} ^ (n - 1)) *
      volume (subgradientImage u (interior {y | u y - inner ℝ p y ≤ a})) := by
  let F := fun y => u y - inner ℝ p y
  have hFc : ConvexOn ℝ univ F := alexandrov_convex_tilt hu p
  have hF : Continuous F := continuousOn_univ.mp (hFc.continuousOn isOpen_univ)
  have hSc : Convex ℝ {y | F y ≤ a} := by simpa using hFc.convex_le a
  have hxi : x ∈ interior {y | F y ≤ a} := by
    apply mem_interior_iff_mem_nhds.mpr
    apply Filter.mem_of_superset ((isOpen_lt hF continuous_const).mem_nhds hx)
    exact fun y (hy : F y < a) => hy.le
  have hh := alexandrov_maximum_principle hFc hS hSc hxi hx
    (fun y hy => (frontier_le_subset_eq hF continuous_const hy).ge)
  have he : volume (subgradientImage F (interior {y | F y ≤ a})) =
      volume (subgradientImage u (interior {y | F y ≤ a})) := by
    simpa [F] using alexandrov_volume_affine_tilt u p 0 (interior {y | F y ≤ a})
  rw [he] at hh
  exact hh

end GaussianTilt.MomentMapRegularity
