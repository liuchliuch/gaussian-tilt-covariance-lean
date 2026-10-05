import GaussianTilt.MomentMapRegularitySecondOrderDirichletLimit
import GaussianTilt.MomentMapAlexandrovMaximum

/-! # The actual bounded-domain Aleksandrov maximum principle

Supporting slopes are constructed by compact minimization on the domain.
The anisotropic slope-box argument therefore gives the boundary-distance
estimate without a globally finite convex extension of the potential.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators Gradient NNReal ENNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

/-- A plane below the boundary can be slid to a genuine interior local-domain contact. -/
theorem alexandrovOn_slope_mem_subgradientImage {u : E n → ℝ}
    {S : Set (E n)} (huc : ContinuousOn u S) (hS : IsCompact S)
    {x p : E n} (hx : x ∈ S)
    (hb : ∀ y ∈ frontier S, u x + inner ℝ p (y - x) < u y) :
    p ∈ subgradientImageOn S u (interior S) := by
  let F := fun y => u y - inner ℝ p y
  have hF : ContinuousOn F S := huc.sub (continuous_const.inner continuous_id).continuousOn
  obtain ⟨z, hz, hmin⟩ := hS.exists_isMinOn ⟨x, hx⟩ hF
  have hzi : z ∈ interior S := by
    by_contra hzi
    have hzb : z ∈ frontier S := ⟨subset_closure hz, hzi⟩
    have hh := hb z hzb
    have hm := hmin hx
    dsimp [F] at hm
    rw [inner_sub_right] at hh
    linarith
  refine ⟨z, hzi, ?_⟩
  intro y hy
  have h := hmin hy
  change u z - inner ℝ p z ≤ u y - inner ℝ p y at h
  rw [inner_sub_right]
  linarith

theorem alexandrovOn_polar_subset_subgradientImage {u : E n → ℝ}
    {S : Set (E n)} (huc : ContinuousOn u S) (hS : IsCompact S) {x : E n} (hx : x ∈ S)
    {a : ℝ} (hb : ∀ y ∈ frontier S, a ≤ u y) :
    {p | ∀ y ∈ frontier S, inner ℝ p (y - x) < a - u x} ⊆
      subgradientImageOn S u (interior S) := by
  intro p hp
  apply alexandrovOn_slope_mem_subgradientImage huc hS hx
  intro y hy
  have hh := hp y hy
  have hy' := hb y hy
  linarith


theorem alexandrovOn_anisotropic_box_subset {ι : Type*} [Fintype ι] [DecidableEq ι]
    {u : E n → ℝ} {S : Set (E n)} (huc : ContinuousOn u S) (hS : IsCompact S) {x : E n} (hx : x ∈ S)
    (b : OrthonormalBasis ι ℝ (E n)) (i₀ : ι)
    {a d D : ℝ} (hd : 0 < d) (hD : 0 < D) (hdepth : u x < a)
    (hb : ∀ y ∈ frontier S, a ≤ u y)
    (hwidth : ∀ y ∈ frontier S, b.repr (y - x) i₀ ≤ d)
    (hdiam : ∀ y ∈ frontier S, ∀ i, |b.repr (y - x) i| ≤ D) :
    alexandrovSlopeBox b
      (fun i => if i = i₀ then 0 else -(a - u x) / (2 * (Fintype.card ι + 1) * D))
      (fun i => if i = i₀ then (a - u x) / (2 * d)
        else (a - u x) / (2 * (Fintype.card ι + 1) * D)) ⊆
      subgradientImageOn S u (interior S) := by
  apply Set.Subset.trans ?_ (alexandrovOn_polar_subset_subgradientImage huc hS hx hb)
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


theorem alexandrovOn_anisotropic_volume_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {u : E n → ℝ} {S : Set (E n)} (huc : ContinuousOn u S) (hS : IsCompact S) {x : E n} (hx : x ∈ S)
    (b : OrthonormalBasis ι ℝ (E n)) (i₀ : ι)
    {a d D : ℝ} (hd : 0 < d) (hD : 0 < D) (hdepth : u x < a)
    (hb : ∀ y ∈ frontier S, a ≤ u y)
    (hwidth : ∀ y ∈ frontier S, b.repr (y - x) i₀ ≤ d)
    (hdiam : ∀ y ∈ frontier S, ∀ i, |b.repr (y - x) i| ≤ D) :
    ENNReal.ofReal ((a - u x) / (2 * d)) *
      ENNReal.ofReal ((a - u x) / ((Fintype.card ι + 1) * D)) ^ (Fintype.card ι - 1) ≤
      volume (subgradientImageOn S u (interior S)) := by
  have hm := measure_mono (μ := volume)
    (alexandrovOn_anisotropic_box_subset huc hS hx b i₀ hd hD hdepth hb hwidth hdiam)
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


theorem alexandrovOn_boundaryDistance_volume_le [NeZero n] {u : E n → ℝ}
    {S : Set (E n)} (huc : ContinuousOn u S) (hS : IsCompact S)
    (hSc : Convex ℝ S) {x : E n} (hx : x ∈ interior S)
    {a : ℝ} (hdepth : u x < a) (hb : ∀ y ∈ frontier S, a ≤ u y) :
    ENNReal.ofReal ((a - u x) / (2 * Metric.infDist x (frontier S))) *
      ENNReal.ofReal ((a - u x) / (((n : ℝ) + 1) * Metric.diam S)) ^ (n - 1) ≤
      volume (subgradientImageOn S u (interior S)) := by
  classical
  obtain ⟨hδ, b, i₀, hthin⟩ := alexandrov_exists_thin_frame hS hSc hx
  have hfront : (frontier S).Nonempty := nonempty_frontier_iff.mpr
    ⟨⟨x, interior_subset hx⟩, hS.ne_univ⟩
  obtain ⟨z, hz⟩ := hfront
  have hD : 0 < Metric.diam S := lt_of_lt_of_le hδ
    ((Metric.infDist_le_dist_of_mem hz).trans
      (Metric.dist_le_diam_of_mem hS.isBounded (interior_subset hx) (hS.isClosed.frontier_subset hz)))
  have hh := alexandrovOn_anisotropic_volume_le huc hS (interior_subset hx) b i₀ hδ hD hdepth hb
    (fun y hy => hthin y (hS.isClosed.frontier_subset hy)) (fun y hy i => ?_)
  · simpa [two_mul] using hh
  · calc
      |b.repr (y - x) i| = |inner ℝ (b i) (y - x)| := by rw [b.repr_apply_apply]
      _ ≤ ‖b i‖ * ‖y - x‖ := abs_real_inner_le_norm _ _
      _ = ‖y - x‖ := by rw [b.orthonormal.norm_eq_one, one_mul]
      _ ≤ Metric.diam S := by
        rw [← dist_eq_norm]
        exact Metric.dist_le_diam_of_mem hS.isBounded (hS.isClosed.frontier_subset hy) (interior_subset hx)


theorem alexandrovOn_maximum_principle [NeZero n] {u : E n → ℝ}
    {S : Set (E n)} (huc : ContinuousOn u S) (hS : IsCompact S)
    (hSc : Convex ℝ S) {x : E n} (hx : x ∈ interior S)
    {a : ℝ} (hdepth : u x < a) (hb : ∀ y ∈ frontier S, a ≤ u y) :
    ENNReal.ofReal ((a - u x) ^ n) ≤
      ENNReal.ofReal (2 * ((n : ℝ) + 1) ^ (n - 1) *
        Metric.infDist x (frontier S) * Metric.diam S ^ (n - 1)) *
      volume (subgradientImageOn S u (interior S)) := by
  have hvol := alexandrovOn_boundaryDistance_volume_le huc hS hSc hx hdepth hb
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


end GaussianTilt.MomentMapRegularity
