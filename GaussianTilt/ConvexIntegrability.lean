import Mathlib

/-!
# Compact sublevels of integrable convex potentials

A finite-volume convex set containing a ball is bounded. The proof uses an
explicit affine rank-one expansion of a fixed ball, whose determinant grows
with any coordinate of a point of the set.
-/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace GaussianTilt.ConvexIntegrability
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)
variable {n : ℕ}

def rankShear (x : Space n) (i : Fin n) (r : ℝ) : Space n →ₗ[ℝ] Space n :=
  LinearMap.id + ((r⁻¹ • LinearMap.proj i).comp
    (EuclideanSpace.equiv (Fin n) ℝ).toLinearMap).smulRight x

lemma rankShear_apply (x y : Space n) (i : Fin n) (r : ℝ) :
    rankShear x i r y = y + (y i / r) • x := by
  simp only [rankShear, LinearMap.add_apply, LinearMap.id_apply,
    LinearMap.smulRight_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul]
  congr 2
  change r⁻¹ * y i = y i / r
  ring

lemma rankShear_det (x : Space n) (i : Fin n) (r : ℝ) :
    LinearMap.det (rankShear x i r) = 1 + x i / r := by
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let v : Fin n → ℝ := Pi.single i (r⁻¹)
  have hm : LinearMap.toMatrix b b (rankShear x i r) =
      1 + Matrix.replicateCol Unit (fun j ↦ x j) * Matrix.replicateRow Unit v := by
    ext j k
    simp only [LinearMap.toMatrix_apply, rankShear_apply, b,
      OrthonormalBasis.coe_toBasis, OrthonormalBasis.coe_toBasis_repr_apply,
      EuclideanSpace.basisFun_repr, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul, EuclideanSpace.basisFun_apply, EuclideanSpace.single_apply,
      Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply, Matrix.replicateCol_apply,
      Matrix.replicateRow_apply, Finset.univ_unique, Finset.sum_singleton, v]
    by_cases hki : k = i <;> by_cases hjk : j = k <;> simp_all [Pi.single_apply, eq_comm]
    <;> ring
  rw [← LinearMap.det_toMatrix b, hm, Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp [v, dotProduct, Pi.single_apply, div_eq_mul_inv, mul_comm]

lemma volume_image_add_right (c : Space n) (s : Set (Space n)) :
    volume ((fun x ↦ x + c) '' s) = volume s := by
  rw [show (fun x ↦ x + c) '' s = (fun x ↦ x + -c) ⁻¹' s by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩; simpa using hy
    · intro hx; exact ⟨x + -c, hx, by simp⟩]
  exact measure_preimage_add_right volume (-c) s

lemma expanded_ball_subset {C : Set (Space n)} (hC : Convex ℝ C)
    {r : ℝ} (hr : 0 < r) (hball : Metric.ball 0 r ⊆ C)
    {x : Space n} (hx : x ∈ C) (i : Fin n) :
    (fun y ↦ rankShear x i r y + (1 / 2 : ℝ) • x) '' Metric.ball 0 (r / 4) ⊆ C := by
  rintro z ⟨y, hy, rfl⟩
  have hy' : ‖y‖ < r / 4 := by simpa using hy
  have hi0 : |y i| ≤ ‖y‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le y i
  have hi : |y i| < r / 4 := hi0.trans_lt hy'
  let a : ℝ := 1 / 2 + y i / r
  have ha : 1 / 4 < a ∧ a < 3 / 4 := by
    have hd : -(1 / 4 : ℝ) < y i / r ∧ y i / r < 1 / 4 := by
      constructor
      · apply (lt_div_iff₀ hr).mpr; nlinarith [(abs_lt.mp hi).1]
      · apply (div_lt_iff₀ hr).mpr; nlinarith [(abs_lt.mp hi).2]
    dsimp [a]; constructor <;> linarith
  have hb : 0 < 1 - a := by linarith
  have hw : (1 - a)⁻¹ • y ∈ Metric.ball 0 r := by
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hb)]
    apply (inv_mul_lt_iff₀ hb).mpr
    nlinarith [mul_pos hr (show 0 < 3 / 4 - a by linarith)]
  have h := hC hx (hball hw) (show 0 ≤ a by linarith) hb.le (by ring : a + (1 - a) = 1)
  convert h using 1
  dsimp only
  rw [rankShear_apply, smul_smul, mul_inv_cancel₀ hb.ne', one_smul]
  dsimp [a]
  module

lemma volume_expanded_ball_le {C : Set (Space n)} (hC : Convex ℝ C)
    {r : ℝ} (hr : 0 < r) (hball : Metric.ball 0 r ⊆ C)
    {x : Space n} (hx : x ∈ C) (i : Fin n) :
    ENNReal.ofReal |1 + x i / r| * volume (Metric.ball (0 : Space n) (r / 4)) ≤ volume C := by
  have h := measure_mono (μ := volume) (expanded_ball_subset hC hr hball hx i)
  rw [show (fun y ↦ rankShear x i r y + (1 / 2 : ℝ) • x) '' Metric.ball 0 (r / 4) =
    (fun z ↦ z + (1 / 2 : ℝ) • x) '' (rankShear x i r '' Metric.ball 0 (r / 4)) by
      rw [Set.image_image],
    volume_image_add_right, Measure.addHaar_image_linearMap, rankShear_det] at h
  exact h

theorem isBounded_of_convex_volume_lt_top {C : Set (Space n)} (hC : Convex ℝ C)
    {r : ℝ} (hr : 0 < r) (hball : Metric.ball 0 r ⊆ C) (hfinite : volume C < ⊤) :
    Bornology.IsBounded C := by
  let D := Metric.ball (0 : Space n) (r / 4)
  have hDpos : 0 < volume D := Metric.isOpen_ball.measure_pos volume
    ⟨0, by simpa [D] using (show (0 : ℝ) < r / 4 by positivity)⟩
  have hDfinite : volume D < ⊤ :=
    (measure_mono Metric.ball_subset_closedBall).trans_lt (isCompact_closedBall (0 : Space n) (r / 4)).measure_lt_top
  have hm : 0 < (volume D).toReal := ENNReal.toReal_pos hDpos.ne' hDfinite.ne
  let B : ℝ := ((volume C).toReal / (volume D).toReal + 1) * r
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hb (x : Space n) (hx : x ∈ C) (i : Fin n) : |x i| ≤ B := by
    have h := volume_expanded_ball_le hC hr hball hx i
    have hreal := ENNReal.toReal_mono hfinite.ne h
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)] at hreal
    change |1 + x i / r| * (volume D).toReal ≤ (volume C).toReal at hreal
    have hc := (le_div_iff₀ hm).mpr hreal
    have hd : |x i / r| ≤ |1 + x i / r| + 1 := by
      calc
        |x i / r| = |(1 + x i / r) + (-1)| := by congr 1; ring
        _ ≤ |1 + x i / r| + |-1| := abs_add_le _ _
        _ = |1 + x i / r| + 1 := by norm_num
    have hratio : |x i| / r ≤ (volume C).toReal / (volume D).toReal + 1 := by
      rw [← abs_of_pos hr, ← abs_div]
      linarith
    exact (div_le_iff₀ hr).mp hratio
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨Real.sqrt ((n : ℝ) * B ^ 2), ?_⟩
  intro x hx
  apply (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
  rw [EuclideanSpace.norm_sq_eq]
  calc
    ∑ i : Fin n, ‖x i‖ ^ 2 ≤ ∑ i : Fin n, B ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact pow_le_pow_left₀ (norm_nonneg _) (by simpa only [Real.norm_eq_abs] using hb x hx i) 2
    _ = (n : ℝ) * B ^ 2 := by simp

lemma convexPotential_sublevel_volume_lt_top {φ : Space n → ℝ}
    (hint : Integrable (fun x ↦ Real.exp (-φ x))) (a : ℝ) :
    volume {x | φ x ≤ a} < ⊤ := by
  have heq : {x | φ x ≤ a} = {x | Real.exp (-a) ≤ Real.exp (-φ x)} := by
    ext x; simp
  rw [heq]
  exact hint.measure_ge_lt_top (Real.exp_pos _)

/-- Integrability of an everywhere-finite continuous convex potential's
exponential proves compactness of every sublevel, in all finite dimensions. -/
theorem convexPotential_compact_sublevel {φ : Space n → ℝ}
    (hφ : Continuous φ) (hconv : ConvexOn ℝ univ φ)
    (hint : Integrable (fun x ↦ Real.exp (-φ x))) (a : ℝ) :
    IsCompact {x | φ x ≤ a} := by
  let b : ℝ := max a (φ 0) + 1
  have hzero : φ 0 < b := by dsimp [b]; linarith [le_max_right a (φ 0)]
  have hn : {x | φ x ≤ b} ∈ nhds (0 : Space n) := by
    exact Filter.mem_of_superset (hφ.continuousAt.preimage_mem_nhds (Iio_mem_nhds hzero))
      (fun x hx ↦ show φ x ≤ b from le_of_lt hx)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hn
  have hc : Convex ℝ {x | φ x ≤ b} := by simpa using hconv.convex_le b
  have hbound := isBounded_of_convex_volume_lt_top hc hr hball
    (convexPotential_sublevel_volume_lt_top hint b)
  apply Metric.isCompact_of_isClosed_isBounded (isClosed_le hφ continuous_const)
  apply hbound.subset
  intro x hx
  change φ x ≤ a at hx
  change φ x ≤ b
  exact hx.trans (by dsimp [b]; linarith [le_max_left a (φ 0)])

theorem convexPotential_attains_minimum {φ : Space n → ℝ}
    (hφ : Continuous φ) (hconv : ConvexOn ℝ univ φ)
    (hint : Integrable (fun x ↦ Real.exp (-φ x))) :
    ∃ x : Space n, ∀ y : Space n, φ x ≤ φ y := by
  obtain ⟨x, hx, hmin⟩ := (convexPotential_compact_sublevel hφ hconv hint (φ 0)).exists_isMinOn
    ⟨(0 : Space n), show φ 0 ≤ φ 0 from le_rfl⟩ hφ.continuousOn
  refine ⟨x, fun y ↦ ?_⟩
  by_cases hy : φ y ≤ φ 0
  · exact hmin hy
  · exact (show φ x ≤ φ 0 from hx).trans (le_of_not_ge hy)

end GaussianTilt.ConvexIntegrability
