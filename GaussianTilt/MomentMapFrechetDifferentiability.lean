import GaussianTilt.MomentMapCoordinateDifferentiability

/-! # Coordinate differentiability implies full differentiability for convex functions

Finite Jensen averaging bounds the increment by the coordinate increments.
Applying this also to the opposite increment traps the full remainder
between two little-o expressions. Thus the Fubini full-measure coordinate
set is a genuine Fréchet differentiability set.
-/
noncomputable section
open MeasureTheory Filter Set Asymptotics
open scoped Topology ENNReal NNReal BigOperators
namespace GaussianTilt.MomentMapCoercivity
variable {n : ℕ}

lemma sum_coordinate_vectors (h : E n) : (∑ i : Fin n, h i • unitCoordinate i) = h := by
  ext j
  change (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) j) (∑ i : Fin n, h i • unitCoordinate i) = h j
  rw [map_sum]
  simp [unitCoordinate, PiLp.proj_apply, Pi.single_apply]

lemma convex_coordinate_average {φ : E n → ℝ} (hφ : ConvexOn ℝ univ φ)
    (hn : 0 < n) (x h : E n) :
    φ (x + h) ≤ (n : ℝ)⁻¹ * ∑ i : Fin n, φ (x + ((n : ℝ) * h i) • unitCoordinate i) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsum : (∑ i : Fin n, (n : ℝ)⁻¹) = 1 := by simp [hn0]
  have heq : (∑ i : Fin n, (n : ℝ)⁻¹ •
      (x + ((n : ℝ) * h i) • unitCoordinate i)) = x + h := by
    simp only [smul_add, smul_smul, ← mul_assoc, inv_mul_cancel₀ hn0, one_mul,
      Finset.sum_add_distrib]
    rw [sum_coordinate_vectors]
    congr 1
    ext j
    simp [hn0, mul_assoc]
  have hj := hφ.map_sum_le (t := Finset.univ) (w := fun _ : Fin n => (n : ℝ)⁻¹)
    (p := fun i => x + ((n : ℝ) * h i) • unitCoordinate i)
    (fun _ _ => by positivity) hsum (fun _ _ => mem_univ _)
  rw [heq] at hj
  simpa only [smul_eq_mul, ← Finset.mul_sum] using hj

def coordinateLinear (d : Fin n → ℝ) : E n →L[ℝ] ℝ :=
  ∑ i, d i • PiLp.proj 2 (fun _ : Fin n => ℝ) i

lemma coordinateLinear_apply (d : Fin n → ℝ) (h : E n) : coordinateLinear d h = ∑ i, d i * h i := by
  simp [coordinateLinear, ContinuousLinearMap.sum_apply, PiLp.proj_apply]

def coordinateRemainder (φ : E n → ℝ) (x : E n) (d : Fin n → ℝ) (i : Fin n) (t : ℝ) : ℝ :=
  φ (x + t • unitCoordinate i) - φ x - d i * t

def averageCoordinateRemainder (φ : E n → ℝ) (x : E n) (d : Fin n → ℝ) (h : E n) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, coordinateRemainder φ x d i ((n : ℝ) * h i)

lemma convex_remainder_upper {φ : E n → ℝ} (hφ : ConvexOn ℝ univ φ) (hn : 0 < n)
    (x h : E n) (d : Fin n → ℝ) :
    φ (x + h) - φ x - coordinateLinear d h ≤ averageCoordinateRemainder φ x d h := by
  have hj := convex_coordinate_average hφ hn x h
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hs : (∑ i : Fin n, coordinateRemainder φ x d i ((n : ℝ) * h i)) =
      (∑ i : Fin n, φ (x + ((n : ℝ) * h i) • unitCoordinate i)) -
        (n : ℝ) * φ x - (n : ℝ) * coordinateLinear d h := by
    simp only [coordinateRemainder, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, coordinateLinear_apply, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [averageCoordinateRemainder, hs]
  have heq : (n : ℝ)⁻¹ *
      ((∑ i : Fin n, φ (x + ((n : ℝ) * h i) • unitCoordinate i)) -
        (n : ℝ) * φ x - (n : ℝ) * coordinateLinear d h) =
      (n : ℝ)⁻¹ * (∑ i : Fin n, φ (x + ((n : ℝ) * h i) • unitCoordinate i)) - φ x - coordinateLinear d h := by
    field_simp
  rw [heq]
  linarith

lemma convex_remainder_abs_bound {φ : E n → ℝ} (hφ : ConvexOn ℝ univ φ) (hn : 0 < n)
    (x h : E n) (d : Fin n → ℝ) :
    |φ (x + h) - φ x - coordinateLinear d h| ≤
      |averageCoordinateRemainder φ x d h| + |averageCoordinateRemainder φ x d (-h)| := by
  have hupper := convex_remainder_upper hφ hn x h d
  have hlower := convex_remainder_upper hφ hn x (-h) d
  have hmid := hφ.2 (mem_univ (x + h)) (mem_univ (x + -h))
    (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num)
  have he : (1 / 2 : ℝ) • (x + h) + (1 / 2 : ℝ) • (x + -h) = x := by module
  rw [he] at hmid
  simp only [smul_eq_mul] at hmid
  rw [map_neg] at hlower
  apply abs_le.mpr
  constructor
  · linarith [le_abs_self (averageCoordinateRemainder φ x d (-h)), abs_nonneg (averageCoordinateRemainder φ x d h)]
  · linarith [le_abs_self (averageCoordinateRemainder φ x d h), abs_nonneg (averageCoordinateRemainder φ x d (-h))]

theorem convex_hasFDerivAt_of_coordinate_derivatives {φ : E n → ℝ}
    (hφ : ConvexOn ℝ univ φ) (hn : 0 < n) (x : E n) (d : Fin n → ℝ)
    (hd : ∀ i, HasDerivAt (affineLine φ (unitCoordinate i) x) (d i) 0) :
    HasFDerivAt φ (coordinateLinear d) x := by
  have hr (i : Fin n) : coordinateRemainder φ x d i =o[𝓝 0] (fun t : ℝ => t) := by
    change (fun t : ℝ => φ (x + t • unitCoordinate i) - φ x - d i * t) =o[𝓝 0] (fun t : ℝ => t)
    have h := hasDerivAt_iff_isLittleO_nhds_zero.mp (hd i)
    simpa only [affineLine, zero_add, zero_smul, add_zero, smul_eq_mul, mul_comm] using h
  have hcoord (i : Fin n) : (fun h : E n => coordinateRemainder φ x d i ((n : ℝ) * h i)) =o[𝓝 0]
      (fun h : E n => h) := by
    let L : E n →L[ℝ] ℝ := (n : ℝ) • PiLp.proj 2 (fun _ : Fin n => ℝ) i
    have hL : Tendsto L (𝓝 0) (𝓝 (0 : ℝ)) := by simpa using L.continuous.tendsto (0 : E n)
    exact (hr i |>.comp_tendsto hL).trans_isBigO (L.isBigO_id _)
  have hU : averageCoordinateRemainder φ x d =o[𝓝 0] (fun h : E n => h) :=
    (Asymptotics.IsLittleO.sum (fun i _ => hcoord i)).const_mul_left _
  have hUneg : (fun h : E n => averageCoordinateRemainder φ x d (-h)) =o[𝓝 0] (fun h : E n => h) := by
    have h := hU.comp_tendsto (show Tendsto (fun h : E n => -h) (𝓝 0) (𝓝 0) by
      simpa using continuous_neg.tendsto (0 : E n))
    exact isLittleO_neg_right.mp h
  have hW := hU.abs_left.add hUneg.abs_left
  apply hasFDerivAt_iff_isLittleO_nhds_zero.mpr
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  filter_upwards [hW.bound hε] with h hh
  rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))] at hh
  rw [Real.norm_eq_abs]
  exact (convex_remainder_abs_bound hφ hn x h d).trans hh

theorem convex_differentiableAt_of_coordinate_derivatives {φ : E n → ℝ}
    (hφ : ConvexOn ℝ univ φ) (x : E n)
    (hd : ∀ i, DifferentiableAt ℝ (affineLine φ (unitCoordinate i) x) 0) :
    DifferentiableAt ℝ φ x := by
  by_cases hn : n = 0
  · subst n
    have he : φ = fun _ => φ x := by funext y; rw [Subsingleton.elim y x]
    rw [he]
    exact differentiableAt_const _
  · exact (convex_hasFDerivAt_of_coordinate_derivatives hφ (Nat.pos_of_ne_zero hn) x
      (fun i => deriv (affineLine φ (unitCoordinate i) x) 0) (fun i => (hd i).hasDerivAt)).differentiableAt

/-- Every finite convex potential on Euclidean space is Fréchet
differentiable almost everywhere. No Rademacher or subgradient axiom is used. -/
theorem convex_ae_differentiable {φ : E n → ℝ} (hφ : ConvexOn ℝ univ φ) :
    ∀ᵐ x ∂volume, DifferentiableAt ℝ φ x := by
  filter_upwards [convex_ae_all_coordinates_differentiable hφ] with x hx
  exact convex_differentiableAt_of_coordinate_derivatives hφ x hx

end GaussianTilt.MomentMapCoercivity
