import GaussianTilt.LetwinMomentLaw
import GaussianTilt.PaourisGaussianBlocks

/-! # Genuine Gaussian Stein noise for the compact-law approximation -/
noncomputable section
open MeasureTheory Matrix Set
open scoped BigOperators ContDiff ENNReal InnerProductSpace
namespace GaussianTilt.Letwin

abbrev euclideanCoordinates (n : ℕ) : Reference.Space n ≃L[ℝ] CoordinateSpace n :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)

def coordinateGaussian (n : ℕ) : Measure (CoordinateSpace n) :=
  (Paouris.standardGaussian n).map (euclideanCoordinates n)

instance coordinateGaussian_probability (n : ℕ) : IsProbabilityMeasure (coordinateGaussian n) :=
  Measure.isProbabilityMeasure_map (euclideanCoordinates n).continuous.measurable.aemeasurable

lemma integral_coordinateGaussian {n : ℕ} (f : CoordinateSpace n → ℝ) :
    (∫ x, f x ∂coordinateGaussian n) = ∫ x, f (euclideanCoordinates n x) ∂Paouris.standardGaussian n :=
  (euclideanCoordinates n).toHomeomorph.measurableEmbedding.integral_map f

lemma euclideanCoordinates_coordinateVector {n : ℕ} (i : Fin n) :
    euclideanCoordinates n (Paouris.coordinateVector i) = Pi.single i 1 := by
  ext j
  simp [Paouris.coordinateVector_apply, Pi.single_apply]

lemma fderiv_coordinate_pullback {n : ℕ} {g : CoordinateSpace n → ℝ}
    (hg : Differentiable ℝ g) (i : Fin n) (x : Reference.Space n) :
    fderiv ℝ (g ∘ euclideanCoordinates n) x (Paouris.coordinateVector i) =
      coordinateDerivative i g (euclideanCoordinates n x) := by
  rw [fderiv_comp x (hg _) (euclideanCoordinates n).differentiableAt,
    (euclideanCoordinates n).fderiv, ContinuousLinearMap.comp_apply]
  rw [show (euclideanCoordinates n).toContinuousLinearMap (Paouris.coordinateVector i) =
    Pi.single i 1 from euclideanCoordinates_coordinateVector i]
  rfl

/-- Standard Gaussian Stein identity on the exact coordinate law. The
integrability obligations are discharged by actual Gaussian first moments. -/
theorem coordinateGaussian_stein_identity {n : ℕ} {g : CoordinateSpace n → ℝ}
    (hg : ContDiff ℝ 1 g) (C D : ℝ)
    (hgB : ∀ x, |g x| ≤ C) (hD : ∀ x j, |coordinateDerivative j g x| ≤ D)
    (i : Fin n) :
    (∫ x, x i * g x ∂coordinateGaussian n) =
      ∫ x, coordinateDerivative i g x ∂coordinateGaussian n := by
  let q := g ∘ euclideanCoordinates n
  have hq : ContDiff ℝ 1 q := hg.comp (euclideanCoordinates n).contDiff
  have hqi : Integrable q (Paouris.standardGaussian n) :=
    Paouris.standardGaussian_integrable_of_bound hq.continuous (fun x => hgB _)
  have hdq : Integrable (fun x => fderiv ℝ q x (Paouris.coordinateVector i))
      (Paouris.standardGaussian n) := by
    simp only [q, fderiv_coordinate_pullback (hg.differentiable le_rfl)]
    apply Paouris.standardGaussian_integrable_of_bound
      (((contDiff_coordinateDerivative hg (m := 0) (by norm_num) i).continuous).comp
        (euclideanCoordinates n).continuous)
    exact fun x => hD _ i
  have hprod : Integrable (fun x => ⟪x, Paouris.coordinateVector i⟫_ℝ * q x)
      (Paouris.standardGaussian n) :=
    Paouris.standardGaussian_inner_mul_integrable_of_bound hq.continuous (fun x => hgB _) _
  have h := Paouris.standardGaussian_integration_by_parts (hq.differentiable le_rfl)
    (Paouris.coordinateVector i) hqi hdq hprod
  rw [integral_coordinateGaussian, integral_coordinateGaussian]
  simpa only [q, fderiv_coordinate_pullback (hg.differentiable le_rfl),
    Paouris.coordinateVector_inner_right, Function.comp_apply] using h.symm

lemma coordinateGaussian_coordinate_integrable {n : ℕ} (i : Fin n) :
    Integrable (fun x : CoordinateSpace n => x i) (coordinateGaussian n) := by
  exact (euclideanCoordinates n).toHomeomorph.measurableEmbedding.integrable_map_iff.mpr
    (Paouris.standardGaussian_coordinate_integrable i)

lemma coordinateGaussian_coordinate_memLp {n : ℕ} (i : Fin n) :
    MemLp (fun x : CoordinateSpace n => x i) 2 (coordinateGaussian n) := by
  apply (memLp_map_measure_iff (continuous_apply i).aestronglyMeasurable
    (euclideanCoordinates n).continuous.measurable.aemeasurable).mpr
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  exact Paouris.standardGaussian_coordinate_sq_integrable i

lemma coordinateDerivative_affine_scalar {n : ℕ} {g : CoordinateSpace n → ℝ}
    (hg : Differentiable ℝ g) (a : CoordinateSpace n) (r : ℝ) (i : Fin n) (x : CoordinateSpace n) :
    coordinateDerivative i (fun y => g (a + r • y)) x =
      r * coordinateDerivative i g (a + r • x) := by
  have hA : HasFDerivAt (fun y : CoordinateSpace n => a + r • y)
      (r • ContinuousLinearMap.id ℝ (CoordinateSpace n)) x := by
    simpa only [zero_add, Pi.smul_apply, id_eq] using (hasFDerivAt_const (𝕜 := ℝ) a x).add ((hasFDerivAt_id (𝕜 := ℝ) x).const_smul r)
  unfold coordinateDerivative
  have hc := ((hg _).hasFDerivAt.comp x hA).fderiv
  simp only [Function.comp_def] at hc
  rw [hc]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]

/-- Adding a fixed vector and scaling genuine Gaussian noise produces the
exact scalar covariance factor r² in its Stein identity, including r=0. -/
theorem coordinateGaussian_affine_stein {n : ℕ} {g : CoordinateSpace n → ℝ}
    (hg : ContDiff ℝ 1 g) (C D : ℝ)
    (hgB : ∀ x, |g x| ≤ C) (hD : ∀ x j, |coordinateDerivative j g x| ≤ D)
    (a : CoordinateSpace n) (r : ℝ) (i : Fin n) :
    (∫ z, (r * z i) * g (a + r • z) ∂coordinateGaussian n) =
      ∫ z, r^2 * coordinateDerivative i g (a + r • z) ∂coordinateGaussian n := by
  have hq : ContDiff ℝ 1 (fun z => g (a + r • z)) := hg.comp (contDiff_const.add (contDiff_const.smul contDiff_id))
  have hqD (z : CoordinateSpace n) (j : Fin n) :
      |coordinateDerivative j (fun y => g (a + r • y)) z| ≤ |r| * D := by
    rw [coordinateDerivative_affine_scalar (hg.differentiable le_rfl), abs_mul]
    exact mul_le_mul_of_nonneg_left (hD _ j) (abs_nonneg r)
  have h := coordinateGaussian_stein_identity hq C (|r| * D) (fun z => hgB _) hqD i
  have heq : (fun z : CoordinateSpace n => (r * z i) * g (a + r • z)) =
      (fun z => r * (z i * g (a + r • z))) := by funext z; ring
  rw [heq, integral_const_mul, h]
  simp only [coordinateDerivative_affine_scalar (hg.differentiable le_rfl), integral_const_mul]
  ring

lemma smooth_compact_uniform_bounds {n : ℕ} {g : CoordinateSpace n → ℝ}
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    ∃ C D : ℝ, (∀ x, |g x| ≤ C) ∧ (∀ x i, |coordinateDerivative i g x| ≤ D) := by
  obtain ⟨C, hC⟩ := hg.continuous.bounded_above_of_compact_support hgc
  have hbound (i : Fin n) : ∃ D : ℝ, ∀ x, |coordinateDerivative i g x| ≤ D := by
    obtain ⟨D, hD⟩ := (smooth_coordinateDerivative hg i).continuous.bounded_above_of_compact_support
      (hgc.fderiv_apply ℝ (Pi.single i 1))
    exact ⟨D, fun x => by simpa only [Real.norm_eq_abs] using hD x⟩
  choose D hD using hbound
  refine ⟨C, ∑ i, |D i|, (fun x => by simpa only [Real.norm_eq_abs] using hC x), ?_⟩
  intro x i
  exact (hD i x).trans ((le_abs_self _).trans
    (Finset.single_le_sum (fun j _ => abs_nonneg (D j)) (Finset.mem_univ i)))

end GaussianTilt.Letwin
