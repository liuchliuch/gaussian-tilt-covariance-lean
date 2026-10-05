import GaussianTilt.MomentMapRegularityLocalization
import GaussianTilt.ConvexIntegrability

/-! # Affine covariance of literal subgradient images -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators Gradient ENNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

def affineSource (T : E n ≃L[ℝ] E n) (a y : E n) : E n := T.symm y + a

def affinePotential (φ : E n → ℝ) (T : E n ≃L[ℝ] E n) (a p : E n) (b : ℝ)
    (y : E n) : ℝ := φ (affineSource T a y) - inner ℝ p (affineSource T a y) - b

def affineSlope (T : E n ≃L[ℝ] E n) (p r : E n) : E n :=
  (T.symm.toLinearEquiv.toLinearMap.adjoint) (r - p)

lemma affineSlope_surjective (T : E n ≃L[ℝ] E n) (p : E n) :
    Function.Surjective (affineSlope T p) := by
  intro q
  refine ⟨T.toLinearEquiv.toLinearMap.adjoint q + p, ?_⟩
  apply ext_inner_right ℝ
  intro v
  simp only [affineSlope, add_sub_cancel_right, LinearMap.adjoint_inner_left]
  simp

lemma supportsAt_affine_iff (φ : E n → ℝ) (T : E n ≃L[ℝ] E n)
    (a p : E n) (b : ℝ) (r y : E n) :
    SupportsAt (affinePotential φ T a p b) (affineSlope T p r) y ↔
      SupportsAt φ r (affineSource T a y) := by
  have hid (z : E n) : inner ℝ (affineSlope T p r) (z - y) =
      inner ℝ (r - p) (affineSource T a z - affineSource T a y) := by
    rw [affineSlope, LinearMap.adjoint_inner_left]
    change inner ℝ (r - p) (T.symm (z - y)) = _
    congr 1
    simp [affineSource, map_sub]
  constructor
  · intro hs z
    let w := T (z - a)
    have hw : affineSource T a w = z := by simp [w, affineSource]
    have h := hs w
    change affinePotential φ T a p b y + inner ℝ (affineSlope T p r) (w - y) ≤
      affinePotential φ T a p b w at h
    rw [hid w] at h
    unfold affinePotential at h
    rw [hw] at h
    change φ (affineSource T a y) + inner ℝ r (z - affineSource T a y) ≤ φ z
    simp only [inner_sub_left, inner_sub_right] at h ⊢
    linarith
  · intro hs z
    have h := hs (affineSource T a z)
    change affinePotential φ T a p b y + inner ℝ (affineSlope T p r) (z - y) ≤
      affinePotential φ T a p b z
    rw [hid z]
    unfold affinePotential
    simp only [inner_sub_left, inner_sub_right] at h ⊢
    linarith

/-- Exact covariance of the literal global subgradient image under an
invertible affine change of source coordinates and subtraction of a plane. -/
theorem subgradientImage_affine (φ : E n → ℝ) (T : E n ≃L[ℝ] E n)
    (a p : E n) (b : ℝ) (A : Set (E n)) :
    subgradientImage (affinePotential φ T a p b) A =
      affineSlope T p '' subgradientImage φ (affineSource T a '' A) := by
  ext q
  constructor
  · rintro ⟨y, hy, hs⟩
    obtain ⟨r, rfl⟩ := affineSlope_surjective T p q
    exact ⟨r, ⟨affineSource T a y, ⟨y, hy, rfl⟩,
      (supportsAt_affine_iff φ T a p b r y).mp hs⟩, rfl⟩
  · rintro ⟨r, ⟨x, ⟨y, hy, rfl⟩, hs⟩, rfl⟩
    exact ⟨y, hy, (supportsAt_affine_iff φ T a p b r y).mpr hs⟩

lemma determinant_adjoint (T : E n →ₗ[ℝ] E n) : LinearMap.det T.adjoint = LinearMap.det T := by
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  rw [← LinearMap.det_toMatrix e.toBasis, LinearMap.toMatrix_adjoint e e,
    Matrix.det_conjTranspose, star_trivial, LinearMap.det_toMatrix]

lemma volume_affineSource_image (T : E n ≃L[ℝ] E n) (a : E n) (A : Set (E n)) :
    volume (affineSource T a '' A) =
      ENNReal.ofReal |LinearMap.det T.symm.toLinearEquiv.toLinearMap| * volume A := by
  have he : affineSource T a '' A = (fun z => z + a) '' (T.symm.toLinearEquiv.toLinearMap '' A) := by
    rw [Set.image_image]
    rfl
  rw [he, ConvexIntegrability.volume_image_add_right, Measure.addHaar_image_linearMap]

lemma volume_affineSlope_image (T : E n ≃L[ℝ] E n) (p : E n) (A : Set (E n)) :
    volume (affineSlope T p '' A) =
      ENNReal.ofReal |LinearMap.det T.symm.toLinearEquiv.toLinearMap| * volume A := by
  have he : affineSlope T p '' A = T.symm.toLinearEquiv.toLinearMap.adjoint ''
      ((fun z => z + -p) '' A) := by rw [Set.image_image]; rfl
  rw [he, Measure.addHaar_image_linearMap, determinant_adjoint,
    ConvexIntegrability.volume_image_add_right]

/-- The exact scaling identity for Alexandrov image volume. Both source and
slope volume contribute the same determinant factor in density comparisons. -/
theorem volume_subgradientImage_affine (φ : E n → ℝ) (T : E n ≃L[ℝ] E n)
    (a p : E n) (b : ℝ) (A : Set (E n)) :
    volume (subgradientImage (affinePotential φ T a p b) A) =
      ENNReal.ofReal |LinearMap.det T.symm.toLinearEquiv.toLinearMap| *
        volume (subgradientImage φ (affineSource T a '' A)) := by
  rw [subgradientImage_affine, volume_affineSlope_image]

def affineJacobian (T : E n ≃L[ℝ] E n) : ℝ≥0∞ :=
  ENNReal.ofReal |LinearMap.det T.symm.toLinearEquiv.toLinearMap|

lemma affineJacobian_pos (T : E n ≃L[ℝ] E n) : 0 < affineJacobian T :=
  ENNReal.ofReal_pos.mpr (abs_pos.mpr T.symm.toLinearEquiv.isUnit_det'.ne_zero)

lemma affineJacobian_ne_top (T : E n ≃L[ℝ] E n) : affineJacobian T ≠ ⊤ := ENNReal.ofReal_ne_top

/-- Affine source normalization multiplies both Alexandrov density bounds
by exactly d², where d=|det(T⁻¹)|. In particular, it preserves their ratio. -/
theorem subgradientImage_affine_density_bounds (φ : E n → ℝ) (T : E n ≃L[ℝ] E n)
    (a p : E n) (b : ℝ) (A : Set (E n)) {c C : ℝ≥0∞}
    (hl : c * volume (affineSource T a '' A) ≤
      volume (subgradientImage φ (affineSource T a '' A)))
    (hu : volume (subgradientImage φ (affineSource T a '' A)) ≤
      C * volume (affineSource T a '' A)) :
    (affineJacobian T)^2 * c * volume A ≤ volume (subgradientImage (affinePotential φ T a p b) A) ∧
      volume (subgradientImage (affinePotential φ T a p b) A) ≤
        (affineJacobian T)^2 * C * volume A := by
  rw [volume_affineSource_image] at hl hu
  rw [volume_subgradientImage_affine]
  have hl' := mul_le_mul_left' hl (affineJacobian T)
  have hu' := mul_le_mul_left' hu (affineJacobian T)
  change affineJacobian T * (c * (affineJacobian T * volume A)) ≤ _ at hl'
  change _ ≤ affineJacobian T * (C * (affineJacobian T * volume A)) at hu'
  constructor
  · convert hl' using 1 <;> unfold affineJacobian <;> ring
  · convert hu' using 1 <;> unfold affineJacobian <;> ring

end GaussianTilt.MomentMapRegularity
