import GaussianTilt.MomentMapRegularityImprovementDensityNormalization
import GaussianTilt.MomentMapRegularityImprovementUniformSections

/-! # The actual centered unit-density-normalized source section -/
noncomputable section
open Set MeasureTheory
open scoped NNReal ENNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

def normalizedSectionPotential (φ f : E n → ℝ) (T : E n ≃L[ℝ] E n)
    (x p : E n) (h : ℝ) : E n → ℝ := fun y=>
  densityNormalizationFactor n (|(T.symm : E n →L[ℝ] E n).det|^2*f x)*
    affinePotential φ T x p (φ x-inner ℝ p x+h) y

def normalizedSectionDensity (f : E n → ℝ) (T : E n ≃L[ℝ] E n) (x : E n) : E n → ℝ :=
  fun y=>f (affineSource T x y)/f x

lemma normalizedSectionDensity_center (f : E n → ℝ) (T : E n ≃L[ℝ] E n)
    {x : E n} (hfx : f x≠0) : normalizedSectionDensity f T x 0=1 := by
  simp [normalizedSectionDensity,affineSource,hfx]

/-- The true source section is transformed into a finite global convex
potential with zero boundary and literal central-density-one Alexandrov
law. Neither a weak equation nor a normalized density is assumed. -/
theorem normalized_section_potential_data [NeZero n] {φ f : E n → ℝ}
    (hφ : Continuous φ) (hc : ConvexOn ℝ univ φ) (hf : Continuous f)
    (hMA : ∀ A, IsCompact A → volume (subgradientImage φ A)=
      (volume.withDensity (fun y=>ENNReal.ofReal (f y))) A)
    (T : E n ≃L[ℝ] E n) (x p : E n) (h : ℝ) (hfx : 0 < f x) :
    Continuous (normalizedSectionPotential φ f T x p h) ∧
    ConvexOn ℝ univ (normalizedSectionPotential φ f T x p h) ∧
    Continuous (normalizedSectionDensity f T x) ∧
    (∀ y∈frontier ((fun z=>T (z-x)) '' supportSection φ p x h),
      normalizedSectionPotential φ f T x p h y=0) ∧
    ∀ A, IsCompact A → volume (subgradientImage (normalizedSectionPotential φ f T x p h) A)=
      (volume.withDensity (fun y=>ENNReal.ofReal (normalizedSectionDensity f T x y))) A := by
  let b := φ x-inner ℝ p x+h
  let v := affinePotential φ T x p b
  let d := |(T.symm : E n →L[ℝ] E n).det|^2*f x
  have hd : 0 < d := mul_pos (sq_pos_of_pos (abs_pos.mpr T.symm.toLinearEquiv.isUnit_det'.ne_zero)) hfx
  have ht := densityNormalizationFactor_pos (n:=n) hd
  have hvconv : ConvexOn ℝ univ v := convexOn_affinePotential hc T x p b
  have hvc : Continuous v := continuousOn_univ.mp (hvconv.continuousOn isOpen_univ)
  have hucont : Continuous (normalizedSectionPotential φ f T x p h) := continuous_const.mul hvc
  have huconv : ConvexOn ℝ univ (normalizedSectionPotential φ f T x p h) := hvconv.smul ht.le
  refine ⟨hucont,huconv,by unfold normalizedSectionDensity affineSource; fun_prop,?_,?_⟩
  · have hvalue (y : E n) : v y=supportResidual φ p x (affineSource T x y)-h := by
      dsimp [v,affinePotential,b,supportResidual]
      rw [inner_sub_right]
      ring
    have hN : (fun z=>T (z-x)) '' supportSection φ p x h={y | v y≤0} := by
      rw [forward_image_eq_affineSource_preimage T x]
      ext y
      rw [mem_preimage,mem_setOf_eq,hvalue]
      change supportResidual φ p x (affineSource T x y)≤h ↔
        supportResidual φ p x (affineSource T x y)-h≤0
      constructor <;> intro hh <;> linarith
    intro y hy
    rw [hN] at hy
    have hz : v y=0 := frontier_le_subset_eq hvc continuous_const hy
    change densityNormalizationFactor n d*v y=0
    rw [hz,mul_zero]
  · intro A hA
    rw [withDensity_apply _ hA.measurableSet]
    apply alexandrov_density_center_normalized T x p b hfx hA
    have himage : IsCompact (affineSource T x '' A) := hA.image (T.symm.continuous.add continuous_const)
    rw [hMA _ himage,withDensity_apply _ himage.measurableSet]

end GaussianTilt.MomentMapRegularity
