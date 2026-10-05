import GaussianTilt.Reference.Section4Definitions
import GaussianTilt.Section4FixedPrecision
import GaussianTilt.CramerUniform

/-! # Exact identification of independent lower-construction formulas

The pure Reference objects are kept separate. These implementation-side
identities prove that the raw centered variances, explicit body, product
slice laws, and normalized axial density are the same mathematical objects.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators Matrix.Norms.L2Operator
namespace GaussianTilt.Reference.Lower

lemma deviation_eq_implementation (d : ℕ) : deviation d=GaussianTilt.deviationScale d := rfl
lemma rate_eq_implementation (d : ℕ) : rate d=GaussianTilt.deviationScale d^2/(d:ℝ) := rfl
lemma rawBody_eq_implementation (d : ℕ) : rawBody d=GaussianTilt.rawBody d := rfl
lemma rawUniform_eq_implementation (d : ℕ) : rawUniform d=GaussianTilt.rawUniform d (GaussianTilt.deviationScale d) := rfl
lemma rawCoordinate_eq_implementation {d : ℕ} (i : Option (Fin d)) :
    rawCoordinate i=GaussianTilt.rawCoordinate i := rfl
lemma rawCovariance_eq_implementation (d : ℕ) :
    rawCovariance d=GaussianTilt.rawCovarianceMatrix d (GaussianTilt.deviationScale d) := rfl
lemma rawSignChange_eq_implementation {d : ℕ} (ε : Fin d→Bool) (η : Bool) :
    rawSignChange ε η=GaussianTilt.signChange ε η := rfl

/-- The means vanish by the proved raw symmetries; the independent centered
variance is therefore exactly the implementation's second-moment integral. -/
lemma transverseVariance_eq_implementation {d : ℕ} (i : Fin d) :
    transverseVariance i=GaussianTilt.rawTransverseVariance (GaussianTilt.deviationScale d) i := by
  simp only [transverseVariance,rawCovariance_eq_implementation,GaussianTilt.rawCovarianceMatrix,
    GaussianTilt.rawUniform_transverse_mean_zero,zero_mul,sub_zero,
    GaussianTilt.rawCoordinate,GaussianTilt.rawTransverseVariance,pow_two]

lemma axialVariance_eq_implementation (d : ℕ) :
    axialVariance d=GaussianTilt.rawAxialVariance d (GaussianTilt.deviationScale d) := by
  simp only [axialVariance,rawCovariance_eq_implementation,GaussianTilt.rawCovarianceMatrix,
    GaussianTilt.rawUniform_axial_mean_zero,zero_mul,sub_zero,
    GaussianTilt.rawCoordinate,GaussianTilt.rawAxialVariance,pow_two]

lemma cubeLaw_eq_implementation (d : ℕ) : cubeLaw d=GaussianTilt.LowerProbability.cubeLaw d := rfl
lemma sliceMass_eq_implementation (d : ℕ) (s : ℝ) :
    sliceMass d s=GaussianTilt.LowerProbability.cubeSlice d (GaussianTilt.deviationScale d) s := rfl
lemma sliceMoment_eq_implementation (d ℓ : ℕ) : sliceMoment d ℓ=
    ∫ s in Ici (0:ℝ),s^ℓ*GaussianTilt.LowerProbability.cubeSlice d (GaussianTilt.deviationScale d) s := rfl
lemma diagonalScale_eq_implementation {d : ℕ} (a b : ℝ) :
    (diagonalScale a b : RawSpace d→RawSpace d)=GaussianTilt.diagonalScale a b := rfl
lemma isotropization_eq_implementation {d : ℕ} (i : Fin d) : isotropization i=
    GaussianTilt.diagonalScale (Real.sqrt (GaussianTilt.rawTransverseVariance (GaussianTilt.deviationScale d) i))⁻¹
      (Real.sqrt (GaussianTilt.rawAxialVariance d (GaussianTilt.deviationScale d)))⁻¹ := by
  simp only [isotropization,transverseVariance_eq_implementation,axialVariance_eq_implementation,
    diagonalScale_eq_implementation]
lemma inverseIsotropization_eq_implementation {d : ℕ} (i : Fin d) : inverseIsotropization i=
    GaussianTilt.diagonalScale (Real.sqrt (GaussianTilt.rawTransverseVariance (GaussianTilt.deviationScale d) i))
      (Real.sqrt (GaussianTilt.rawAxialVariance d (GaussianTilt.deviationScale d))) := by
  simp only [inverseIsotropization,transverseVariance_eq_implementation,axialVariance_eq_implementation,
    diagonalScale_eq_implementation]
lemma toEuclidean_eq_implementation (d : ℕ) : toEuclidean d=GaussianTilt.rawToEuclidean d := rfl
lemma isotropicBody_eq_implementation {d : ℕ} (i : Fin d) :
    isotropicBody i=GaussianTilt.euclideanBody (GaussianTilt.deviationScale d) i := by
  simp only [isotropicBody,toEuclidean_eq_implementation,isotropization_eq_implementation,
    rawBody_eq_implementation,GaussianTilt.euclideanBody,GaussianTilt.isotropizedBody,GaussianTilt.rawBody]
lemma precision_eq_implementation (d : ℕ) (A : ℝ) : precision d A=A/(d:ℝ)^(2/5:ℝ) := rfl
lemma tiltedCube_eq_implementation (d : ℕ) (τ : ℝ) :
    tiltedCube d τ=GaussianTilt.LowerProbability.tiltedCubeLaw d τ := rfl
lemma acceptance_eq_implementation {d : ℕ} (i : Fin d) (A z : ℝ) : acceptance i A z=
    GaussianTilt.LowerProbability.tiltedSlice d
      ((A/(d:ℝ)^(2/5:ℝ))/GaussianTilt.rawTransverseVariance (GaussianTilt.deviationScale d) i)
      (GaussianTilt.deviationScale d) (GaussianTilt.rawAxialVariance d (GaussianTilt.deviationScale d)) z := by
  simp only [acceptance,tiltedCube_eq_implementation,precision_eq_implementation,
    transverseVariance_eq_implementation,axialVariance_eq_implementation,deviation_eq_implementation,
    GaussianTilt.LowerProbability.tiltedSlice]
lemma axialMarginal_eq_implementation {d : ℕ} (i : Fin d) (A : ℝ) : axialMarginal i A=
    GaussianTilt.LowerMarginal.axialLaw (A/(d:ℝ)^(2/5:ℝ))
      (GaussianTilt.LowerProbability.tiltedSlice d
        ((A/(d:ℝ)^(2/5:ℝ))/GaussianTilt.rawTransverseVariance (GaussianTilt.deviationScale d) i)
        (GaussianTilt.deviationScale d) (GaussianTilt.rawAxialVariance d (GaussianTilt.deviationScale d))) := by
  simp only [axialMarginal,axialKernel,precision_eq_implementation,acceptance_eq_implementation,
    GaussianTilt.LowerMarginal.axialLaw,GaussianTilt.LowerMarginal.kernel,GaussianTilt.LowerMarginal.mass]
lemma axialTiltVariance_eq_implementation {d : ℕ} (i : Fin d) (A : ℝ) : axialTiltVariance i A=
    ProbabilityTheory.variance (fun x : Space (d+1)=>x 0)
      (gaussianTilt (uniform (GaussianTilt.euclideanBody (GaussianTilt.deviationScale d) i))
        (A/(d:ℝ)^(2/5:ℝ))) := by
  simp only [axialTiltVariance,isotropicBody_eq_implementation,precision_eq_implementation]
lemma one_sub_standardNormalCDF_eq (z : ℝ) :
    1-standardNormalCDF z=GaussianTilt.GaussianLaplace.normalTail z := rfl

end GaussianTilt.Reference.Lower
