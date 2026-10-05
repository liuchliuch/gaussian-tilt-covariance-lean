import GaussianTilt.Energy

/-!
# Nondegeneracy is preserved by genuine Gaussian tilts

Mutual absolute continuity transports the absence of affine support. Isotropy
therefore supplies positive-definite covariance and second moments at every
real tilt parameter, without an extra nondegeneracy hypothesis.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal BigOperators Matrix.Norms.L2Operator

namespace GaussianTilt

lemma variance_pos_of_absolutelyContinuous {Ω : Type*} [MeasurableSpace Ω]
    {μ ν : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : Ω → ℝ} (hac : μ ≪ ν) (hf : MemLp f 2 ν)
    (hpos : 0 < ProbabilityTheory.variance f μ) :
    0 < ProbabilityTheory.variance f ν := by
  apply lt_of_le_of_ne (variance_nonneg f ν)
  intro hz
  have hev : evariance f ν = 0 := by
    rw [← hf.ofReal_variance_eq, ← hz]
    simp
  have hae := (evariance_eq_zero_iff hf.aemeasurable).mp hev
  have hconst := variance_congr (hac.ae_le hae)
  have hzero : ProbabilityTheory.variance f μ = 0 := by
    rw [hconst]
    simp [ProbabilityTheory.variance_eq_integral]
  exact (ne_of_gt hpos) hzero

namespace CompactProbability
variable {n : ℕ} (P : CompactProbability n)

lemma covariance_posDef (hiso : Reference.isotropic P.measure) (t : ℝ) :
    (Reference.covariance (P.tilt t)).PosDef := by
  have hX (s : ℝ) (i : Fin n) : MemLp (fun x : Point n ↦ x i) 2 (P.tilt s) :=
    P.memLp_continuous_tilt (by fun_prop) s 2
  refine ⟨(P.covariance_posSemidef t).1, ?_⟩
  intro v hv
  have hV := variance_pos_of_absolutelyContinuous (P.absolutelyContinuous_tilt t)
    (P.memLp_continuous_tilt (f := fun x : Point n ↦ v ⬝ᵥ (fun i ↦ x i))
      (by unfold dotProduct; fun_prop) t 2)
  have hbase : 0 < ProbabilityTheory.variance (fun x : Point n ↦ v ⬝ᵥ (fun i ↦ x i)) P.measure := by
    have heq := variance_linear_eq_covariance (hX 0) v
    rw [P.tilt_zero] at heq
    have hc0 := P.reference_covariance_eq_covarianceMatrix 0
    rw [P.tilt_zero] at hc0
    rw [heq, ← hc0, hiso.2]
    simpa only [matrixQuadratic, star_trivial] using
      (Matrix.PosDef.one (n := Fin n) (R := ℝ)).2 v hv
  have hresult := hV hbase
  rw [variance_linear_eq_covariance (hX t), ← P.reference_covariance_eq_covarianceMatrix t] at hresult
  simpa only [matrixQuadratic, star_trivial] using hresult

lemma secondMoment_posDef (hiso : Reference.isotropic P.measure) (t : ℝ) :
    (secondMomentMatrix (P.tilt t) (fun x : Point n ↦ fun i ↦ x i)).PosDef := by
  rw [secondMomentMatrix_eq_covariance_add_rankOne
    (fun i ↦ P.memLp_continuous_tilt (by fun_prop) t 2)]
  apply Matrix.PosDef.add_posSemidef
  · rw [← P.reference_covariance_eq_covarianceMatrix t]
    exact P.covariance_posDef hiso t
  · simpa only [star_trivial] using
      posSemidef_vecMulVec_self_star (meanVector (P.tilt t) (fun x : Point n ↦ fun i ↦ x i))

lemma covariance_opNorm_pos (hiso : Reference.isotropic P.measure) (hn : 0 < n) (t : ℝ) :
    0 < ‖Reference.covariance (P.tilt t)‖ := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact norm_pos_iff.mpr (P.covariance_posDef hiso t).isUnit.ne_zero

lemma secondMoment_opNorm_pos (hiso : Reference.isotropic P.measure) (hn : 0 < n) (t : ℝ) :
    0 < ‖secondMomentMatrix (P.tilt t) (fun x : Point n ↦ fun i ↦ x i)‖ := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact norm_pos_iff.mpr (P.secondMoment_posDef hiso t).isUnit.ne_zero

end CompactProbability
end GaussianTilt
