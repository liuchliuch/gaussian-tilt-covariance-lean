import GaussianTilt.Reference.Section2Statements
import GaussianTilt.PaperResults
import GaussianTilt.ActualUpperFlowGradient
import GaussianTilt.PaourisProjectedGeneral
import GaussianTilt.ExtendedPotential

/-! # Machine-checked bridges to the independent Section 2 specification

The target propositions live in a Mathlib-only dependency lane. Exact object
identities are recorded here before the theorem bridges. The Letwin-dependent
results 2.2 and 2.6 remain explicitly conditional on the one original analytic
input; this file does not assert that unresolved input.
-/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped Topology BigOperators ENNReal Matrix.Norms.L2Operator MatrixOrder
namespace GaussianTilt.Reference
variable {n : ℕ}

lemma quadraticForm_eq_matrixQuadratic (A : Matrix (Fin n) (Fin n) ℝ) :
    quadraticForm A=(fun x:Space n=>GaussianTilt.matrixQuadratic A (fun i=>x i)) := rfl

lemma secondMoment_eq_implementation (μ:Measure (Space n)) :
    secondMoment μ=GaussianTilt.secondMomentMatrix μ (fun x:Space n=>fun i=>x i) := rfl

lemma properPotential_iff_implementation (W:Space n→EReal) :
    properPotential W↔GaussianTilt.ExtendedPotential.Proper W := Iff.rfl

lemma convexExtendedPotential_iff_implementation (W:Space n→EReal) :
    convexExtendedPotential W↔GaussianTilt.ExtendedPotential.ConvexExtended W := Iff.rfl

lemma potentialDensity_eq_implementation (W:Space n→EReal) :
    potentialDensity W=GaussianTilt.ExtendedPotential.density W := rfl

lemma potentialLaw_eq_implementation (W:Space n→EReal) :
    potentialLaw W=GaussianTilt.ExtendedPotential.normalizedLaw W volume := rfl

lemma observableVariance_eq_probabilityVariance {μ:Measure (Space n)} [IsProbabilityMeasure μ]
    {f:Space n→ℝ} (hf:MemLp f 2 μ) :
    observableVariance μ f=ProbabilityTheory.variance f μ := by
  rw [ProbabilityTheory.variance_eq_sub hf]
  simp only [observableVariance,observableCovariance,pow_two,Pi.mul_apply]

/-- Every clause of independent Lemma 2.1, including actual second
differentiability and the entrywise moment flow, is proved. -/
theorem lemma2_1_proved : Lemma2_1 := by
  intro n μ hμ hc
  letI : IsProbabilityMeasure μ := hμ
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro f hf t ht
    exact expectation_hasDerivAt μ hc hf t
  · intro t ht
    refine ⟨logPartition_hasDerivAt μ hc t,?_⟩
    obtain ⟨P,rfl⟩:=exists_compactProbability_of_compactlySupported μ hc
    simpa only [logPartition,P.reference_partition,P.reference_gaussianTilt,P.integral_tilt,
      observableVariance,observableCovariance,CompactProbability.variance,CompactProbability.covariance,energy]
      using P.hasDerivAt_deriv_logPartition t
  · intro t ht
    exact mean_hasDerivAt μ hc t
  · intro t ht i j
    exact secondMoment_hasDerivAt μ hc t i j
  · intro r hr s t
    exact renyi_identity μ hc hr s t

/-- The exact independent Theorem 2.2 follows from the still explicit
compact isotropic Letwin input. No extra integrability assumption is added. -/
theorem theorem2_2_of_isotropic_bound (hL:IsotropicQuadraticVarianceBound) : Theorem2_2 := by
  intro n μ hμ hi hl A hA
  letI : IsProbabilityMeasure μ := hμ
  have h4:=Whitening.isotropic_logconcave_norm_fourth_integrable μ hl hi
  have hq:MemLp (quadraticForm A) 2 μ := Whitening.quadratic_memLp_of_fourth h4 A
  rw [observableVariance_eq_probabilityVariance hq]
  simpa only [quadraticForm_eq_matrixQuadratic,pow_two] using original2_2_of_compact_bound hL μ hl hi A hA

/-- The independent full-scope Letwin target is equivalent to the compact
analytic input used in the implementation. The forward implication merely
restricts the law; the reverse one uses the proved noncompact approximation. -/
theorem theorem2_2_iff_isotropic_bound : Theorem2_2↔IsotropicQuadraticVarianceBound := by
  constructor
  · intro h n μ hμ hc hi hl A hA
    letI : IsProbabilityMeasure μ := hμ
    have hh:=h n μ hμ hi hl A hA
    have hq:MemLp (quadraticForm A) 2 μ := Whitening.quadratic_memLp_of_fourth
      (Whitening.isotropic_logconcave_norm_fourth_integrable μ hl hi) A
    have hb:=hh.1.trans_eq hh.2
    rw [observableVariance_eq_probabilityVariance hq,quadraticForm_eq_matrixQuadratic] at hb
    simpa only [pow_two] using hb
  · exact theorem2_2_of_isotropic_bound

/-- The independent literal Paouris tail target is closed at noncompact scope. -/
theorem theorem2_3_proved : Theorem2_3 := by
  refine ⟨Paouris.generalPaourisTailConstant,Paouris.generalPaourisTailConstant_pos,?_⟩
  intro n μ hμ hi hl t ht
  letI : IsProbabilityMeasure μ := hμ
  exact Paouris.isotropic_norm_tail μ hl hi ht

/-- The independent projected Paouris target uses the actual matrix rank. -/
theorem theorem2_4_proved : Theorem2_4 := by
  refine ⟨Paouris.generalPaourisMomentConstant,Paouris.generalPaourisMomentConstant_pos,?_⟩
  intro n μ hμ hi hl P hP p hp
  letI : IsProbabilityMeasure μ := hμ
  exact (Paouris.projected_moment_le μ hl hi P hP.1 hP.2 hp).2

/-- The directional covariance inequality gives its printed Loewner-matrix
form through actual finite second moments. -/
lemma covariance_upper_matrix_of_directional {μ:Measure (Space n)} [IsProbabilityMeasure μ]
    {κ:ℝ} (hκ:0<κ)
    (hdir:∀u:Space n,MemLp (fun x=>inner ℝ u x) 2 μ ∧
      ProbabilityTheory.variance (fun x=>inner ℝ u x) μ≤κ⁻¹*‖u‖^2) :
    ((κ⁻¹:ℝ) • (1:Matrix (Fin n) (Fin n) ℝ)-covariance μ).PosSemidef := by
  have hX : ∀i:Fin n,MemLp (fun x:Space n=>x i) 2 μ := by
    intro i
    simpa only [EuclideanSpace.basisFun_inner] using (hdir (EuclideanSpace.basisFun (Fin n) ℝ i)).1
  refine ⟨(Matrix.PosSemidef.one.smul (inv_nonneg.mpr hκ.le)).1.sub (covariance_posSemidef hX).1,?_⟩
  intro v
  have hv:= (hdir (WithLp.toLp 2 v)).2
  have hfun : (fun x:Space n=>inner ℝ (WithLp.toLp 2 v) x)=(fun x:Space n=>v⬝ᵥ(fun i=>x i)) := by
    funext x
    simp only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial,WithLp.ofLp_toLp]
    exact dotProduct_comm _ _
  rw [hfun,GaussianTilt.variance_linear_eq_covariance hX] at hv
  change matrixQuadratic (covarianceMatrix μ (fun x:Space n=>WithLp.ofLp x)) v≤κ⁻¹*‖(WithLp.toLp 2 v:Space n)‖^2 at hv
  rw [←covariance_eq_covarianceMatrix hX] at hv
  have hn : ‖(WithLp.toLp 2 v:Space n)‖^2=v⬝ᵥv := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [PiLp.toLp_apply,Real.norm_eq_abs,sq_abs]
    simp only [pow_two,dotProduct]
  rw [hn] at hv
  simpa only [star_trivial,Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,
    dotProduct_sub,dotProduct_smul,GaussianTilt.matrixQuadratic] using sub_nonneg.mpr hv

/-- Both independent forms of the full nonsmooth extended-potential
Brascamp--Lieb theorem are closed. -/
theorem theorem2_5_proved : Theorem2_5 := by
  intro n W hp hW κ hκ hc hZp hZf
  obtain ⟨hprob,hdir⟩:=ExtendedPotential.brascamp_lieb_extended_variance hp hW hκ hc hZp hZf
  letI : IsProbabilityMeasure (potentialLaw W) := hprob
  refine ⟨hprob,?_,covariance_upper_matrix_of_directional hκ hdir⟩
  intro u
  change observableVariance (ExtendedPotential.normalizedLaw W volume) (fun x=>inner ℝ u x)≤κ⁻¹*‖u‖^2
  rw [observableVariance_eq_probabilityVariance (hdir u).1]
  exact (hdir u).2

/-- The independent noncentered target, including its positive-square-root
trace equality, follows from the same explicit isotropic input. -/
theorem lemma2_6_of_isotropic_bound (hL:IsotropicQuadraticVarianceBound) : Lemma2_6 := by
  intro n μ hμ hl hCov B hB
  letI : IsProbabilityMeasure μ := hμ
  dsimp only
  have hX:=posDef_coordinate_memLp hCov
  have hM : (secondMoment μ).PosSemidef := GaussianTilt.secondMomentMatrix_posSemidef hX
  have he : Matrix.trace ((CFC.sqrt (secondMoment μ)*B*CFC.sqrt (secondMoment μ))^2)=
      Matrix.trace ((B*secondMoment μ)^2) := Whitening.sandwich_trace_square B hM
  have h4:=logconcave_norm_fourth_integrable_of_posDef hl hCov
  have hq:MemLp (quadraticForm B) 2 μ := Whitening.quadratic_memLp_of_fourth h4 B
  have hb:=original2_6_of_isotropic_bound hL μ hl hCov B hB
  rw [←quadraticForm_eq_matrixQuadratic,←observableVariance_eq_probabilityVariance hq,
    ←secondMoment_eq_implementation] at hb
  constructor
  · simpa only [←pow_two,he] using hb
  · simp only [←pow_two,he]

/-- The independent noncentered statement follows from independent
Theorem 2.2, with no implementation predicate in the stated dependency. -/
theorem lemma2_6_of_theorem2_2 (h:Theorem2_2) : Lemma2_6 :=
  lemma2_6_of_isotropic_bound (theorem2_2_iff_isotropic_bound.mp h)

end GaussianTilt.Reference
