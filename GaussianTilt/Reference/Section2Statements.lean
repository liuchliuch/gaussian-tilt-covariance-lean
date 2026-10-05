import GaussianTilt.Reference.NumberedDefinitions

/-! # Independent specification of all six active Section 2 results

Source: pinned `paper/source/main.tex`, lines 1176--1552. This module imports
only Mathlib through independent Reference definitions. It contains proposition
definitions, no implementation theorems and no asserted analytic results.

The paper interprets matrix covariance and differentiation entrywise; this is
used explicitly in Lemma 2.1. Extended potentials exclude negative infinity,
allow positive infinity, and their normalizing mass is an ENNReal integral so
that finiteness is not erased by the totalized real integral.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators ENNReal Matrix.Norms.L2Operator MatrixOrder
namespace GaussianTilt.Reference

/-- Literal proper extended-real convex potentials, with the paper's
codomain ℝ∪{+∞} represented as EReal plus exclusion of −∞. -/
def properPotential {n : ℕ} (W : Space n→EReal) : Prop :=
  (∀x,W x≠⊥) ∧ ∃x,W x≠⊤

def convexExtendedPotential {n : ℕ} (W : Space n→EReal) : Prop :=
  ∀x y:Space n,∀a b:ℝ,0≤a → 0≤b → a+b=1 →
    W (a • x+b • y)≤(a:EReal)*W x+(b:EReal)*W y

def potentialDensity {n : ℕ} (W : Space n→EReal) (x:Space n) : ℝ :=
  (EReal.exp (-W x)).toReal

def potentialMass {n : ℕ} (W : Space n→EReal) : ENNReal :=
  ∫⁻x,EReal.exp (-W x)

def potentialLaw {n : ℕ} (W : Space n→EReal) : Measure (Space n) :=
  volume.withDensity (fun x=>ENNReal.ofReal (potentialDensity W x/(∫y,potentialDensity W y)))

/-- Lemma 2.1, Gaussian-tilt identities, including the full real-time Rényi
formula. The derivative clauses use actual derivatives, not formal symbols. -/
def Lemma2_1 : Prop :=
  ∀n:ℕ,∀μ:Measure (Space n),IsProbabilityMeasure μ → compactlySupported μ →
    (∀f:Space n→ℝ,Integrable f μ → ∀t:ℝ,0≤t →
      HasDerivAt (fun s=>∫x,f x∂gaussianTilt μ s)
        (-observableCovariance (gaussianTilt μ t) f (fun x=>‖x‖^2)) t) ∧
    (∀t:ℝ,0≤t →
      HasDerivAt (logPartition μ) (-(∫x,‖x‖^2∂gaussianTilt μ t)) t ∧
      HasDerivAt (deriv (logPartition μ))
        (observableVariance (gaussianTilt μ t) (fun x=>‖x‖^2)) t) ∧
    (∀t:ℝ,0≤t →
      HasDerivAt (fun s=>mean (gaussianTilt μ s))
        (WithLp.toLp 2 (fun i=>-observableCovariance (gaussianTilt μ t)
          (fun x=>x i) (fun x=>‖x‖^2))) t) ∧
    (∀t:ℝ,0≤t → ∀i j:Fin n,
      HasDerivAt (fun s=>secondMoment (gaussianTilt μ s) i j)
        (-observableCovariance (gaussianTilt μ t) (fun x=>x i*x j) (fun x=>‖x‖^2)) t) ∧
    (∀r:ℝ,1<r → ∀s t:ℝ,
      renyi r (gaussianTilt μ s) (gaussianTilt μ t)=
        (logPartition μ (t+r*(s-t))-r*logPartition μ s+(r-1)*logPartition μ t)/(r-1))

/-- Theorem 2.2, including the genuine Euclidean-gradient energy and its
printed exact value. There is no compact-support hypothesis. -/
def Theorem2_2 : Prop :=
  ∀n:ℕ,∀μ:Measure (Space n),IsProbabilityMeasure μ → isotropic μ → logconcave μ →
    ∀A:Matrix (Fin n) (Fin n) ℝ,A.IsHermitian →
      observableVariance μ (quadraticForm A)≤2*(∫x,‖gradient (quadraticForm A) x‖^2∂μ) ∧
      2*(∫x,‖gradient (quadraticForm A) x‖^2∂μ)=8*Matrix.trace (A*A)

/-- Theorem 2.3, the literal norm tail, with one universal constant before
all dimensions, laws and scales. -/
def Theorem2_3 : Prop :=
  ∃C₀:ℝ,0<C₀ ∧ ∀n:ℕ,∀μ:Measure (Space n),IsProbabilityMeasure μ →
    isotropic μ → logconcave μ → ∀t:ℝ,1≤t →
      μ.real {x|C₀*t*Real.sqrt (n:ℝ)≤‖x‖}≤Real.exp (-t*Real.sqrt (n:ℝ))

/-- Theorem 2.4, every genuine orthogonal projection and every real p≥2,
using its actual rank rather than an auxiliary dimension parameter. -/
def Theorem2_4 : Prop :=
  ∃C:ℝ,0<C ∧ ∀n:ℕ,∀μ:Measure (Space n),IsProbabilityMeasure μ →
    isotropic μ → logconcave μ → ∀P:Matrix (Fin n) (Fin n) ℝ,
      orthogonalProjectionMatrix P → ∀p:ℝ,2≤p →
      (∫x,‖Matrix.toEuclideanCLM (𝕜:=ℝ) (n:=Fin n) P x‖^p∂μ)^(1/p)≤
        C*(Real.sqrt (P.rank:ℝ)+p)

/-- Theorem 2.5, proper lower-semicontinuous extended-valued strong
convexity, with the printed directional and matrix formulations. -/
def Theorem2_5 : Prop :=
  ∀n:ℕ,∀W:Space n→EReal,properPotential W → LowerSemicontinuous W →
    ∀κ:ℝ,0<κ →
      convexExtendedPotential (fun x=>W x-(κ/2*‖x‖^2:ℝ)) →
      0<potentialMass W → potentialMass W<⊤ →
      IsProbabilityMeasure (potentialLaw W) ∧
      (∀u:Space n,observableVariance (potentialLaw W) (fun x=>inner ℝ u x)≤κ⁻¹*‖u‖^2) ∧
      ((κ⁻¹:ℝ) • (1:Matrix (Fin n) (Fin n) ℝ)-covariance (potentialLaw W)).PosSemidef

/-- Lemma 2.6, the nondegenerate noncentered estimate including the printed
positive-semidefinite-square-root trace equality. -/
def Lemma2_6 : Prop :=
  ∀n:ℕ,∀μ:Measure (Space n),IsProbabilityMeasure μ → logconcave μ →
    (covariance μ).PosDef → ∀B:Matrix (Fin n) (Fin n) ℝ,B.IsHermitian →
    let M:=secondMoment μ
    observableVariance μ (quadraticForm B)≤
      10*Matrix.trace ((CFC.sqrt M*B*CFC.sqrt M)*(CFC.sqrt M*B*CFC.sqrt M)) ∧
    10*Matrix.trace ((CFC.sqrt M*B*CFC.sqrt M)*(CFC.sqrt M*B*CFC.sqrt M))=
      10*Matrix.trace ((B*M)*(B*M))

end GaussianTilt.Reference
