import GaussianTilt.Reference.NumberedDefinitions

/-! # Independent definitions of the paper's explicit lower construction

This file imports no implementation theorem or construction. The formulas
are transcribed from the pinned source, Section 4. The product coordinates
are (x,λ); the Euclidean realization lists λ first and then x. This fixed
coordinate permutation changes neither geometry nor the asserted covariance
norm. Both raw covariance scales below are literal variances, including
the mean correction; centering must be proved in any implementation bridge.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped Topology BigOperators ENNReal Matrix.Norms.L2Operator
namespace GaussianTilt.Reference.Lower

abbrev RawSpace (d : ℕ) := (Fin d→ℝ) × ℝ

def deviation (d : ℕ) : ℝ := (d:ℝ)^(3/5:ℝ)

def rate (d : ℕ) : ℝ := deviation d^2/(d:ℝ)

def rawBody (d : ℕ) : Set (RawSpace d) :=
  {p | (∀ i,|p.1 i|≤Real.sqrt 3) ∧
    (∑ i,(p.1 i)^2)+2*deviation d*|p.2|≤(d:ℝ)-2*deviation d}

def rawUniform (d : ℕ) : Measure (RawSpace d) := ProbabilityTheory.cond volume (rawBody d)

def rawCoordinate {d : ℕ} : Option (Fin d)→RawSpace d→ℝ
  | none=>fun p=>p.2
  | some i=>fun p=>p.1 i

def rawCovariance (d : ℕ) : Matrix (Option (Fin d)) (Option (Fin d)) ℝ :=
  fun i k=>(∫ p,rawCoordinate i p*rawCoordinate k p∂rawUniform d)-
    (∫ p,rawCoordinate i p∂rawUniform d)*(∫ p,rawCoordinate k p∂rawUniform d)

def rawSignChange {d : ℕ} (ε : Fin d→Bool) (η : Bool) (p : RawSpace d) : RawSpace d :=
  (fun i=>if ε i then -p.1 i else p.1 i,if η then -p.2 else p.2)

def rawUnconditional {d : ℕ} (K : Set (RawSpace d)) : Prop :=
  ∀ (ε : Fin d→Bool) (η : Bool) (p : RawSpace d),rawSignChange ε η p∈K ↔ p∈K

def transverseVariance {d : ℕ} (i : Fin d) : ℝ := rawCovariance d (some i) (some i)

def axialVariance (d : ℕ) : ℝ := rawCovariance d none none

def uniformCoordinate : Measure ℝ :=
  ProbabilityTheory.cond volume (Icc (-Real.sqrt 3) (Real.sqrt 3))

def cubeLaw (d : ℕ) : Measure (Fin d→ℝ) := Measure.pi (fun _=>uniformCoordinate)

/-- The exact centered cube-energy event defining G_d(s). -/
def sliceMass (d : ℕ) (s : ℝ) : ℝ :=
  (cubeLaw d).real {x | (∑ i,((x i)^2-1))≤ -2*deviation d*(1+s)}

def squareVariance : ℝ := 4/5

def sliceMoment (d ℓ : ℕ) : ℝ := ∫ s in Ici (0:ℝ),s^ℓ*sliceMass d s

def diagonalScale {d : ℕ} (a b : ℝ) (p : RawSpace d) : RawSpace d := (fun i=>a*p.1 i,b*p.2)

def isotropization {d : ℕ} (i : Fin d) : RawSpace d→RawSpace d :=
  diagonalScale (Real.sqrt (transverseVariance i))⁻¹ (Real.sqrt (axialVariance d))⁻¹

def inverseIsotropization {d : ℕ} (i : Fin d) : RawSpace d→RawSpace d :=
  diagonalScale (Real.sqrt (transverseVariance i)) (Real.sqrt (axialVariance d))

def toEuclidean (d : ℕ) (p : RawSpace d) : Space (d+1) := WithLp.toLp 2 (Fin.cons p.2 p.1)

def isotropicBody {d : ℕ} (i : Fin d) : Set (Space (d+1)) :=
  toEuclidean d '' (isotropization i '' rawBody d)

def precision (d : ℕ) (A : ℝ) : ℝ := A/(d:ℝ)^(2/5:ℝ)

def tiltedCoordinate (τ : ℝ) : Measure ℝ := uniformCoordinate.tilted (fun u=> -τ*u^2)

def tiltedCube (d : ℕ) (τ : ℝ) : Measure (Fin d→ℝ) := Measure.pi (fun _=>tiltedCoordinate τ)

/-- The literal independent tilted-cube acceptance probability p_d(z). -/
def acceptance {d : ℕ} (i : Fin d) (A z : ℝ) : ℝ :=
  (tiltedCube d (precision d A/transverseVariance i)).real
    {x | (∑ k,(x k)^2)≤(d:ℝ)-2*deviation d*(1+Real.sqrt (axialVariance d)*|z|)}

def axialKernel {d : ℕ} (i : Fin d) (A z : ℝ) : ℝ :=
  Real.exp (-precision d A*z^2)*acceptance i A z

def axialMarginal {d : ℕ} (i : Fin d) (A : ℝ) : Measure ℝ :=
  volume.withDensity (fun z=>ENNReal.ofReal (axialKernel i A z/(∫ w,axialKernel i A w)))

def axialTiltVariance {d : ℕ} (i : Fin d) (A : ℝ) : ℝ :=
  ProbabilityTheory.variance (fun x : Space (d+1)=>x 0)
    (gaussianTilt (uniform (isotropicBody i)) (precision d A))

def standardNormalCDF (z : ℝ) : ℝ := ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) z

end GaussianTilt.Reference.Lower
