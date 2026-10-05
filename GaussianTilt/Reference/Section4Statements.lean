import GaussianTilt.Reference.Section4Definitions

/-! # Independent numbered targets from pinned Section 4

These are propositions, not proofs. Only independent specifications are
imported. All asymptotic constants precede the dimension and are uniform
in the variables displayed by the source. The fixed precision multiple A
is quantified before its dimension threshold; that threshold and the
Corollary 4.10 constants may depend on this fixed numerical A.

The printed Corollary 4.10 uses the same c in a chain incompatible with
A>1. `Literal410` preserves that chain. `Corrected410` records the minimal
constant-renaming interpretation, separately and without identifying it
with the literal source. `Corollary4_10` is the literal target.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped Topology BigOperators ENNReal Matrix.Norms.L2Operator
universe u
namespace GaussianTilt.Reference
open Lower

/-- Theorem 4.1, source lines 2057–2070. -/
def Theorem4_1 : Prop := LowerBound

/-- Lemma 4.2, source lines 2096–2104: geometry, all coordinate sign
symmetries, centering and the actual positive two-block covariance. -/
def Lemma4_2 : Prop := ∃ d₀ : ℕ,∀ d≥d₀,
  IsCompact (Lower.rawBody d) ∧ Convex ℝ (Lower.rawBody d) ∧
  (interior (Lower.rawBody d)).Nonempty ∧ Lower.rawUnconditional (Lower.rawBody d) ∧
  IsProbabilityMeasure (Lower.rawUniform d) ∧
  (∀ i,∫ p,Lower.rawCoordinate i p∂Lower.rawUniform d=0) ∧
  ∃ a b : ℝ,0<a ∧ 0<b ∧ Lower.rawCovariance d=
    Matrix.diagonal (fun i=>match i with | none=>b | some _=>a)

/-- Theorem 4.3, source lines 2140–2154. IID variables are indexed from
zero; the sum over range d is the paper's sum from one through d. The
literal denominator is 1 minus the standard normal distribution function. -/
def Theorem4_3 : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω),IsProbabilityMeasure μ →
  ∀ Y : ℕ→Ω→ℝ,(∀ i,Measurable (Y i)) →
    ProbabilityTheory.iIndepFun Y μ →
    (∀ i,ProbabilityTheory.IdentDistrib (Y i) (Y 0) μ μ) →
    (∫ ω,Y 0 ω∂μ)=0 →
    ∀ σ : ℝ,0<σ → ProbabilityTheory.variance (Y 0) μ=σ^2 →
      0∈interior (ProbabilityTheory.integrableExpSet (Y 0) μ) →
      ∀ v : ℕ→ℝ,(∀ d,0≤v d) →
        Asymptotics.IsLittleO atTop v (fun d=>(d:ℝ)^(1/6:ℝ)) →
        Tendsto (fun d=>sSup {e : ℝ | ∃ z∈Icc (0:ℝ) (v d),
          e=|μ.real {ω | (∑ i∈Finset.range d,Y i ω)≤ -σ*Real.sqrt (d:ℝ)*z}/
            (1-Lower.standardNormalCDF z)-1|}) atTop (𝓝 0)

/-- Lemma 4.4, source lines 2157–2164. Constants and the dimension
threshold may depend on the fixed s₀, but not on d or s. -/
def Lemma4_4 : Prop := ∀ s₀ : ℝ,0<s₀ →
  ∃ c C : ℝ,0<c ∧ 0<C ∧ ∃ d₀ : ℕ,∀ d≥d₀,∀ s∈Icc (0:ℝ) s₀,
    c*(Lower.rate d)^(-1/2:ℝ)*Real.exp (-(2/Lower.squareVariance)*Lower.rate d*(1+s)^2)≤Lower.sliceMass d s ∧
    Lower.sliceMass d s≤C*(Lower.rate d)^(-1/2:ℝ)*Real.exp (-(2/Lower.squareVariance)*Lower.rate d*(1+s)^2)

/-- Lemma 4.5, source lines 2196–2202, in every positive dimension. -/
def Lemma4_5 : Prop := ∀ d : ℕ,0<d → ∀ s : ℝ,0≤s →
  Lower.sliceMass d s≤Real.exp (-(8/9:ℝ)*Lower.rate d*(1+s)^2)

/-- Lemma 4.6, source lines 2215–2222. One pair of numerical constants
and one threshold works for the two-element set of moment orders. -/
def Lemma4_6 : Prop := ∃ c C : ℝ,0<c ∧ 0<C ∧ ∃ d₀ : ℕ,∀ d≥d₀,∀ ℓ : ℕ,ℓ=0 ∨ ℓ=2 →
  c*Lower.sliceMass d 0/(Lower.rate d)^(ℓ+1)≤Lower.sliceMoment d ℓ ∧
  Lower.sliceMoment d ℓ≤C*Lower.sliceMass d 0/(Lower.rate d)^(ℓ+1)

/-- Lemma 4.7, source lines 2269–2279: both raw scales, the exact axial
slice-integral ratio and the displayed equality of the two scale formulas. -/
def Lemma4_7 : Prop := ∃ c C : ℝ,0<c ∧ 0<C ∧ ∃ d₀ : ℕ,∀ d≥d₀,
  (∀ i : Fin d,(1/4:ℝ)≤Lower.transverseVariance i ∧ Lower.transverseVariance i≤3) ∧
  Lower.axialVariance d=Lower.sliceMoment d 2/Lower.sliceMoment d 0 ∧
  c*(Lower.rate d)^(-2:ℝ)≤Lower.axialVariance d ∧
  Lower.axialVariance d≤C*(Lower.rate d)^(-2:ℝ) ∧
  (Lower.rate d)^(-2:ℝ)=(d:ℝ)^(-2/5:ℝ)

/-- Corollary 4.8, source lines 2329–2335. Every transverse coordinate
may be used for the common variance, and both coordinate maps are actual
inverses. The explicit formulas are definitions in Section4Definitions. -/
def Corollary4_8 : Prop := ∃ c C : ℝ,0<c ∧ 0<C ∧ ∃ d₀ : ℕ,∀ d≥d₀,∀ i : Fin d,
  convexBody (Lower.isotropicBody i) ∧ unconditional (Lower.isotropicBody i) ∧
  isotropic (uniform (Lower.isotropicBody i)) ∧
  c*Lower.rate d≤(Real.sqrt (Lower.axialVariance d))⁻¹ ∧
  (Real.sqrt (Lower.axialVariance d))⁻¹≤C*Lower.rate d ∧
  (∀ p : Lower.RawSpace d,Lower.inverseIsotropization i (Lower.isotropization i p)=p) ∧
  (∀ p : Lower.RawSpace d,Lower.isotropization i (Lower.inverseIsotropization i p)=p)

/-- Lemma 4.9, source lines 2381–2389. The actual infimum on the entire
Gaussian window is retained. The dimension threshold follows the fixed A. -/
def Lemma4_9 : Prop := ∃ A₀ : ℝ,0<A₀ ∧ ∀ A≥max 1 A₀,
  ∃ d₀ : ℕ,∀ d≥d₀,∀ i : Fin d,
    1-Real.exp (-2*Lower.rate d/9)≤
      sInf (Lower.acceptance i A '' {z : ℝ | |z|≤(Real.sqrt (Lower.precision d A))⁻¹}) ∧
    (1/2:ℝ)≤1-Real.exp (-2*Lower.rate d/9)

/-- The literal same-c chain printed in Corollary 4.10. This target is
kept even though the arithmetic conflict is separately proved. -/
def Literal410 : Prop := ∃ A₀ : ℝ,0<A₀ ∧ ∀ A≥max 1 A₀,
  ∃ c : ℝ,0<c ∧ ∃ d₀ : ℕ,∀ d≥d₀,∀ i : Fin d,
    Measure.map (fun x : Space (d+1)=>x 0)
      (gaussianTilt (uniform (Lower.isotropicBody i)) (Lower.precision d A))=Lower.axialMarginal i A ∧
    c/Lower.precision d A≤Lower.axialTiltVariance i A ∧
    c*(d:ℝ)^(2/5:ℝ)≤c/Lower.precision d A

/-- Minimal constant-renaming interpretation of Corollary 4.10, with the
arbitrary fixed A retained. This is not identified with Literal410. -/
def Corrected410 : Prop := ∃ A₀ : ℝ,0<A₀ ∧ ∀ A≥max 1 A₀,
  ∃ c₁ c₂ : ℝ,0<c₁ ∧ 0<c₂ ∧ ∃ d₀ : ℕ,∀ d≥d₀,∀ i : Fin d,
    Measure.map (fun x : Space (d+1)=>x 0)
      (gaussianTilt (uniform (Lower.isotropicBody i)) (Lower.precision d A))=Lower.axialMarginal i A ∧
    c₁/Lower.precision d A≤Lower.axialTiltVariance i A ∧
    c₂*(d:ℝ)^(2/5:ℝ)≤c₁/Lower.precision d A

/-- Corollary 4.10 as printed, source lines 2419–2428. -/
def Corollary4_10 : Prop := Literal410

end GaussianTilt.Reference
