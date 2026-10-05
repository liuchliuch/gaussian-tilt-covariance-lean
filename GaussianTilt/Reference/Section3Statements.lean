import GaussianTilt.Reference.NumberedDefinitions

/-!
# Independent targets for the ten numbered statements of Section 3

Source: pinned `paper/source/main.tex`, section `sec:upper`, lines 1554--1995.
Only the independent Reference definitions and Mathlib are imported. Every
declaration below is a proposition definition, not a proof or closure claim.
Universal constants precede dimension, measure, and time quantifiers.

Implementation-side bridges belong in `Section3StatementBridges.lean`.
The mapping is: 3.1 `upperBound_of_isotropic_bound`; 3.2
`original3_2_of_isotropic_bound` plus genuine log-HS differentiability;
3.3 `original3_3_of_isotropic_bound`; 3.4 `renyi_comparison_conjugate`;
3.5 `projected_second_moment_estimate`; 3.6 `earlier_time_spectral_profile`;
3.7 `original3_7_of_isotropic_bound`; 3.8 `original3_8_of_isotropic_bound`;
3.9 and 3.10 `original3_9_and_3_10_of_isotropic_bound`.
Those names are documentation only and introduce no import dependency.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Matrix.Norms.L2Operator
namespace GaussianTilt.Reference

/-- Theorem 3.1 (`thm:upper-general`): the universal n^(2/5) upper bound. -/
def Theorem3_1 : Prop := UpperBound

/- The paper's nondegeneracy convention makes the ambient dimension
positive and S_t>0 when logarithmic differential estimates are used.
The explicit n>0 in 3.2, 3.3, and 3.7 records this convention; it is not
an additional analytic hypothesis. Dimension-zero companions, where
mathematical log S_t is undefined, are separate optional extensions. -/

/-- Lemma 3.2 (`lem:differential-estimates`): all three estimates, with
actual differentiability of log S and the extended-real upper Dini derivative. -/
def Lemma3_2 : Prop :=
  ∀ n : ℕ, 0 < n → ∀ μ : Measure (Space n),
    IsProbabilityMeasure μ → compactlySupported μ → isotropic μ → logconcave μ →
    ∀ t : ℝ, 0 ≤ t →
      observableVariance (gaussianTilt μ t) (fun x => ‖x‖^2) ≤ 10*(hilbertSchmidtAlong μ t)^2 ∧
      DifferentiableAt ℝ (fun s => Real.log (hilbertSchmidtAlong μ s)) t ∧
      |deriv (fun s => Real.log (hilbertSchmidtAlong μ s)) t| ≤ 10*‖momentAlong μ t‖ ∧
      upperRightDini (fun s => Real.log ‖momentAlong μ s‖) t ≤ ((10*hilbertSchmidtAlong μ t : ℝ) : EReal)

/-- Corollary 3.3 (`cor:integrated-differential`): both actual interval integrals. -/
def Corollary3_3 : Prop :=
  ∀ n : ℕ, 0 < n → ∀ μ : Measure (Space n),
    IsProbabilityMeasure μ → compactlySupported μ → isotropic μ → logconcave μ →
    ∀ a b : ℝ, 0 ≤ a → a < b →
      hilbertSchmidtAlong μ b ≤ hilbertSchmidtAlong μ a *
        Real.exp (10*∫ s in a..b, ‖momentAlong μ s‖) ∧
      ‖momentAlong μ b‖ ≤ ‖momentAlong μ a‖ *
        Real.exp (10*∫ s in a..b, hilbertSchmidtAlong μ s)

/-- Lemma 3.4 (`lem:renyi-comparison`): the conjugate order, exact log-partition
identity, and entropy upper bound, without dropping the equality. -/
def Lemma3_4 : Prop :=
  ∀ n : ℕ, ∀ μ : Measure (Space n),
    IsProbabilityMeasure μ → compactlySupported μ → isotropic μ → logconcave μ →
    ∀ T q : ℝ, 0 < T → 1 < q →
      let r := q/(q-1)
      renyi r (gaussianTilt μ (T/r)) μ =
        (logPartition μ T-r*logPartition μ (T/r))/(r-1) ∧
      (logPartition μ T-r*logPartition μ (T/r))/(r-1) ≤ entropyAlong μ T

/-- Lemma 3.5 (`lem:projected-second-moment`): every orthogonal projection,
its literal rank, and the exact trace/expectation equality at the earlier time. -/
def Lemma3_5 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ μ : Measure (Space n),
    IsProbabilityMeasure μ → compactlySupported μ → isotropic μ → logconcave μ →
    ∀ T q : ℝ, 0 < T → max 2 (entropyAlong μ T) ≤ q →
    ∀ P : Matrix (Fin n) (Fin n) ℝ, orthogonalProjectionMatrix P →
      let t := T*(1-1/q)
      Matrix.trace (P*momentAlong μ t) =
        (∫ x, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) P x‖^2 ∂gaussianTilt μ t) ∧
      (∫ x, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) P x‖^2 ∂gaussianTilt μ t) ≤
        C*((P.rank : ℝ)+q^2)

/-- Corollary 3.6 (`cor:spectral-profile`): the actual nonincreasing eigenvalue
sequence, indexed by j=i+1, and both consequential norm bounds with one
universal constant. The witness is a proof of symmetry of the actual matrix. -/
def Corollary3_6 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ μ : Measure (Space n),
    IsProbabilityMeasure μ → compactlySupported μ → isotropic μ → logconcave μ →
    ∀ T q : ℝ, 0 < T → max 2 (entropyAlong μ T) ≤ q →
      let t := T*(1-1/q)
      ∃ hA : (momentAlong μ t).IsHermitian,
        (∀ i : Fin n, hA.eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm i) ≤
          C*(1+q^2/((i.val : ℝ)+1))) ∧
        ‖momentAlong μ t‖ ≤ C*q^2 ∧
        hilbertSchmidtAlong μ t ≤ C*Real.sqrt ((n : ℝ)+q^4)

/-- Lemma 3.7 (`lem:short-time-stability`): both strict log-2 smallness
conditions and the closed interval, including both endpoints. -/
def Lemma3_7 : Prop :=
  ∀ n : ℕ, 0 < n → ∀ μ : Measure (Space n),
    IsProbabilityMeasure μ → compactlySupported μ → isotropic μ → logconcave μ →
    ∀ a b α β : ℝ, 0 ≤ a → a < b → 0 < α → 0 < β →
      ‖momentAlong μ a‖ ≤ α → hilbertSchmidtAlong μ a ≤ β →
      20*α*(b-a) < Real.log 2 → 20*β*(b-a) < Real.log 2 →
      ∀ s ∈ Icc a b, ‖momentAlong μ s‖ ≤ 2*α ∧ hilbertSchmidtAlong μ s ≤ 2*β

/-- Lemma 3.8 (`lem:endpoint-estimate`): all three universal constants and
all three simultaneous parameter constraints at the target time. -/
def Lemma3_8 : Prop :=
  ∃ εstar Cstar Csp : ℝ, 0 < εstar ∧ 0 < Cstar ∧ 0 < Csp ∧
    ∀ n : ℕ, ∀ μ : Measure (Space n),
      IsProbabilityMeasure μ → compactlySupported μ → isotropic μ → logconcave μ →
      ∀ T q : ℝ, 0 < T →
        Csp*max 1 (max (entropyAlong μ T) (T*Real.sqrt (n : ℝ))) ≤ q →
        q^4 ≤ (n : ℝ) → T*q ≤ εstar →
        ‖momentAlong μ T‖ ≤ Cstar*q^2 ∧ hilbertSchmidtAlong μ T ≤ Cstar*Real.sqrt (n : ℝ)

/-- Lemma 3.9 (`lem:entropy-barrier`): c, C_H, and the dimensional threshold
are universal, and the window contains t=0 and its upper endpoint. -/
def Lemma3_9 : Prop :=
  ∃ c CH : ℝ, 0 < c ∧ 0 < CH ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∀ μ : Measure (Space n),
      IsProbabilityMeasure μ → compactlySupported μ → isotropic μ → logconcave μ →
      ∀ t ∈ Icc 0 (c*(n : ℝ)^(-(3/8 : ℝ))),
        entropyAlong μ t ≤ CH*(n : ℝ)*t^2

/-- Proposition 3.10 (`prop:small-t-upper`): the complete covariance ≤
second-moment ≤ precision-profile chain, uniformly above one dimension threshold. -/
def Proposition3_10 : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∀ μ : Measure (Space n),
      IsProbabilityMeasure μ → compactlySupported μ → isotropic μ → logconcave μ →
      ∀ t ∈ Icc 0 (c*(n : ℝ)^(-(3/8 : ℝ))),
        ‖covariance (gaussianTilt μ t)‖ ≤ ‖momentAlong μ t‖ ∧
        ‖momentAlong μ t‖ ≤ C*(1+(n : ℝ)^2*t^4)

end GaussianTilt.Reference
