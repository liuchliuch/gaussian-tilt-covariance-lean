import GaussianTilt.LetwinMatrixCalculus
import GaussianTilt.LetwinPotential

/-!
# Identifying the Monge--Ampère diffusion

The drift is derived by differentiating the given Monge--Ampère equation and
the actual inverse Hessian. No Stein or generator identity is assumed.
-/
noncomputable section
open Matrix MeasureTheory Filter Set
open scoped BigOperators Topology ContDiff
namespace GaussianTilt.Letwin

def inverseHessian {n : ℕ} (φ : CoordinateSpace n → ℝ) (x : CoordinateSpace n) :
    Matrix (Fin n) (Fin n) ℝ := (coordinateHessian φ x)⁻¹

def diffusionDrift {n : ℕ} (φ : CoordinateSpace n → ℝ)
    (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ) (x : CoordinateSpace n) (j : Fin n) : ℝ :=
  (∑ i, coordinateDerivative i (fun y => A y i j) x) -
    ∑ i, coordinateDerivative i φ x * A x i j

lemma contDiff_inverseHessian {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 3 φ) (hdet : ∀ x, (coordinateHessian φ x).det ≠ 0) (i j : Fin n) :
    ContDiff ℝ 1 (fun x => inverseHessian φ x i j) :=
  contDiff_matrix_inv (contDiff_coordinateHessian hφ) hdet i j

/-- Divergence of the inverse Hessian, derived from inverse differentiation
and commutation of third derivatives. -/
theorem divergence_inverseHessian {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 3 φ) (hdet : ∀ x, (coordinateHessian φ x).det ≠ 0)
    (x : CoordinateSpace n) (j : Fin n) :
    (∑ i, coordinateDerivative i (fun y => inverseHessian φ y i j) x) =
      -(∑ b, Matrix.trace (inverseHessian φ x * matrixCoordinateDerivative (coordinateHessian φ) b x) *
        inverseHessian φ x b j) := by
  let H := coordinateHessian φ
  let A := inverseHessian φ x
  have hs (i a b : Fin n) : matrixCoordinateDerivative H i x a b =
      matrixCoordinateDerivative H b x a i := coordinateThirdDerivative_swap_last hφ x a b i
  change (∑ i, matrixCoordinateDerivative (fun y => (H y)⁻¹) i x i j) = _
  simp_rw [matrixCoordinateDerivative_inv (H := H) (contDiff_coordinateHessian hφ) hdet]
  simp only [Matrix.neg_apply, Finset.sum_neg_distrib]
  congr 1
  change (∑ i, (A * matrixCoordinateDerivative H i x * A) i j) =
    ∑ b, Matrix.trace (A * matrixCoordinateDerivative H b x) * A b j
  calc
    _ = ∑ i, ∑ b, (∑ a, A i a * matrixCoordinateDerivative H b x a i) * A b j := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro b _
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      rw [hs i a b]
    _ = ∑ b, ∑ i, (∑ a, A i a * matrixCoordinateDerivative H b x a i) * A b j := Finset.sum_comm
    _ = _ := by simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Finset.sum_mul]

/-- The actual Monge--Ampère equation determines the drift of the divergence
operator as minus the target potential's score. -/
theorem diffusionDrift_inverseHessian {n : ℕ} {φ V : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 3 φ) (hV : ∀ y, DifferentiableAt ℝ V (coordinateGradient φ y))
    (hdet : ∀ x, (coordinateHessian φ x).det ≠ 0)
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x + V (coordinateGradient φ x))
    (x : CoordinateSpace n) (j : Fin n) :
    diffusionDrift φ (inverseHessian φ) x j = -coordinateDerivative j V (coordinateGradient φ x) := by
  rw [diffusionDrift, divergence_inverseHessian hφ hdet]
  have htrace (b : Fin n) : Matrix.trace
      (inverseHessian φ x * matrixCoordinateDerivative (coordinateHessian φ) b x) =
      -coordinateDerivative b φ x +
        ∑ a, coordinateDerivative a V (coordinateGradient φ x) * coordinateHessian φ x a b :=
    differentiated_mongeAmpere hφ hV hdet hMA b x
  simp_rw [htrace]
  have hmul : (∑ b, (∑ a, coordinateDerivative a V (coordinateGradient φ x) * coordinateHessian φ x a b) *
      inverseHessian φ x b j) = coordinateDerivative j V (coordinateGradient φ x) := by
    change ((coordinateGradient V (coordinateGradient φ x) ᵥ* coordinateHessian φ x) ᵥ*
      (coordinateHessian φ x)⁻¹) j = _
    rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hdet x)), Matrix.vecMul_one]
    rfl
  simp only [add_mul, neg_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  rw [hmul]
  ring

/-- Expanding the actual divergence-form operator gives its Hessian and drift
terms. -/
theorem divergenceDiffusion_eq_trace_add_drift {n : ℕ}
    (φ : CoordinateSpace n → ℝ) {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    {f : CoordinateSpace n → ℝ}
    (hA : ∀ i j, ContDiff ℝ 1 (fun x => A x i j)) (hf : ContDiff ℝ 2 f) (x : CoordinateSpace n) :
    divergenceDiffusion φ A f x = Matrix.trace (A x * coordinateHessian f x) +
      ∑ j, diffusionDrift φ A x j * coordinateDerivative j f x := by
  have hdf (j : Fin n) : Differentiable ℝ (coordinateDerivative j f) :=
    (contDiff_coordinateDerivative hf (m := 1) (by norm_num) j).differentiable le_rfl
  have hAd := fun i j => (hA i j).differentiable le_rfl
  have hrow (i : Fin n) : weightedCoordinateDivergence φ (diffusionFlux A f i) i x =
      (∑ j, A x i j * coordinateHessian f x j i) +
      ∑ j, (coordinateDerivative i (fun y => A y i j) x - coordinateDerivative i φ x * A x i j) *
        coordinateDerivative j f x := by
    change coordinateDerivative i (fun y => ∑ j, A y i j * coordinateDerivative j f y) x -
      coordinateDerivative i φ x * (∑ j, A x i j * coordinateDerivative j f x) = _
    rw [coordinateDerivative_sum (fun j y => A y i j * coordinateDerivative j f y)
      (fun j => (hAd i j).mul (hdf j))]
    simp only [coordinateDerivative_mul (hAd _ _) (hdf _), Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [coordinateHessian]
    ring
  simp only [divergenceDiffusion, hrow, Finset.sum_add_distrib]
  have htrace : (∑ i, ∑ j, A x i j * coordinateHessian f x j i) =
      Matrix.trace (A x * coordinateHessian f x) := rfl
  rw [htrace]
  congr 1
  rw [Finset.sum_comm]
  simp only [diffusionDrift, Finset.sum_mul, Finset.sum_sub_distrib, sub_mul]

/-- The coordinate generator formula used by Letwin, derived from the actual
Monge--Ampère equation. -/
theorem mongeAmpere_generator_formula {n : ℕ} {φ V f : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 3 φ) (hV : ∀ y, DifferentiableAt ℝ V (coordinateGradient φ y)) (hf : ContDiff ℝ 2 f)
    (hdet : ∀ x, (coordinateHessian φ x).det ≠ 0)
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x + V (coordinateGradient φ x))
    (x : CoordinateSpace n) :
    divergenceDiffusion φ (inverseHessian φ) f x =
      Matrix.trace (inverseHessian φ x * coordinateHessian f x) -
      ∑ j, coordinateDerivative j V (coordinateGradient φ x) * coordinateDerivative j f x := by
  rw [divergenceDiffusion_eq_trace_add_drift φ (contDiff_inverseHessian hφ hdet) hf]
  simp_rw [diffusionDrift_inverseHessian hφ hV hdet hMA]
  simp only [neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]

/-- Applying the identified generator to its own potential gives the
Lyapunov identity needed for A4. -/
theorem mongeAmpere_generator_potential {n : ℕ} {φ V : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 3 φ) (hV : ∀ y, DifferentiableAt ℝ V (coordinateGradient φ y))
    (hdet : ∀ x, (coordinateHessian φ x).det ≠ 0)
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x + V (coordinateGradient φ x))
    (x : CoordinateSpace n) :
    divergenceDiffusion φ (inverseHessian φ) φ x = (n : ℝ) -
      ∑ j, coordinateDerivative j V (coordinateGradient φ x) * coordinateDerivative j φ x := by
  rw [mongeAmpere_generator_formula hφ hV (hφ.of_le (by norm_num)) hdet hMA]
  rw [inverseHessian, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hdet x)), Matrix.trace_one]
  simp

/-- Bounded source and target scores imply the actual generator bound needed
by the constructed cutoffs. -/
theorem mongeAmpere_generator_potential_bound {n : ℕ} {φ V : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 3 φ) (hV : ∀ y, DifferentiableAt ℝ V (coordinateGradient φ y))
    (hdet : ∀ x, (coordinateHessian φ x).det ≠ 0)
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x + V (coordinateGradient φ x))
    {R S : ℝ} (hS : 0 ≤ S)
    (hφb : ∀ x j, |coordinateDerivative j φ x| ≤ R)
    (hVb : ∀ x j, |coordinateDerivative j V (coordinateGradient φ x)| ≤ S)
    (x : CoordinateSpace n) :
    |divergenceDiffusion φ (inverseHessian φ) φ x| ≤ (n : ℝ) * (1 + S * R) := by
  rw [mongeAmpere_generator_potential hφ hV hdet hMA]
  calc
    _ ≤ |(n : ℝ)| + |∑ j, coordinateDerivative j V (coordinateGradient φ x) * coordinateDerivative j φ x| :=
      abs_sub _ _
    _ ≤ n + ∑ j : Fin n, S * R := by
      rw [abs_of_nonneg (Nat.cast_nonneg n)]
      apply add_le_add_left
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul (hVb x j) (hφb x j) (abs_nonneg _) hS
    _ = _ := by simp; ring

/-- Appendix A4 under the actual regular Monge--Ampère hypotheses: the
potential is smooth and convex, its Hessian is positive definite, its gradient
lands in a compact set, and the target potential is C¹ near that set. The
cutoffs, properness, Lyapunov identity, and O(1/R) decay are all proved. -/
theorem regular_mongeAmpere_cutoffs {n : ℕ} {φ V : CoordinateSpace n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ ∞ φ) (hc : ConvexOn ℝ univ φ)
    (hH : ∀ x, (coordinateHessian φ x).PosDef)
    {K U : Set (CoordinateSpace n)} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hgrad : ∀ x, coordinateGradient φ x ∈ K) (hV : ContDiffOn ℝ 1 V U)
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x + V (coordinateGradient φ x)) :
    ∃ χ : ℕ → CoordinateSpace n → ℝ, ∃ C : ℝ, 0 ≤ C ∧
      (∀ k, ContDiff ℝ ∞ (χ k) ∧ HasCompactSupport (χ k)) ∧
      (∀ k x, 0 ≤ χ k x ∧ χ k x ≤ 1) ∧
      (∀ x, Monotone (fun k => χ k x)) ∧
      (∀ x, Tendsto (fun k => χ k x) atTop (𝓝 1)) ∧
      (∀ k, (∫ x, ‖divergenceDiffusion φ (inverseHessian φ) (χ k) x‖ ∂potentialMeasure φ) ≤
        C / ((k : ℝ) + 1)) := by
  have hφ3 : ContDiff ℝ 3 φ := contDiff_infty.mp hφ 3
  have hdet : ∀ x, (coordinateHessian φ x).det ≠ 0 := fun x => (hH x).det_pos.ne'
  have hVd : ∀ x, DifferentiableAt ℝ V (coordinateGradient φ x) :=
    fun x => (hV.differentiableOn le_rfl).differentiableAt (hU.mem_nhds (hKU (hgrad x)))
  have hVgc : ContinuousOn (coordinateGradient V) U := by
    apply continuousOn_pi.mpr
    intro j
    exact (hV.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn (continuous_id.continuousOn)
  obtain ⟨S, hS⟩ := hK.exists_bound_of_continuousOn (hVgc.mono hKU)
  have hφb : ∀ x j, |coordinateDerivative j φ x| ≤ max R 0 := by
    intro x j
    calc
      _ ≤ ‖coordinateGradient φ x‖ := by
        simpa only [coordinateGradient, Real.norm_eq_abs] using norm_le_pi_norm (coordinateGradient φ x) j
      _ ≤ R := hR _ (hgrad x)
      _ ≤ max R 0 := le_max_left _ _
  have hVb : ∀ x j, |coordinateDerivative j V (coordinateGradient φ x)| ≤ max S 0 := by
    intro x j
    calc
      _ ≤ ‖coordinateGradient V (coordinateGradient φ x)‖ := by
        simpa only [coordinateGradient, Real.norm_eq_abs] using
          norm_le_pi_norm (coordinateGradient V (coordinateGradient φ x)) j
      _ ≤ S := hS _ (hgrad x)
      _ ≤ max S 0 := le_max_left _ _
  have hi : Integrable (fun x => Real.exp (-φ x)) := by
    simpa using (integrable_potentialMeasure_iff hφ.continuous (fun _ => (1 : ℝ))).mp (integrable_const 1)
  exact exists_diffusion_cutoffs_of_convexPotential hφ hc hi
    (contDiff_inverseHessian hφ3 hdet) (fun x => (hH x).posSemidef.inv)
    ((n : ℝ) * (1 + max S 0 * max R 0))
    (mongeAmpere_generator_potential_bound hφ3 hVd hdet hMA (le_max_right _ _) hφb hVb)

/-- Appendix A5 for the actual regular Monge--Ampère diffusion. The cutoffs
and tested symmetry are now proved and instantiated; neither integrability of
Lf nor its zero mean is assumed. -/
theorem regular_mongeAmpere_conservation {n : ℕ} {φ V f : CoordinateSpace n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ ∞ φ) (hc : ConvexOn ℝ univ φ)
    (hH : ∀ x, (coordinateHessian φ x).PosDef)
    {K U : Set (CoordinateSpace n)} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hgrad : ∀ x, coordinateGradient φ x ∈ K) (hV : ContDiffOn ℝ 1 V U)
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x + V (coordinateGradient φ x))
    (hf : ContDiff ℝ ∞ f) (c B : ℝ) (hB : ∀ᵐ x ∂potentialMeasure φ, ‖f x‖ ≤ B)
    (hsub : ∀ᵐ x ∂potentialMeasure φ, 0 ≤ divergenceDiffusion φ (inverseHessian φ) f x + c * f x) :
    Integrable (divergenceDiffusion φ (inverseHessian φ) f) (potentialMeasure φ) ∧
      (∫ x, divergenceDiffusion φ (inverseHessian φ) f x ∂potentialMeasure φ) = 0 := by
  obtain ⟨χ, C, hC, hχ, hχ01, hχmono, hχlim, hdecay⟩ :=
    regular_mongeAmpere_cutoffs hφ hc hH hK hU hKU hgrad hV hMA
  have hφ1 : ContDiff ℝ 1 φ := contDiff_infty.mp hφ 1
  have hφ3 : ContDiff ℝ 3 φ := contDiff_infty.mp hφ 3
  have hf2 : ContDiff ℝ 2 f := contDiff_infty.mp hf 2
  have hdet : ∀ x, (coordinateHessian φ x).det ≠ 0 := fun x => (hH x).det_pos.ne'
  have hA := contDiff_inverseHessian hφ3 hdet
  have hAs (x : CoordinateSpace n) : (inverseHessian φ x).IsSymm := by
    have h := (hH x).posSemidef.inv.isHermitian
    simpa only [Matrix.IsHermitian, Matrix.IsSymm, Matrix.conjTranspose_eq_transpose_of_trivial] using h
  have hLf := continuous_divergenceDiffusion hφ1 hA hf2
  have hχint (k : ℕ) : Integrable
      (fun x => χ k x * divergenceDiffusion φ (inverseHessian φ) f x) (potentialMeasure φ) :=
    ((hχ k).1.continuous.mul hLf).integrable_of_hasCompactSupport (hχ k).2.mul_right
  have hLχint (k : ℕ) : Integrable
      (divergenceDiffusion φ (inverseHessian φ) (χ k)) (potentialMeasure φ) :=
    (continuous_divergenceDiffusion hφ1 hA (contDiff_infty.mp (hχ k).1 2)).integrable_of_hasCompactSupport
      (divergenceDiffusion_hasCompactSupport φ (inverseHessian φ) (hχ k).2)
  have hLχlim : Tendsto
      (fun k => ∫ x, ‖divergenceDiffusion φ (inverseHessian φ) (χ k) x‖ ∂potentialMeasure φ)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun k => integral_nonneg fun x => norm_nonneg _) hdecay
    have h := (tendsto_add_atTop_iff_nat 1).2 (tendsto_const_div_atTop_nhds_zero_nat C)
    simpa only [Nat.cast_add, Nat.cast_one] using h
  exact integrable_and_integral_eq_zero_of_cutoff_symmetry c B
    hf.continuous.aestronglyMeasurable hLf.aestronglyMeasurable hB hsub
    (fun k => (hχ k).1.continuous.aestronglyMeasurable)
    (fun k => Filter.Eventually.of_forall fun x => (hχ01 k x).1)
    (fun k => Filter.Eventually.of_forall fun x => (hχ01 k x).2)
    (Filter.Eventually.of_forall hχlim) hχint hLχint hLχlim
    (fun k => divergenceDiffusion_test_symmetry hφ1 hA hAs hf2
      (contDiff_infty.mp (hχ k).1 2) (hχ k).2)

end GaussianTilt.Letwin
