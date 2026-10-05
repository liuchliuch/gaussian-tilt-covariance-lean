import GaussianTilt.LetwinSign

/-! # Genuine nonsingular symmetric approximation and quadratic variance limits

Only zero eigenvalues are replaced, by positive numbers tending to zero.
Quadratic variance is an explicitly proved polynomial in matrix entries under
the natural fourth-moment hypotheses. This removes invertibility restrictions
without assuming a variance estimate for the limiting matrix.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix Filter
open scoped BigOperators Topology
set_option linter.unusedSectionVars false

namespace GaussianTilt.Whitening

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι]

def spectralRegularization {B : Matrix ι ι ℝ} (hB : B.IsHermitian) (k : ℕ) : Matrix ι ι ℝ :=
  (hB.eigenvectorUnitary : Matrix ι ι ℝ) *
    diagonal (fun i ↦ if hB.eigenvalues i = 0 then ((k : ℝ) + 1)⁻¹ else hB.eigenvalues i) *
    star (hB.eigenvectorUnitary : Matrix ι ι ℝ)

lemma spectralRegularization_isSymm {B : Matrix ι ι ℝ} (hB : B.IsHermitian) (k : ℕ) :
    (spectralRegularization hB k).IsSymm :=
  Letwin.real_unitary_conjugate_isSymm _ _ (Matrix.isSymm_diagonal _)

lemma spectralRegularization_det_ne_zero {B : Matrix ι ι ℝ} (hB : B.IsHermitian) (k : ℕ) :
    (spectralRegularization hB k).det ≠ 0 := by
  have hU : IsUnit (hB.eigenvectorUnitary : Matrix ι ι ℝ) := by
    rw [← unitary.val_toUnits_apply]
    exact Units.isUnit _
  have hD : IsUnit (diagonal (fun i ↦
      if hB.eigenvalues i = 0 then ((k : ℝ) + 1)⁻¹ else hB.eigenvalues i)) := by
    apply Matrix.isUnit_diagonal.mpr
    apply Pi.isUnit_iff.mpr
    intro i
    apply isUnit_iff_ne_zero.mpr
    split_ifs with h
    · positivity
    · exact h
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp ((hU.mul hD).mul hU.star))

lemma spectralRegularization_tendsto {B : Matrix ι ι ℝ} (hB : B.IsHermitian) :
    Tendsto (spectralRegularization hB) atTop (𝓝 B) := by
  have he : Tendsto (fun k : ℕ ↦ fun i : ι ↦
      if hB.eigenvalues i = 0 then ((k : ℝ) + 1)⁻¹ else hB.eigenvalues i)
      atTop (𝓝 hB.eigenvalues) := by
    apply tendsto_pi_nhds.mpr
    intro i
    by_cases hi : hB.eigenvalues i = 0
    · simp only [hi, if_true]
      exact tendsto_inv_atTop_zero.comp
        (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
    · simp only [hi, if_false]
      exact tendsto_const_nhds
  have hd := (show Continuous (fun v : ι → ℝ ↦ Matrix.diagonal v) by fun_prop).tendsto _ |>.comp he
  have h := (tendsto_const_nhds (x := (hB.eigenvectorUnitary : Matrix ι ι ℝ))).mul hd
    |>.mul (tendsto_const_nhds (x := star (hB.eigenvectorUnitary : Matrix ι ι ℝ)))
  have hspec : B = (hB.eigenvectorUnitary : Matrix ι ι ℝ) *
      Matrix.diagonal hB.eigenvalues * star (hB.eigenvectorUnitary : Matrix ι ι ℝ) := hB.spectral_theorem
  rw [← hspec] at h
  exact h

lemma matrixQuadratic_expansion (B : Matrix ι ι ℝ) (x : ι → ℝ) :
    matrixQuadratic B x = ∑ i, ∑ j, B i j * (x i * x j) := by
  simp only [matrixQuadratic, dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

variable [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → ι → ℝ}

lemma quadratic_memLp_of_products (hX : ∀ i j, MemLp (fun ω ↦ X ω i * X ω j) 2 μ)
    (B : Matrix ι ι ℝ) : MemLp (fun ω ↦ matrixQuadratic B (X ω)) 2 μ := by
  simp_rw [matrixQuadratic_expansion]
  exact memLp_finset_sum _ (fun i _ ↦ memLp_finset_sum _ (fun j _ ↦ (hX i j).const_mul (B i j)))

lemma covariance_quadratic_left (hX : ∀ i j, MemLp (fun ω ↦ X ω i * X ω j) 2 μ)
    {Y : Ω → ℝ} (hY : MemLp Y 2 μ) (B : Matrix ι ι ℝ) :
    covariance (fun ω ↦ matrixQuadratic B (X ω)) Y μ =
      ∑ i, ∑ j, B i j * covariance (fun ω ↦ X ω i * X ω j) Y μ := by
  simp_rw [matrixQuadratic_expansion]
  rw [covariance_fun_sum_left
    (fun i ↦ memLp_finset_sum _ (fun j _ ↦ (hX i j).const_mul (B i j))) hY]
  apply Finset.sum_congr rfl
  intro i _
  rw [covariance_fun_sum_left (fun j ↦ (hX i j).const_mul (B i j)) hY]
  simp only [covariance_mul_left]

lemma quadratic_variance_eq_polynomial
    (hX : ∀ i j, MemLp (fun ω ↦ X ω i * X ω j) 2 μ) (B : Matrix ι ι ℝ) :
    variance (fun ω ↦ matrixQuadratic B (X ω)) μ =
      ∑ i, ∑ j, ∑ k, ∑ l, B i j * B k l *
        covariance (fun ω ↦ X ω i * X ω j) (fun ω ↦ X ω k * X ω l) μ := by
  rw [← covariance_self (quadratic_memLp_of_products hX B).aemeasurable,
    covariance_quadratic_left hX (quadratic_memLp_of_products hX B) B]
  have hr (i j : ι) : covariance (fun ω ↦ X ω i * X ω j)
      (fun ω ↦ matrixQuadratic B (X ω)) μ =
      ∑ k, ∑ l, B k l * covariance (fun ω ↦ X ω i * X ω j)
        (fun ω ↦ X ω k * X ω l) μ := by
    rw [covariance_comm, covariance_quadratic_left hX (hX i j) B]
    simp only [covariance_comm]
  simp only [hr, Finset.mul_sum, mul_assoc]

theorem continuous_quadratic_variance
    (hX : ∀ i j, MemLp (fun ω ↦ X ω i * X ω j) 2 μ) :
    Continuous (fun B : Matrix ι ι ℝ ↦ variance (fun ω ↦ matrixQuadratic B (X ω)) μ) := by
  simp_rw [quadratic_variance_eq_polynomial hX]
  fun_prop

theorem quadratic_variance_tendsto
    (hX : ∀ i j, MemLp (fun ω ↦ X ω i * X ω j) 2 μ)
    {B : Matrix ι ι ℝ} {A : ℕ → Matrix ι ι ℝ} (hA : Tendsto A atTop (𝓝 B)) :
    Tendsto (fun k ↦ variance (fun ω ↦ matrixQuadratic (A k) (X ω)) μ)
      atTop (𝓝 (variance (fun ω ↦ matrixQuadratic B (X ω)) μ)) :=
  (continuous_quadratic_variance hX).continuousAt.tendsto.comp hA

/-- A proved nonsingular quadratic-variance inequality automatically extends
to every symmetric matrix, with the same constant. -/
theorem quadratic_bound_of_invertible
    (hX : ∀ i j, MemLp (fun ω ↦ X ω i * X ω j) 2 μ) {C : ℝ}
    (hbound : ∀ B : Matrix ι ι ℝ, B.IsSymm → B.det ≠ 0 →
      variance (fun ω ↦ matrixQuadratic B (X ω)) μ ≤ C * Matrix.trace (B ^ 2))
    (B : Matrix ι ι ℝ) (hB : B.IsSymm) :
    variance (fun ω ↦ matrixQuadratic B (X ω)) μ ≤ C * Matrix.trace (B ^ 2) := by
  have hBh : B.IsHermitian := by
    simpa only [Matrix.IsHermitian, Matrix.IsSymm, Matrix.conjTranspose_eq_transpose_of_trivial] using hB
  have ht := spectralRegularization_tendsto hBh
  have hv := quadratic_variance_tendsto hX ht
  have hr := (show Continuous (fun A : Matrix ι ι ℝ ↦ C * Matrix.trace (A ^ 2)) by
    unfold Matrix.trace Matrix.diag
    fun_prop).continuousAt.tendsto.comp ht
  exact le_of_tendsto_of_tendsto hv hr (Eventually.of_forall (fun k ↦
    hbound _ (spectralRegularization_isSymm hBh k) (spectralRegularization_det_ne_zero hBh k)))

end GaussianTilt.Whitening
