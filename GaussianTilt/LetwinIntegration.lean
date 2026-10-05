import Mathlib
import GaussianTilt.Quadratic

/-!
# Integration by parts for Letwin's moment measure

This file proves Appendix Lemma A3 of the pinned Letwin source directly from
one-dimensional improper FTC and Fubini. In particular the integration-by-parts
identity is not a hypothesis, and no boundary decay is assumed: integrability
of the product and its derivative supplies the vanishing boundary terms.

This does not construct a moment map or assert its regularity.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace GaussianTilt.Letwin

/-- The actual coordinate derivative in the finite product model of Euclidean
space. -/
def coordinateDerivative {n : ℕ} (i : Fin n) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  fderiv ℝ f x (Pi.single i 1)

/-- The exponential measure used in the moment-map argument. -/
def potentialMeasure {n : ℕ} (φ : (Fin n → ℝ) → ℝ) : Measure (Fin n → ℝ) :=
  volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x)))

lemma integral_potentialMeasure {n : ℕ} {φ : (Fin n → ℝ) → ℝ}
    (hφ : Continuous φ) (f : (Fin n → ℝ) → ℝ) :
    (∫ x, f x ∂potentialMeasure φ) = ∫ x, Real.exp (-φ x) * f x := by
  rw [potentialMeasure, integral_withDensity_eq_integral_toReal_smul]
  · simp only [ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul]
  · exact ((Real.continuous_exp.comp hφ.neg).measurable.ennreal_ofReal)
  · exact Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top

lemma integrable_potentialMeasure_iff {n : ℕ} {φ : (Fin n → ℝ) → ℝ}
    (hφ : Continuous φ) (f : (Fin n → ℝ) → ℝ) :
    Integrable f (potentialMeasure φ) ↔ Integrable (fun x => Real.exp (-φ x) * f x) := by
  have hw : Measurable (fun x => ENNReal.ofReal (Real.exp (-φ x))) := by fun_prop
  simpa only [potentialMeasure, ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul] using
    (integrable_withDensity_iff_integrable_smul' (μ := volume) (g := f) hw
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top))


lemma hasDerivAt_insertNth {n : ℕ} (i : Fin (n + 1)) (y : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => i.insertNth s y) (Pi.single i 1 : Fin (n + 1) → ℝ) t := by
  apply hasDerivAt_pi.mpr
  intro j
  obtain rfl | ⟨j, rfl⟩ := i.eq_self_or_eq_succAbove j
  · simpa using hasDerivAt_id t
  · simpa using hasDerivAt_const t (y j)

lemma hasDerivAt_slice {n : ℕ} (i : Fin (n + 1))
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : Differentiable ℝ f)
    (y : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (i.insertNth s y))
      (coordinateDerivative i f (i.insertNth t y)) t := by
  exact (hf (i.insertNth t y)).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_insertNth i y t)

/-- The integral of an integrable coordinate derivative of an integrable
function vanishes. The proof uses no smooth cutoffs and needs only
coordinatewise differentiability. -/
theorem integral_eq_zero_of_has_partial {n : ℕ} (i : Fin (n + 1))
    {f df : (Fin (n + 1) → ℝ) → ℝ}
    (hd : ∀ y : Fin n → ℝ, ∀ t : ℝ,
      HasDerivAt (fun s => f (i.insertNth s y)) (df (i.insertNth t y)) t)
    (hf : Integrable f) (hdf : Integrable df) : (∫ x, df x) = 0 := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm
  have he : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm _
  have hf' : Integrable (f ∘ e) := (he.integrable_comp_emb e.measurableEmbedding).mpr hf
  have hdf' : Integrable (df ∘ e) := (he.integrable_comp_emb e.measurableEmbedding).mpr hdf
  rw [← he.integral_comp' df]
  change (∫ x, (df ∘ e) x) = 0
  rw [Measure.volume_eq_prod, integral_prod_symm _ hdf']
  apply integral_eq_zero_of_ae
  filter_upwards [hf'.prod_left_ae, hdf'.prod_left_ae] with y hy hdy
  apply integral_eq_zero_of_hasDerivAt_of_integrable _ hdy hy
  intro t
  exact hd y t

/-- Whole-space coordinate FTC in terms of the actual Fréchet derivative. -/
theorem integral_partial_eq_zero {n : ℕ} (i : Fin n)
    {f : (Fin n → ℝ) → ℝ} (hd : Differentiable ℝ f)
    (hf : Integrable f) (hdf : Integrable (coordinateDerivative i f)) :
    (∫ x, coordinateDerivative i f x) = 0 := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n => exact integral_eq_zero_of_has_partial i (hasDerivAt_slice i hd) hf hdf

/-- Appendix Lemma A3: full-space weighted coordinate integration by parts.
The four integrability assumptions are exactly those in the source. All
boundary terms are proved to vanish, rather than assumed. -/
theorem weighted_integration_by_parts {n : ℕ} (i : Fin n)
    {φ f g : (Fin n → ℝ) → ℝ}
    (hφ : Differentiable ℝ φ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hdfg : Integrable (fun x => coordinateDerivative i f x * g x) (potentialMeasure φ))
    (hfdg : Integrable (fun x => f x * coordinateDerivative i g x) (potentialMeasure φ))
    (hfgdφ : Integrable (fun x => f x * g x * coordinateDerivative i φ x) (potentialMeasure φ))
    (hfg : Integrable (fun x => f x * g x) (potentialMeasure φ)) :
    (∫ x, coordinateDerivative i f x * g x ∂potentialMeasure φ) =
      ∫ x, f x * (coordinateDerivative i φ x * g x - coordinateDerivative i g x)
        ∂potentialMeasure φ := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    let w := fun x => Real.exp (-φ x)
    have hA := (integrable_potentialMeasure_iff hφ.continuous _).mp hdfg
    have hB := (integrable_potentialMeasure_iff hφ.continuous _).mp hfdg
    have hC := (integrable_potentialMeasure_iff hφ.continuous _).mp hfgdφ
    have hP := (integrable_potentialMeasure_iff hφ.continuous _).mp hfg
    let q := fun x => w x * (f x * g x)
    let dq := fun x => w x * (coordinateDerivative i f x * g x) +
      w x * (f x * coordinateDerivative i g x) -
      w x * (f x * g x * coordinateDerivative i φ x)
    have hdq : ∀ y : Fin n → ℝ, ∀ t : ℝ,
        HasDerivAt (fun s => q (i.insertNth s y)) (dq (i.insertNth t y)) t := by
      intro y t
      convert ((hasDerivAt_slice i hφ y t).neg.exp).mul
        ((hasDerivAt_slice i hf y t).mul (hasDerivAt_slice i hg y t)) using 1
      dsimp [q, dq, w]
      ring
    have hz := integral_eq_zero_of_has_partial i hdq hP ((hA.add hB).sub hC)
    change (∫ x, w x * (coordinateDerivative i f x * g x) +
      w x * (f x * coordinateDerivative i g x) -
      w x * (f x * g x * coordinateDerivative i φ x)) = 0 at hz
    dsimp [w] at hz
    have hsplit := integral_sub (hA.add hB) hC
    simp only [Pi.add_apply] at hsplit
    rw [hsplit, integral_add hA hB] at hz
    rw [integral_potentialMeasure hφ.continuous, integral_potentialMeasure hφ.continuous]
    have heq : (fun x => Real.exp (-φ x) *
        (f x * (coordinateDerivative i φ x * g x - coordinateDerivative i g x))) =
        (fun x => w x * (f x * g x * coordinateDerivative i φ x) -
          w x * (f x * coordinateDerivative i g x)) := by
      funext x
      dsimp [w]
      ring
    rw [heq]
    dsimp [w]
    rw [integral_sub hC hB]
    linarith

/-- The score identity, with integrability rather than boundary conditions. -/
theorem integral_coordinateDerivative {n : ℕ} (i : Fin n)
    {φ f : (Fin n → ℝ) → ℝ}
    (hφ : Differentiable ℝ φ) (hf : Differentiable ℝ f)
    (hdf : Integrable (coordinateDerivative i f) (potentialMeasure φ))
    (hfdφ : Integrable (fun x => f x * coordinateDerivative i φ x) (potentialMeasure φ))
    (hfi : Integrable f (potentialMeasure φ)) :
    (∫ x, coordinateDerivative i f x ∂potentialMeasure φ) =
      ∫ x, f x * coordinateDerivative i φ x ∂potentialMeasure φ := by
  have h := weighted_integration_by_parts i hφ hf (differentiable_const (1 : ℝ))
    (by simpa using hdf) (by simp [coordinateDerivative])
    (by simpa using hfdφ) (by simpa using hfi)
  simpa [coordinateDerivative] using h

/-- The score vector, written in coordinates. -/
def coordinateGradient {n : ℕ} (φ : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => coordinateDerivative i φ x

/-- The Hessian consists of actual second coordinate derivatives. -/
def coordinateHessian {n : ℕ} (φ : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => coordinateDerivative j (coordinateDerivative i φ) x

lemma contDiff_coordinateDerivative {n : ℕ} {φ : (Fin n → ℝ) → ℝ}
    {k m : WithTop ℕ∞} (hφ : ContDiff ℝ k φ) (hmk : m + 1 ≤ k) (i : Fin n) :
    ContDiff ℝ m (coordinateDerivative i φ) :=
  (hφ.fderiv_right hmk).clm_apply contDiff_const

/-- Integrable scores are centered under their own exponential measure. -/
theorem integral_coordinateGradient_eq_zero {n : ℕ} (i : Fin n)
    {φ : (Fin n → ℝ) → ℝ} [IsFiniteMeasure (potentialMeasure φ)]
    (hφ : Differentiable ℝ φ)
    (hi : Integrable (fun x => coordinateGradient φ x i) (potentialMeasure φ)) :
    (∫ x, coordinateGradient φ x i ∂potentialMeasure φ) = 0 := by
  have hz : coordinateDerivative i (fun _ : Fin n → ℝ => (1 : ℝ)) = 0 := by
    funext x
    simp [coordinateDerivative]
  have h := integral_coordinateDerivative i (φ := φ) (f := fun _ : Fin n → ℝ => (1 : ℝ))
    hφ (differentiable_const (1 : ℝ))
    (by rw [hz]; exact integrable_zero _ _ _)
    (by simpa [coordinateGradient] using hi)
    (integrable_const 1)
  rw [hz] at h
  simpa [coordinateGradient] using h.symm

/-- The Hessian-score identity underlying Letwin Lemma 2.3. No integration by
parts or Stein identity is postulated. -/
theorem integral_coordinateHessian {n : ℕ} (i j : Fin n)
    {φ : (Fin n → ℝ) → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hi : Integrable (fun x => coordinateGradient φ x i) (potentialMeasure φ))
    (hij : Integrable (fun x => coordinateHessian φ x i j) (potentialMeasure φ))
    (hprod : Integrable (fun x => coordinateGradient φ x i * coordinateGradient φ x j)
      (potentialMeasure φ)) :
    (∫ x, coordinateHessian φ x i j ∂potentialMeasure φ) =
      ∫ x, coordinateGradient φ x i * coordinateGradient φ x j ∂potentialMeasure φ := by
  exact integral_coordinateDerivative j (hφ.differentiable (by norm_num))
    ((contDiff_coordinateDerivative hφ (m := 1) (by norm_num) i).differentiable le_rfl)
    hij hprod hi

/-- The moment measure associated with a smooth potential. This is a
pushforward definition, not an existence assertion. -/
def momentMeasure {n : ℕ} (φ : (Fin n → ℝ) → ℝ) : Measure (Fin n → ℝ) :=
  (potentialMeasure φ).map (coordinateGradient φ)

lemma continuous_coordinateGradient {n : ℕ} {φ : (Fin n → ℝ) → ℝ}
    (hφ : ContDiff ℝ 1 φ) : Continuous (coordinateGradient φ) := by
  apply continuous_pi
  intro i
  exact (contDiff_coordinateDerivative hφ (m := 0) (by norm_num) i).continuous

/-- Passing the proved Hessian identity through the actual gradient
pushforward gives the second-moment identity in Lemma 2.3. -/
theorem integral_hessian_eq_moment_secondMoment {n : ℕ} (i j : Fin n)
    {φ : (Fin n → ℝ) → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hi : Integrable (fun x => coordinateGradient φ x i) (potentialMeasure φ))
    (hij : Integrable (fun x => coordinateHessian φ x i j) (potentialMeasure φ))
    (hprod : Integrable (fun x => coordinateGradient φ x i * coordinateGradient φ x j)
      (potentialMeasure φ)) :
    (∫ x, coordinateHessian φ x i j ∂potentialMeasure φ) =
      ∫ x, x i * x j ∂momentMeasure φ := by
  rw [momentMeasure, integral_map
    (continuous_coordinateGradient (hφ.of_le (by norm_num))).measurable.aemeasurable
    (by fun_prop)]
  exact integral_coordinateHessian i j hφ hi hij hprod

/-- The expected Hessian equals the score covariance. Centering of the score
is proved above; it is not an additional hypothesis. -/
theorem integral_hessian_eq_covariance {n : ℕ}
    {φ : (Fin n → ℝ) → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ)
    (hscore : ∀ i, MemLp (fun x => coordinateGradient φ x i) 2 (potentialMeasure φ))
    (hH : ∀ i j, Integrable (fun x => coordinateHessian φ x i j) (potentialMeasure φ)) :
    (fun i j => ∫ x, coordinateHessian φ x i j ∂potentialMeasure φ) =
      covarianceMatrix (potentialMeasure φ) (coordinateGradient φ) := by
  ext i j
  have hi := (hscore i).integrable (by norm_num)
  rw [integral_coordinateHessian i j hφ hi (hH i j) ((hscore i).integrable_mul (hscore j))]
  simp only [covarianceMatrix, ProbabilityTheory.covariance_eq_sub (hscore i) (hscore j)]
  rw [integral_coordinateGradient_eq_zero i (hφ.differentiable (by norm_num)) hi]
  simp

/-- Bounded gradient and Hessian, as supplied by the regular moment-map
construction, suffice for every integrability hypothesis in Lemma 2.3. -/
theorem integral_hessian_eq_covariance_of_bounded {n : ℕ}
    {φ : (Fin n → ℝ) → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (R S : ℝ)
    (hR : ∀ x i, |coordinateGradient φ x i| ≤ R)
    (hS : ∀ x i j, |coordinateHessian φ x i j| ≤ S) :
    (fun i j => ∫ x, coordinateHessian φ x i j ∂potentialMeasure φ) =
      covarianceMatrix (potentialMeasure φ) (coordinateGradient φ) := by
  apply integral_hessian_eq_covariance hφ
  · intro i
    exact MemLp.of_bound
      ((contDiff_coordinateDerivative hφ (m := 1) (by norm_num) i).continuous.aestronglyMeasurable)
      R (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hR x i)
  · intro i j
    have hc : Continuous (fun x => coordinateHessian φ x i j) :=
      (contDiff_coordinateDerivative
        (contDiff_coordinateDerivative hφ (m := 1) (by norm_num) i)
        (m := 0) (by norm_num) j).continuous
    exact (MemLp.of_bound hc.aestronglyMeasurable S (p := 1)
      (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hS x i j)).integrable le_rfl

/-- Letwin Lemma 2.3 for any C² moment potential with bounded gradient and
Hessian and isotropic gradient law. The actual Hessian expectation is the
identity matrix. -/
theorem integral_hessian_eq_one_of_isotropic {n : ℕ}
    {φ : (Fin n → ℝ) → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (R S : ℝ)
    (hR : ∀ x i, |coordinateGradient φ x i| ≤ R)
    (hS : ∀ x i j, |coordinateHessian φ x i j| ≤ S)
    (hiso : covarianceMatrix (potentialMeasure φ) (coordinateGradient φ) = 1) :
    (fun i j => ∫ x, coordinateHessian φ x i j ∂potentialMeasure φ) =
      (1 : Matrix (Fin n) (Fin n) ℝ) := by
  rw [integral_hessian_eq_covariance_of_bounded hφ R S hR hS, hiso]

/-- The coordinate Hessian agrees with the iterated Fréchet derivative. -/
lemma coordinateHessian_eq_fderiv_fderiv {n : ℕ} {φ : (Fin n → ℝ) → ℝ}
    (hφ : ContDiff ℝ 2 φ) (x : Fin n → ℝ) (i j : Fin n) :
    coordinateHessian φ x i j =
      fderiv ℝ (fderiv ℝ φ) x (Pi.single j 1) (Pi.single i 1) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    ((hφ.fderiv_right (m := 1) (by norm_num)).differentiable le_rfl) x
  change (fderiv ℝ (fun y => fderiv ℝ φ y (Pi.single i 1)) x) (Pi.single j 1) = _
  rw [fderiv_clm_apply hd (differentiableAt_const (Pi.single i 1))]
  simp

/-- Schwarz symmetry for the actual coordinate Hessian. -/
theorem coordinateHessian_isSymm {n : ℕ} {φ : (Fin n → ℝ) → ℝ}
    (hφ : ContDiff ℝ 2 φ) (x : Fin n → ℝ) : (coordinateHessian φ x).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, coordinateHessian_eq_fderiv_fderiv hφ]
  exact (hφ.contDiffAt.isSymmSndFDerivAt (by simp)) _ _

/-- The third coordinate derivative tensor appearing in the comparison
argument. -/
def coordinateThirdDerivative {n : ℕ} (φ : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) (i j k : Fin n) : ℝ :=
  coordinateDerivative k (fun y => coordinateHessian φ y i j) x

/-- The transposition symmetry needed by the tensor comparison is proved for
actual derivatives, rather than supplied as an independent tensor axiom. -/
theorem coordinateThirdDerivative_symm {n : ℕ} {φ : (Fin n → ℝ) → ℝ}
    (hφ : ContDiff ℝ 2 φ) (x : Fin n → ℝ) (i j k : Fin n) :
    coordinateThirdDerivative φ x i j k = coordinateThirdDerivative φ x j i k := by
  have heq : (fun y => coordinateHessian φ y i j) =
      (fun y => coordinateHessian φ y j i) := by
    funext y
    exact ((coordinateHessian_isSymm hφ y).apply i j).symm
  unfold coordinateThirdDerivative
  rw [heq]

/-- For a compactly supported smooth test function, all four integrability
conditions in A3 follow from continuity. -/
theorem weighted_integration_by_parts_compact_right {n : ℕ} (i : Fin n)
    {φ f g : (Fin n → ℝ) → ℝ} [IsFiniteMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 1 φ) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) :
    (∫ x, coordinateDerivative i f x * g x ∂potentialMeasure φ) =
      ∫ x, f x * (coordinateDerivative i φ x * g x - coordinateDerivative i g x)
        ∂potentialMeasure φ := by
  have hdf := (contDiff_coordinateDerivative hf (m := 0) (by norm_num) i).continuous
  have hdg := (contDiff_coordinateDerivative hg (m := 0) (by norm_num) i).continuous
  have hdφ := (contDiff_coordinateDerivative hφ (m := 0) (by norm_num) i).continuous
  have hdgc : HasCompactSupport (coordinateDerivative i g) :=
    hgc.fderiv_apply (𝕜 := ℝ) (Pi.single i 1)
  exact weighted_integration_by_parts i (hφ.differentiable le_rfl)
    (hf.differentiable le_rfl) (hg.differentiable le_rfl)
    ((hdf.mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left)
    ((hf.continuous.mul hdg).integrable_of_hasCompactSupport hdgc.mul_left)
    (((hf.continuous.mul hg.continuous).mul hdφ).integrable_of_hasCompactSupport hgc.mul_left.mul_right)
    ((hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left)

/-- The weighted coordinate divergence of an actual vector-field component. -/
def weightedCoordinateDivergence {n : ℕ} (φ F : (Fin n → ℝ) → ℝ) (i : Fin n)
    (x : Fin n → ℝ) : ℝ :=
  coordinateDerivative i F x - coordinateDerivative i φ x * F x

/-- The weak divergence identity for the exponential measure. This supplies
Green's formula from differentiation and compact support, rather than treating
symmetry of a diffusion as an axiom. -/
theorem integral_weightedCoordinateDivergence_mul {n : ℕ} (i : Fin n)
    {φ F g : (Fin n → ℝ) → ℝ} [IsFiniteMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 1 φ) (hF : ContDiff ℝ 1 F) (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) :
    (∫ x, weightedCoordinateDivergence φ F i x * g x ∂potentialMeasure φ) =
      -(∫ x, F x * coordinateDerivative i g x ∂potentialMeasure φ) := by
  have hDF := (contDiff_coordinateDerivative hF (m := 0) (by norm_num) i).continuous
  have hdg := (contDiff_coordinateDerivative hg (m := 0) (by norm_num) i).continuous
  have hdφ := (contDiff_coordinateDerivative hφ (m := 0) (by norm_num) i).continuous
  have hdgc : HasCompactSupport (coordinateDerivative i g) :=
    hgc.fderiv_apply (𝕜 := ℝ) (Pi.single i 1)
  have hA : Integrable (fun x => coordinateDerivative i F x * g x) (potentialMeasure φ) :=
    (hDF.mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left
  have hB : Integrable (fun x => coordinateDerivative i φ x * F x * g x) (potentialMeasure φ) :=
    ((hdφ.mul hF.continuous).mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left
  have hC : Integrable (fun x => F x * coordinateDerivative i g x) (potentialMeasure φ) :=
    (hF.continuous.mul hdg).integrable_of_hasCompactSupport hdgc.mul_left
  have h := weighted_integration_by_parts_compact_right i hφ hF hg hgc
  have heq : (fun x => F x * (coordinateDerivative i φ x * g x - coordinateDerivative i g x)) =
      (fun x => coordinateDerivative i φ x * F x * g x - F x * coordinateDerivative i g x) := by
    funext x
    ring
  rw [heq, integral_sub hB hC] at h
  have heq' : (fun x => weightedCoordinateDivergence φ F i x * g x) =
      (fun x => coordinateDerivative i F x * g x - coordinateDerivative i φ x * F x * g x) := by
    funext x
    dsimp [weightedCoordinateDivergence]
    ring
  rw [heq', integral_sub hA hB, h]
  ring

/-- The compact-flux form of A3. The test function need not be compact. -/
theorem weighted_integration_by_parts_compact_left {n : ℕ} (i : Fin n)
    {φ f g : (Fin n → ℝ) → ℝ} [IsFiniteMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 1 φ) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hfc : HasCompactSupport f) :
    (∫ x, coordinateDerivative i f x * g x ∂potentialMeasure φ) =
      ∫ x, f x * (coordinateDerivative i φ x * g x - coordinateDerivative i g x)
        ∂potentialMeasure φ := by
  have hdf := (contDiff_coordinateDerivative hf (m := 0) (by norm_num) i).continuous
  have hdg := (contDiff_coordinateDerivative hg (m := 0) (by norm_num) i).continuous
  have hdφ := (contDiff_coordinateDerivative hφ (m := 0) (by norm_num) i).continuous
  have hdfc : HasCompactSupport (coordinateDerivative i f) :=
    hfc.fderiv_apply (𝕜 := ℝ) (Pi.single i 1)
  exact weighted_integration_by_parts i (hφ.differentiable le_rfl)
    (hf.differentiable le_rfl) (hg.differentiable le_rfl)
    ((hdf.mul hg.continuous).integrable_of_hasCompactSupport hdfc.mul_right)
    ((hf.continuous.mul hdg).integrable_of_hasCompactSupport hfc.mul_right)
    (((hf.continuous.mul hg.continuous).mul hdφ).integrable_of_hasCompactSupport hfc.mul_right.mul_right)
    ((hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hfc.mul_right)

/-- Green's identity when the vector-field component, rather than the test
function, has compact support. -/
theorem integral_weightedCoordinateDivergence_mul_compact_left {n : ℕ} (i : Fin n)
    {φ F g : (Fin n → ℝ) → ℝ} [IsFiniteMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 1 φ) (hF : ContDiff ℝ 1 F) (hg : ContDiff ℝ 1 g)
    (hFc : HasCompactSupport F) :
    (∫ x, weightedCoordinateDivergence φ F i x * g x ∂potentialMeasure φ) =
      -(∫ x, F x * coordinateDerivative i g x ∂potentialMeasure φ) := by
  have hDF := (contDiff_coordinateDerivative hF (m := 0) (by norm_num) i).continuous
  have hdg := (contDiff_coordinateDerivative hg (m := 0) (by norm_num) i).continuous
  have hdφ := (contDiff_coordinateDerivative hφ (m := 0) (by norm_num) i).continuous
  have hDFc : HasCompactSupport (coordinateDerivative i F) :=
    hFc.fderiv_apply (𝕜 := ℝ) (Pi.single i 1)
  have hA : Integrable (fun x => coordinateDerivative i F x * g x) (potentialMeasure φ) :=
    (hDF.mul hg.continuous).integrable_of_hasCompactSupport hDFc.mul_right
  have hB : Integrable (fun x => coordinateDerivative i φ x * F x * g x) (potentialMeasure φ) :=
    ((hdφ.mul hF.continuous).mul hg.continuous).integrable_of_hasCompactSupport hFc.mul_left.mul_right
  have hC : Integrable (fun x => F x * coordinateDerivative i g x) (potentialMeasure φ) :=
    (hF.continuous.mul hdg).integrable_of_hasCompactSupport hFc.mul_right
  have h := weighted_integration_by_parts_compact_left i hφ hF hg hFc
  have heq : (fun x => F x * (coordinateDerivative i φ x * g x - coordinateDerivative i g x)) =
      (fun x => coordinateDerivative i φ x * F x * g x - F x * coordinateDerivative i g x) := by
    funext x
    ring
  rw [heq, integral_sub hB hC] at h
  have heq' : (fun x => weightedCoordinateDivergence φ F i x * g x) =
      (fun x => coordinateDerivative i F x * g x - coordinateDerivative i φ x * F x * g x) := by
    funext x
    dsimp [weightedCoordinateDivergence]
    ring
  rw [heq', integral_sub hA hB, h]
  ring

end GaussianTilt.Letwin
