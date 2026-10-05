import GaussianTilt.CompactIteratedMarginal
import GaussianTilt.UnboundedBrascampLieb
import GaussianTilt.Reference.PaperStatements

/-! # Euclidean transport of the actual product-space covariance inequality -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace GaussianTilt.EuclideanBrascampLieb
open IteratedMarginal LogConcaveMarginal

/-- Split off the last coordinate, as a genuine linear equivalence. -/
def splitLast (n : ℕ) : (Fin (n + 1) → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) × ℝ where
  toEquiv := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) (Fin.last n)).toEquiv.trans (Equiv.prodComm _ _)
  map_add' := by intro x y; rfl
  map_smul' := by intro c x; rfl

lemma splitLast_apply (n : ℕ) (x : Fin (n + 1) → ℝ) :
    splitLast n x = ((fun i ↦ x i.castSucc), x (Fin.last n)) := by
  ext i <;> simp [splitLast, MeasurableEquiv.piFinSuccAbove] <;> rfl

lemma splitLast_measurePreserving (n : ℕ) : MeasurePreserving (splitLast n) := by
  exact (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
    (ν := (volume : Measure (Fin n → ℝ)))).comp
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) (Fin.last n))

def flatten : (n : ℕ) → Space n ≃ₗ[ℝ] (Fin (n + 1) → ℝ)
  | 0 => (LinearEquiv.funUnique (Fin 1) ℝ ℝ).symm
  | n + 1 => ((flatten n).prodCongr (LinearEquiv.refl ℝ ℝ)).trans (splitLast (n + 1)).symm

lemma flatten_measurePreserving : ∀ n : ℕ, MeasurePreserving (flatten n)
  | 0 => (volume_preserving_funUnique (Fin 1) ℝ).symm
  | n + 1 => by
    have hs : MeasurePreserving ((splitLast (n + 1)).symm) :=
      MeasurePreserving.symm ((splitLast (n + 1)).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv)
        (splitLast_measurePreserving (n + 1))
    exact hs.comp ((flatten_measurePreserving n).prod (MeasurePreserving.id volume))

lemma splitLast_symm_castSucc (n : ℕ) (p : (Fin n → ℝ) × ℝ) (i : Fin n) :
    (splitLast n).symm p i.castSucc = p.1 i := by
  have h := (splitLast n).apply_symm_apply p
  rw [splitLast_apply] at h
  exact congrFun (congrArg Prod.fst h) i

lemma splitLast_symm_last (n : ℕ) (p : (Fin n → ℝ) × ℝ) :
    (splitLast n).symm p (Fin.last n) = p.2 := by
  have h := (splitLast n).apply_symm_apply p
  rw [splitLast_apply] at h
  exact congrArg Prod.snd h

lemma flatten_succ_castSucc (n : ℕ) (p : Space (n + 1)) (i : Fin (n + 1)) :
    flatten (n + 1) p i.castSucc = flatten n p.1 i :=
  splitLast_symm_castSucc (n + 1) (flatten n p.1, p.2) i

lemma flatten_succ_last (n : ℕ) (p : Space (n + 1)) :
    flatten (n + 1) p (Fin.last (n + 1)) = p.2 :=
  splitLast_symm_last (n + 1) (flatten n p.1, p.2)

lemma flatten_coordinate : ∀ (n : ℕ) (p : Space n), flatten n p 0 = coordinate p
  | 0, p => rfl
  | n + 1, p => by
    rw [show (0 : Fin (n + 2)) = (0 : Fin (n + 1)).castSucc by rfl,
      flatten_succ_castSucc, flatten_coordinate]
    rfl

lemma flatten_energy : ∀ (n : ℕ) (p : Space n),
    (∑ i : Fin (n + 1), (flatten n p i) ^ 2) = energy p
  | 0, p => by simp [flatten, energy, LinearEquiv.funUnique]
  | n + 1, p => by
    rw [Fin.sum_univ_castSucc, flatten_succ_last]
    simp_rw [flatten_succ_castSucc]
    rw [flatten_energy]
    rfl

lemma norm_sq_le_energy : ∀ (n : ℕ) (p : Space n), ‖p‖ ^ 2 ≤ energy p
  | 0, p => by simp [energy, Real.norm_eq_abs, sq_abs]
  | n + 1, p => by
    have h := norm_sq_le_energy n p.1
    change max ‖p.1‖ ‖p.2‖ ^ 2 ≤ energy p.1 + p.2 ^ 2
    rcases le_total ‖p.1‖ ‖p.2‖ with hle | hle
    · rw [max_eq_right hle, Real.norm_eq_abs, sq_abs]
      nlinarith [sq_nonneg ‖p.1‖]
    · rw [max_eq_left hle]
      nlinarith [sq_nonneg p.2]

def toEuclidean (n : ℕ) : Space n ≃L[ℝ] Reference.Space (n + 1) :=
  (flatten n).toContinuousLinearEquiv.trans (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm

lemma toEuclidean_measurePreserving (n : ℕ) : MeasurePreserving (toEuclidean n) :=
  (PiLp.volume_preserving_toLp (Fin (n + 1))).comp (flatten_measurePreserving n)

lemma toEuclidean_coordinate (n : ℕ) (p : Space n) : toEuclidean n p 0 = coordinate p :=
  flatten_coordinate n p

lemma toEuclidean_energy (n : ℕ) (p : Space n) : ‖toEuclidean n p‖ ^ 2 = energy p := by
  rw [EuclideanSpace.norm_sq_eq]
  simpa only [Real.norm_eq_abs, sq_abs] using flatten_energy n p

lemma norm_le_toEuclidean (n : ℕ) (p : Space n) : ‖p‖ ≤ ‖toEuclidean n p‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [toEuclidean_energy]
  exact norm_sq_le_energy n p

lemma integral_coordinate_transport (n k : ℕ) (f : Reference.Space (n + 1) → ℝ) :
    (∫ p : Space n, coordinate p ^ k * f (toEuclidean n p)) =
      ∫ x : Reference.Space (n + 1), x 0 ^ k * f x := by
  have h := (toEuclidean_measurePreserving n).integral_comp
    (toEuclidean n).toHomeomorph.measurableEmbedding
    (fun x : Reference.Space (n + 1) ↦ x 0 ^ k * f x)
  simpa only [toEuclidean_coordinate] using h

/-- Compact nonsmooth strongly logconcave density: the first coordinate bound
in the paper's Euclidean space, with exact normalized Lebesgue integrals. -/
theorem compact_coordinate_variance_le_inv {n : ℕ} {f : Reference.Space (n + 1) → ℝ}
    {κ R : ℝ} (hκ : 0 < κ) (hf : IsStronglyLogConcave (fun x ↦ ‖x‖ ^ 2) κ f)
    (hm : Measurable f) (hs : ∀ x, R < ‖x‖ → f x = 0)
    (hZ : 0 < ∫ x, f x) :
    (∫ x, (x 0) ^ 2 * f x) / (∫ x, f x) -
      ((∫ x, x 0 * f x) / (∫ x, f x)) ^ 2 ≤ κ⁻¹ := by
  let g : Space n → ℝ := fun p ↦ f (toEuclidean n p)
  have hg : IsStronglyLogConcave energy κ g := by
    constructor
    · intro p
      simpa only [g, toEuclidean_energy] using hf.1 (toEuclidean n p)
    · intro p q α β hα hβ hαβ
      have h := hf.2 (toEuclidean n p) (toEuclidean n q) α β hα hβ hαβ
      simpa only [g, ← map_smul, ← map_add, toEuclidean_energy] using h
  have hgm : Measurable g := hm.comp (toEuclidean n).continuous.measurable
  have hgs (p : Space n) (hp : R < ‖p‖) : g p = 0 := hs _ (hp.trans_le (norm_le_toEuclidean n p))
  have h0 := integral_coordinate_transport n 0 f
  have h1 := integral_coordinate_transport n 1 f
  have h2 := integral_coordinate_transport n 2 f
  simp only [pow_zero, one_mul] at h0
  simp only [pow_one] at h1
  have hZg : 0 < ∫ p, g p := by rw [show (∫ p, g p) = ∫ x, f x from h0]; exact hZ
  have h := compact_product_coordinate_variance_le_inv hκ hg hgm hgs hZg
  simpa only [g, h0, h1, h2] using h

lemma strong_comp_isometry {n : ℕ} {f : Reference.Space n → ℝ} {κ : ℝ}
    (hf : IsStronglyLogConcave (fun x ↦ ‖x‖ ^ 2) κ f)
    (e : Reference.Space n ≃ₗᵢ[ℝ] Reference.Space n) :
    IsStronglyLogConcave (fun x ↦ ‖x‖ ^ 2) κ (fun x ↦ f (e x)) := by
  constructor
  · intro x; simpa only [e.norm_map] using hf.1 (e x)
  · intro x y α β hα hβ hαβ
    have h := hf.2 (e x) (e y) α β hα hβ hαβ
    simpa only [← map_smul, ← map_add, e.norm_map] using h

lemma basis_zero_inner {n : ℕ} (x : Reference.Space (n + 1)) :
    inner ℝ (EuclideanSpace.single 0 (1 : ℝ)) x = x 0 := by
  simp [EuclideanSpace.inner_eq_star_dotProduct]

/-- The same actual density bound holds in every Euclidean unit direction. -/
theorem compact_unit_variance_le_inv {n : ℕ} {f : Reference.Space (n + 1) → ℝ}
    {κ R : ℝ} (hκ : 0 < κ) (hf : IsStronglyLogConcave (fun x ↦ ‖x‖ ^ 2) κ f)
    (hm : Measurable f) (hs : ∀ x, R < ‖x‖ → f x = 0) (hZ : 0 < ∫ x, f x)
    (u : Reference.Space (n + 1)) (hu : ‖u‖ = 1) :
    (∫ x, (inner ℝ u x) ^ 2 * f x) / (∫ x, f x) -
      ((∫ x, inner ℝ u x * f x) / (∫ x, f x)) ^ 2 ≤ κ⁻¹ := by
  let v : Reference.Space (n + 1) := EuclideanSpace.single 0 1
  let e := (Submodule.span ℝ {v - u})ᗮ.reflection
  have hv : ‖v‖ = 1 := by simp [v]
  have he : e v = u := Submodule.reflection_sub (hv.trans hu.symm)
  have hi (x : Reference.Space (n + 1)) : inner ℝ u (e x) = x 0 := by
    have h := e.inner_map_map v x
    rw [he] at h
    exact h.trans (basis_zero_inner x)
  have h0 := e.measurePreserving.integral_comp e.toHomeomorph.measurableEmbedding f
  have h1 := e.measurePreserving.integral_comp e.toHomeomorph.measurableEmbedding
    (fun x ↦ inner ℝ u x * f x)
  have h2 := e.measurePreserving.integral_comp e.toHomeomorph.measurableEmbedding
    (fun x ↦ (inner ℝ u x) ^ 2 * f x)
  simp only [hi] at h1 h2
  have h := compact_coordinate_variance_le_inv hκ (strong_comp_isometry hf e)
    (hm.comp e.continuous.measurable) (fun x hx ↦ hs (e x) (by simpa only [e.norm_map] using hx))
    (by rw [h0]; exact hZ)
  simpa only [h0, h1, h2] using h

/-- Directional variance of the normalized actual Lebesgue density. -/
def densityDirectionalVariance {n : ℕ} (f : Reference.Space n → ℝ)
    (u : Reference.Space n) : ℝ :=
  (∫ x, (inner ℝ u x) ^ 2 * f x) / (∫ x, f x) -
    ((∫ x, inner ℝ u x * f x) / (∫ x, f x)) ^ 2

lemma densityDirectionalVariance_smul {n : ℕ} (f : Reference.Space n → ℝ)
    (c : ℝ) (u : Reference.Space n) :
    densityDirectionalVariance f (c • u) = c ^ 2 * densityDirectionalVariance f u := by
  simp only [densityDirectionalVariance, real_inner_smul_left, mul_pow, mul_assoc,
    integral_const_mul]
  ring

/-- Compact nonsmooth Brascamp--Lieb for every actual Euclidean direction,
including zero-dimensional and zero-direction cases. -/
theorem compact_directional_variance_le_inv {n : ℕ} {f : Reference.Space n → ℝ}
    {κ R : ℝ} (hκ : 0 < κ) (hf : IsStronglyLogConcave (fun x ↦ ‖x‖ ^ 2) κ f)
    (hm : Measurable f) (hs : ∀ x, R < ‖x‖ → f x = 0) (hZ : 0 < ∫ x, f x)
    (u : Reference.Space n) : densityDirectionalVariance f u ≤ κ⁻¹ * ‖u‖ ^ 2 := by
  by_cases hu : u = 0
  · subst u
    simp [densityDirectionalVariance]
  cases n with
  | zero => exact (hu (Subsingleton.elim _ _)).elim
  | succ n =>
    let v : Reference.Space (n + 1) := ‖u‖⁻¹ • u
    have hv : ‖v‖ = 1 := norm_smul_inv_norm (𝕜 := ℝ) hu
    have huv : u = ‖u‖ • v := by
      dsimp [v]
      rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hu), one_smul]
    have h := compact_unit_variance_le_inv hκ hf hm hs hZ v hv
    change densityDirectionalVariance f v ≤ κ⁻¹ at h
    have hmul := mul_le_mul_of_nonneg_left h (sq_nonneg ‖u‖)
    rw [← densityDirectionalVariance_smul, ← huv] at hmul
    simpa only [mul_comm] using hmul

/-! Unbounded-support versions: the exhaustion theorem supplies all needed moments. -/
theorem coordinate_variance_le_inv_of_integrable {n : ℕ} {f : Reference.Space (n + 1) → ℝ}
    {κ : ℝ} (hκ : 0 < κ) (hf : IsStronglyLogConcave (fun x ↦ ‖x‖ ^ 2) κ f)
    (hm : Measurable f) (hint : Integrable f)
    (hZ : 0 < ∫ x, f x) :
    (∫ x, (x 0) ^ 2 * f x) / (∫ x, f x) -
      ((∫ x, x 0 * f x) / (∫ x, f x)) ^ 2 ≤ κ⁻¹ := by
  let g : Space n → ℝ := fun p ↦ f (toEuclidean n p)
  have hg : IsStronglyLogConcave energy κ g := by
    constructor
    · intro p
      simpa only [g, toEuclidean_energy] using hf.1 (toEuclidean n p)
    · intro p q α β hα hβ hαβ
      have h := hf.2 (toEuclidean n p) (toEuclidean n q) α β hα hβ hαβ
      simpa only [g, ← map_smul, ← map_add, toEuclidean_energy] using h
  have hgm : Measurable g := hm.comp (toEuclidean n).continuous.measurable
  have hgi : Integrable g := (toEuclidean_measurePreserving n).integrable_comp hint.aestronglyMeasurable |>.mpr hint
  have h0 := integral_coordinate_transport n 0 f
  have h1 := integral_coordinate_transport n 1 f
  have h2 := integral_coordinate_transport n 2 f
  simp only [pow_zero, one_mul] at h0
  simp only [pow_one] at h1
  have hZg : 0 < ∫ p, g p := by rw [show (∫ p, g p) = ∫ x, f x from h0]; exact hZ
  have h := (coordinate_variance_le_inv_of_integrable_density hκ hg hgm hgi hZg).2.2
  simpa only [g, h0, h1, h2] using h

theorem unit_variance_le_inv_of_integrable {n : ℕ} {f : Reference.Space (n + 1) → ℝ}
    {κ : ℝ} (hκ : 0 < κ) (hf : IsStronglyLogConcave (fun x ↦ ‖x‖ ^ 2) κ f)
    (hm : Measurable f) (hint : Integrable f) (hZ : 0 < ∫ x, f x)
    (u : Reference.Space (n + 1)) (hu : ‖u‖ = 1) :
    (∫ x, (inner ℝ u x) ^ 2 * f x) / (∫ x, f x) -
      ((∫ x, inner ℝ u x * f x) / (∫ x, f x)) ^ 2 ≤ κ⁻¹ := by
  let v : Reference.Space (n + 1) := EuclideanSpace.single 0 1
  let e := (Submodule.span ℝ {v - u})ᗮ.reflection
  have hv : ‖v‖ = 1 := by simp [v]
  have he : e v = u := Submodule.reflection_sub (hv.trans hu.symm)
  have hi (x : Reference.Space (n + 1)) : inner ℝ u (e x) = x 0 := by
    have h := e.inner_map_map v x
    rw [he] at h
    exact h.trans (basis_zero_inner x)
  have h0 := e.measurePreserving.integral_comp e.toHomeomorph.measurableEmbedding f
  have h1 := e.measurePreserving.integral_comp e.toHomeomorph.measurableEmbedding
    (fun x ↦ inner ℝ u x * f x)
  have h2 := e.measurePreserving.integral_comp e.toHomeomorph.measurableEmbedding
    (fun x ↦ (inner ℝ u x) ^ 2 * f x)
  simp only [hi] at h1 h2
  have h := coordinate_variance_le_inv_of_integrable hκ (strong_comp_isometry hf e)
    (hm.comp e.continuous.measurable) (e.measurePreserving.integrable_comp hint.aestronglyMeasurable |>.mpr hint)
    (by rw [h0]; exact hZ)
  simpa only [h0, h1, h2] using h

theorem directional_variance_le_inv_of_integrable {n : ℕ} {f : Reference.Space n → ℝ}
    {κ : ℝ} (hκ : 0 < κ) (hf : IsStronglyLogConcave (fun x ↦ ‖x‖ ^ 2) κ f)
    (hm : Measurable f) (hint : Integrable f) (hZ : 0 < ∫ x, f x)
    (u : Reference.Space n) : densityDirectionalVariance f u ≤ κ⁻¹ * ‖u‖ ^ 2 := by
  by_cases hu : u = 0
  · subst u
    simp [densityDirectionalVariance]
  cases n with
  | zero => exact (hu (Subsingleton.elim _ _)).elim
  | succ n =>
    let v : Reference.Space (n + 1) := ‖u‖⁻¹ • u
    have hv : ‖v‖ = 1 := norm_smul_inv_norm (𝕜 := ℝ) hu
    have huv : u = ‖u‖ • v := by
      dsimp [v]
      rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hu), one_smul]
    have h := unit_variance_le_inv_of_integrable hκ hf hm hint hZ v hv
    change densityDirectionalVariance f v ≤ κ⁻¹ at h
    have hmul := mul_le_mul_of_nonneg_left h (sq_nonneg ‖u‖)
    rw [← densityDirectionalVariance_smul, ← huv] at hmul
    simpa only [mul_comm] using hmul


theorem coordinate_moments_integrable {n : ℕ} {f : Reference.Space (n + 1) → ℝ}
    {κ : ℝ} (hκ : 0 < κ) (hf : IsStronglyLogConcave (fun x ↦ ‖x‖ ^ 2) κ f)
    (hm : Measurable f) (hint : Integrable f) (hZ : 0 < ∫ x, f x) :
    Integrable (fun x ↦ x 0 * f x) ∧ Integrable (fun x ↦ (x 0) ^ 2 * f x) := by
  let g : Space n → ℝ := fun p ↦ f (toEuclidean n p)
  have hg : IsStronglyLogConcave energy κ g := by
    constructor
    · intro p
      simpa only [g, toEuclidean_energy] using hf.1 (toEuclidean n p)
    · intro p q α β hα hβ hαβ
      have h := hf.2 (toEuclidean n p) (toEuclidean n q) α β hα hβ hαβ
      simpa only [g, ← map_smul, ← map_add, toEuclidean_energy] using h
  have hgm : Measurable g := hm.comp (toEuclidean n).continuous.measurable
  have hgi : Integrable g := (toEuclidean_measurePreserving n).integrable_comp hint.aestronglyMeasurable |>.mpr hint
  have h0 := integral_coordinate_transport n 0 f
  simp only [pow_zero, one_mul] at h0
  have hZg : 0 < ∫ p, g p := by rw [show (∫ p, g p) = ∫ x, f x from h0]; exact hZ
  obtain ⟨h1, h2, _⟩ := coordinate_variance_le_inv_of_integrable_density hκ hg hgm hgi hZg
  constructor
  · apply ((toEuclidean_measurePreserving n).integrable_comp
      (((EuclideanSpace.proj (0 : Fin (n + 1))).continuous.measurable.mul hm).aestronglyMeasurable)).mp
    change Integrable (fun p : Space n ↦ (toEuclidean n p) 0 * f (toEuclidean n p))
    simpa only [toEuclidean_coordinate, g] using h1
  · apply ((toEuclidean_measurePreserving n).integrable_comp
      ((((EuclideanSpace.proj (0 : Fin (n + 1))).continuous.measurable.pow_const 2).mul hm).aestronglyMeasurable)).mp
    change Integrable (fun p : Space n ↦ (toEuclidean n p) 0 ^ 2 * f (toEuclidean n p))
    simpa only [toEuclidean_coordinate, g] using h2

theorem unit_directional_moments_integrable {n : ℕ} {f : Reference.Space (n + 1) → ℝ}
    {κ : ℝ} (hκ : 0 < κ) (hf : IsStronglyLogConcave (fun x ↦ ‖x‖ ^ 2) κ f)
    (hm : Measurable f) (hint : Integrable f) (hZ : 0 < ∫ x, f x)
    (u : Reference.Space (n + 1)) (hu : ‖u‖ = 1) :
    Integrable (fun x ↦ inner ℝ u x * f x) ∧ Integrable (fun x ↦ (inner ℝ u x) ^ 2 * f x) := by
  let v : Reference.Space (n + 1) := EuclideanSpace.single 0 1
  let e := (Submodule.span ℝ {v - u})ᗮ.reflection
  have hv : ‖v‖ = 1 := by simp [v]
  have he : e v = u := Submodule.reflection_sub (hv.trans hu.symm)
  have hi (x : Reference.Space (n + 1)) : inner ℝ u (e x) = x 0 := by
    have h := e.inner_map_map v x
    rw [he] at h
    exact h.trans (basis_zero_inner x)
  have h0 := e.measurePreserving.integral_comp e.toHomeomorph.measurableEmbedding f
  obtain ⟨h1, h2⟩ := coordinate_moments_integrable hκ (strong_comp_isometry hf e)
    (hm.comp e.continuous.measurable) (e.measurePreserving.integrable_comp hint.aestronglyMeasurable |>.mpr hint)
    (by rw [h0]; exact hZ)
  constructor
  · apply (e.measurePreserving.integrable_comp
      ((show Measurable (fun x ↦ inner ℝ u x) from by fun_prop).mul hm).aestronglyMeasurable).mp
    simpa only [Function.comp_def, hi] using h1
  · apply (e.measurePreserving.integrable_comp
      ((show Measurable (fun x ↦ (inner ℝ u x) ^ 2) from by fun_prop).mul hm).aestronglyMeasurable).mp
    simpa only [Function.comp_def, hi] using h2

/-- Actual first and second directional moments are finite in every dimension;
no moment hypothesis is hidden in the nonsmooth covariance estimate. -/
theorem directional_moments_integrable {n : ℕ} {f : Reference.Space n → ℝ}
    {κ : ℝ} (hκ : 0 < κ) (hf : IsStronglyLogConcave (fun x ↦ ‖x‖ ^ 2) κ f)
    (hm : Measurable f) (hint : Integrable f) (hZ : 0 < ∫ x, f x)
    (u : Reference.Space n) :
    Integrable (fun x ↦ inner ℝ u x * f x) ∧ Integrable (fun x ↦ (inner ℝ u x) ^ 2 * f x) := by
  by_cases hu : u = 0
  · subst u; simp
  cases n with
  | zero => exact (hu (Subsingleton.elim _ _)).elim
  | succ n =>
    let v : Reference.Space (n + 1) := ‖u‖⁻¹ • u
    have hv : ‖v‖ = 1 := norm_smul_inv_norm (𝕜 := ℝ) hu
    have huv : u = ‖u‖ • v := by
      dsimp [v]
      rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hu), one_smul]
    obtain ⟨h1, h2⟩ := unit_directional_moments_integrable hκ hf hm hint hZ v hv
    have hinner (x : Reference.Space (n + 1)) : inner ℝ u x = ‖u‖ * inner ℝ v x := by
      conv_lhs => rw [huv, real_inner_smul_left]
    constructor
    · have h := h1.const_mul ‖u‖
      simpa only [hinner, mul_assoc] using h
    · have h := h2.const_mul (‖u‖ ^ 2)
      simpa only [hinner, mul_pow, mul_assoc] using h

end GaussianTilt.EuclideanBrascampLieb
