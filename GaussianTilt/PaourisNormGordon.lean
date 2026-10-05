import GaussianTilt.PaourisCompactGordon

/-!
# Norm-form Gordon comparison

The coefficient processes are built from disjoint coordinate blocks of one
actual standard Gaussian vector. Their increment inequalities are proved by
Euclidean tensor-product identities.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators InnerProductSpace

namespace GaussianTilt.Paouris

variable {n q : ℕ}

def appendVector (x : Reference.Space n) (y : Reference.Space q) : Reference.Space (n + q) :=
  WithLp.toLp 2 (Fin.addCases (fun i ↦ x i) (fun j ↦ y j))

@[simp] lemma appendVector_castAdd (x : Reference.Space n) (y : Reference.Space q) (i : Fin n) :
    appendVector x y (Fin.castAdd q i) = x i := by simp [appendVector]

@[simp] lemma appendVector_natAdd (x : Reference.Space n) (y : Reference.Space q) (j : Fin q) :
    appendVector x y (Fin.natAdd n j) = y j := by simp [appendVector]

def vectorLeft (x : Reference.Space (n + q)) : Reference.Space n :=
  WithLp.toLp 2 (fun i ↦ x (Fin.castAdd q i))

def vectorRight (x : Reference.Space (n + q)) : Reference.Space q :=
  WithLp.toLp 2 (fun j ↦ x (Fin.natAdd n j))

lemma appendVector_sub (x x' : Reference.Space n) (y y' : Reference.Space q) :
    appendVector x y - appendVector x' y' = appendVector (x - x') (y - y') := by
  ext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;> simp

lemma appendVector_norm_sq (x : Reference.Space n) (y : Reference.Space q) :
    ‖appendVector x y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, Fin.sum_univ_add,
    appendVector_castAdd, appendVector_natAdd]

lemma appendVector_inner (x : Reference.Space n) (y : Reference.Space q)
    (w : Reference.Space (n + q)) :
    ⟪appendVector x y, w⟫_ℝ = ⟪x, vectorLeft w⟫_ℝ + ⟪y, vectorRight w⟫_ℝ := by
  simp only [PiLp.inner_apply, Fin.sum_univ_add, appendVector_castAdd, appendVector_natAdd,
    vectorLeft, vectorRight, PiLp.toLp_apply]

lemma appendVector_continuous :
    Continuous (fun z : Reference.Space n × Reference.Space q ↦ appendVector z.1 z.2) := by
  unfold appendVector
  apply (PiLp.continuous_toLp 2 (fun _ : Fin (n + q) ↦ ℝ)).comp
  apply continuous_pi
  intro i
  refine Fin.addCases ?_ ?_ i <;> intro j <;> simp only [Fin.addCases_left, Fin.addCases_right] <;> fun_prop

def tensorVector (x : Reference.Space n) (t : Reference.Space q) : Reference.Space (n * q) :=
  WithLp.toLp 2 (fun j ↦ x (finProdFinEquiv.symm j).1 * t (finProdFinEquiv.symm j).2)

@[simp] lemma tensorVector_apply (x : Reference.Space n) (t : Reference.Space q)
    (i : Fin n) (j : Fin q) : tensorVector x t (finProdFinEquiv (i, j)) = x i * t j := by
  simp only [tensorVector, PiLp.toLp_apply]
  rw [(finProdFinEquiv : Fin n × Fin q ≃ Fin (n * q)).symm_apply_apply]

lemma tensorVector_inner (x y : Reference.Space n) (t s : Reference.Space q) :
    ⟪tensorVector x t, tensorVector y s⟫_ℝ = ⟪x, y⟫_ℝ * ⟪t, s⟫_ℝ := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, RCLike.conj_to_real]
  rw [← Equiv.sum_comp finProdFinEquiv]
  simp only [Fintype.sum_prod_type, tensorVector_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma tensorVector_norm_sq (x : Reference.Space n) (t : Reference.Space q) :
    ‖tensorVector x t‖ ^ 2 = ‖x‖ ^ 2 * ‖t‖ ^ 2 := by
  have h := tensorVector_inner x x t t
  simpa only [real_inner_self_eq_norm_sq] using h

lemma tensorVector_continuous :
    Continuous (fun z : Reference.Space n × Reference.Space q ↦ tensorVector z.1 z.2) := by
  unfold tensorVector
  apply (PiLp.continuous_toLp 2 (fun _ : Fin (n * q) ↦ ℝ)).comp
  apply continuous_pi
  intro i
  fun_prop

/-- Coefficients of `⟪G,z⟫ + L⟪H,t⟫`, in the first two coordinate blocks. -/
def normGordonLeftCoeff (L : ℝ) (t : Reference.Space q) (z : Reference.Space n) :
    Reference.Space ((n + q) + n * q) := appendVector (appendVector z (L • t)) 0

/-- Coefficients of `⟪Γt,z⟫`, in the disjoint matrix-coordinate block. -/
def normGordonRightCoeff (t : Reference.Space q) (z : Reference.Space n) :
    Reference.Space ((n + q) + n * q) := appendVector 0 (tensorVector z t)

lemma normGordonLeft_increment (L : ℝ) (t s : Reference.Space q) (z w : Reference.Space n) :
    ‖normGordonLeftCoeff L t z - normGordonLeftCoeff L s w‖ ^ 2 =
      ‖z - w‖ ^ 2 + L ^ 2 * ‖t - s‖ ^ 2 := by
  rw [normGordonLeftCoeff, normGordonLeftCoeff, appendVector_sub, appendVector_norm_sq]
  rw [appendVector_sub, appendVector_norm_sq]
  simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, add_zero, ← smul_sub, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

lemma normGordonRight_increment (t s : Reference.Space q) (z w : Reference.Space n)
    (ht : ‖t‖ = 1) (hs : ‖s‖ = 1) :
    ‖normGordonRightCoeff t z - normGordonRightCoeff s w‖ ^ 2 =
      ‖z‖ ^ 2 + ‖w‖ ^ 2 - 2 * ⟪z, w⟫_ℝ * ⟪t, s⟫_ℝ := by
  rw [normGordonRightCoeff, normGordonRightCoeff, appendVector_sub, appendVector_norm_sq]
  simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add]
  rw [norm_sub_sq_real, tensorVector_norm_sq, tensorVector_norm_sq, tensorVector_inner, ht, hs]
  ring

lemma normGordon_same_row (L : ℝ) (t : Reference.Space q) (z w : Reference.Space n)
    (ht : ‖t‖ = 1) :
    ‖normGordonLeftCoeff L t z - normGordonLeftCoeff L t w‖ ^ 2 =
      ‖normGordonRightCoeff t z - normGordonRightCoeff t w‖ ^ 2 := by
  rw [normGordonLeft_increment, normGordonRight_increment t t z w ht ht,
    real_inner_self_eq_norm_sq, ht]
  simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    mul_zero, add_zero, one_pow, mul_one]
  nlinarith [norm_sub_sq_real z w]

lemma normGordon_cross_row (L : ℝ) (hL : 0 ≤ L)
    (t s : Reference.Space q) (z w : Reference.Space n)
    (ht : ‖t‖ = 1) (hs : ‖s‖ = 1) (hz : ‖z‖ ≤ L) (hw : ‖w‖ ≤ L) :
    ‖normGordonRightCoeff t z - normGordonRightCoeff s w‖ ^ 2 ≤
      ‖normGordonLeftCoeff L t z - normGordonLeftCoeff L s w‖ ^ 2 := by
  rw [normGordonLeft_increment, normGordonRight_increment t s z w ht hs,
    norm_sub_sq_real z w, norm_sub_sq_real t s, ht, hs]
  have hts : ⟪t, s⟫_ℝ ≤ 1 := by
    simpa only [ht, hs, mul_one] using real_inner_le_norm t s
  have hzw : ⟪z, w⟫_ℝ ≤ L ^ 2 := by
    have h := (real_inner_le_norm z w).trans
      (mul_le_mul hz hw (norm_nonneg _) hL)
    simpa only [pow_two] using h
  have hprod := mul_nonneg (sub_nonneg.mpr hts) (sub_nonneg.mpr hzw)
  nlinarith

lemma appendVector_left_right (w : Reference.Space (n + q)) :
    appendVector (vectorLeft w) (vectorRight w) = w := by
  ext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [vectorLeft, vectorRight]

lemma vectorLeft_norm_le (w : Reference.Space (n + q)) : ‖vectorLeft w‖ ≤ ‖w‖ := by
  have h := appendVector_norm_sq (vectorLeft w) (vectorRight w)
  rw [appendVector_left_right] at h
  nlinarith [norm_nonneg (vectorLeft w), norm_nonneg w, sq_nonneg ‖vectorRight w‖]

lemma vectorRight_norm_le (w : Reference.Space (n + q)) : ‖vectorRight w‖ ≤ ‖w‖ := by
  have h := appendVector_norm_sq (vectorLeft w) (vectorRight w)
  rw [appendVector_left_right] at h
  nlinarith [norm_nonneg (vectorRight w), norm_nonneg w, sq_nonneg ‖vectorLeft w‖]

lemma vectorLeft_continuous : Continuous (vectorLeft (n := n) (q := q)) := by
  unfold vectorLeft
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i ↦ by fun_prop)

lemma vectorRight_continuous : Continuous (vectorRight (n := n) (q := q)) := by
  unfold vectorRight
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i ↦ by fun_prop)

/-- The Gaussian vector, auxiliary vector, and matrix-entry coordinate blocks. -/
def normGordonG (w : Reference.Space ((n + q) + n * q)) : Reference.Space n :=
  vectorLeft (vectorLeft (n := n + q) (q := n * q) w)

def normGordonH (w : Reference.Space ((n + q) + n * q)) : Reference.Space q :=
  vectorRight (vectorLeft (n := n + q) (q := n * q) w)

def normGordonMatrix (w : Reference.Space ((n + q) + n * q)) : Reference.Space (n * q) :=
  vectorRight w

/-- Matrix action of the explicitly indexed Gaussian matrix block. -/
def gaussianMatrixAction (W : Reference.Space (n * q)) (t : Reference.Space q) : Reference.Space n :=
  WithLp.toLp 2 (fun i ↦ ∑ j : Fin q, W (finProdFinEquiv (i, j)) * t j)

lemma tensorVector_inner_matrixAction (z : Reference.Space n) (t : Reference.Space q)
    (W : Reference.Space (n * q)) :
    ⟪tensorVector z t, W⟫_ℝ = ⟪z, gaussianMatrixAction W t⟫_ℝ := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, RCLike.conj_to_real]
  rw [← Equiv.sum_comp finProdFinEquiv]
  simp only [Fintype.sum_prod_type, tensorVector_apply, gaussianMatrixAction,
    PiLp.toLp_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma normGordonLeft_inner (L : ℝ) (t : Reference.Space q) (z : Reference.Space n)
    (w : Reference.Space ((n + q) + n * q)) :
    ⟪normGordonLeftCoeff L t z, w⟫_ℝ = ⟪z, normGordonG w⟫_ℝ + L * ⟪t, normGordonH w⟫_ℝ := by
  simp only [normGordonLeftCoeff, appendVector_inner, inner_zero_left, add_zero,
    real_inner_smul_left, normGordonG, normGordonH]

lemma normGordonRight_inner (t : Reference.Space q) (z : Reference.Space n)
    (w : Reference.Space ((n + q) + n * q)) :
    ⟪normGordonRightCoeff t z, w⟫_ℝ = ⟪z, gaussianMatrixAction (normGordonMatrix w) t⟫_ℝ := by
  simp only [normGordonRightCoeff, appendVector_inner, inner_zero_left, zero_add,
    tensorVector_inner_matrixAction, normGordonMatrix]

/-- The compact Euclidean unit sphere indexing the Gaussian matrix minimum. -/
abbrev UnitSphere (q : ℕ) := Metric.sphere (0 : Reference.Space q) 1

instance unitSphere_compactSpace (q : ℕ) : CompactSpace (UnitSphere q) :=
  isCompact_iff_compactSpace.mp (isCompact_sphere (0 : Reference.Space q) 1)

instance unitSphere_nonempty_instance (q : ℕ) [NeZero q] : Nonempty (UnitSphere q) :=
  (unitSphere_nonempty (NeZero.pos q)).to_subtype

lemma unitSphere_norm (t : UnitSphere q) : ‖(t : Reference.Space q)‖ = 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using t.property

lemma exists_unitSphere_inner_eq_neg_norm [NeZero q] (h : Reference.Space q) :
    ∃ t : UnitSphere q, ⟪(t : Reference.Space q), h⟫_ℝ = -‖h‖ := by
  by_cases hh : h = 0
  · refine ⟨Classical.arbitrary _, ?_⟩
    simp [hh]
  · have hn := norm_pos_iff.mpr hh
    let t : Reference.Space q := -(‖h‖⁻¹ • h)
    have ht : t ∈ UnitSphere q := by
      simp only [UnitSphere, Metric.mem_sphere, dist_zero_right, t, norm_neg]
      exact norm_smul_inv_norm (𝕜 := ℝ) hh
    refine ⟨⟨t, ht⟩, ?_⟩
    change ⟪-(‖h‖⁻¹ • h), h⟫_ℝ = -‖h‖
    rw [inner_neg_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp

lemma unitSphere_inf_affine_inner [NeZero q] (a L : ℝ) (hL : 0 ≤ L)
    (h : Reference.Space q) :
    (⨅ t : UnitSphere q, a + L * ⟪(t : Reference.Space q), h⟫_ℝ) = a - L * ‖h‖ := by
  have hbound (t : UnitSphere q) : a - L * ‖h‖ ≤ a + L * ⟪(t : Reference.Space q), h⟫_ℝ := by
    have hi := (abs_le.mp (abs_real_inner_le_norm (t : Reference.Space q) h)).1
    rw [unitSphere_norm, one_mul] at hi
    have hm := mul_le_mul_of_nonneg_left hi hL
    nlinarith
  apply le_antisymm
  · obtain ⟨t, ht⟩ := exists_unitSphere_inner_eq_neg_norm h
    have hbd : BddBelow (range fun t : UnitSphere q ↦ a + L * ⟪(t : Reference.Space q), h⟫_ℝ) :=
      ⟨a - L * ‖h‖, by rintro _ ⟨t, rfl⟩; exact hbound t⟩
    exact (ciInf_le hbd t).trans_eq (by rw [ht]; ring)
  · exact le_ciInf hbound

/-- Support function of a bounded family of dual vectors. -/
def supportWidth {V : Type*} (z : V → Reference.Space n) (x : Reference.Space n) : ℝ :=
  ⨆ v : V, ⟪z v, x⟫_ℝ

lemma supportWidth_lipschitz {V : Type*} [Nonempty V] (z : V → Reference.Space n)
    {L : ℝ≥0} (hL : ∀ v, ‖z v‖ ≤ L) : LipschitzWith L (supportWidth z) := by
  have h := processMinMax_lipschitz (fun _ : Unit ↦ z) (fun _ v ↦ hL v)
  have heq : processMinMax (fun _ : Unit ↦ z) = supportWidth z := by
    funext x
    exact ciInf_const
  rw [heq] at h
  exact h

lemma normGordonLeft_processMinMax {V : Type*} [Nonempty V] [NeZero q]
    (z : V → Reference.Space n) {L : ℝ} (hL : 0 ≤ L) (hbound : ∀ v, ‖z v‖ ≤ L)
    (w : Reference.Space ((n + q) + n * q)) :
    processMinMax (fun t : UnitSphere q ↦ fun v ↦ normGordonLeftCoeff L t (z v)) w =
      supportWidth z (normGordonG w) - L * ‖normGordonH w‖ := by
  unfold processMinMax
  simp_rw [normGordonLeft_inner]
  have hb := process_row_bddAbove (fun _ : Unit ↦ z) (fun _ v ↦ hbound v) (normGordonG w) ()
  simp_rw [← ciSup_add hb]
  exact unitSphere_inf_affine_inner _ _ hL _

lemma normGordonRight_processMinMax {V : Type*} [Nonempty V]
    (z : V → Reference.Space n) (w : Reference.Space ((n + q) + n * q)) :
    processMinMax (fun t : UnitSphere q ↦ fun v ↦ normGordonRightCoeff t (z v)) w =
      ⨅ t : UnitSphere q, supportWidth z (gaussianMatrixAction (normGordonMatrix w) t) := by
  simp only [processMinMax, normGordonRight_inner, supportWidth]

/-- Gordon's support-function inequality with explicit Gaussian coordinate
blocks. These are the exact Gaussian-vector/matrix processes in the short
Paouris proof, rather than an assumed minimax estimate. -/
theorem supportWidth_gordon [NeZero q] {V : Type*} [PseudoMetricSpace V]
    [CompactSpace V] [Nonempty V] (z : V → Reference.Space n) (hz : Continuous z)
    {L : ℝ≥0} (hbound : ∀ v, ‖z v‖ ≤ L) :
    (∫ w : Reference.Space ((n + q) + n * q), supportWidth z (normGordonG (n := n) (q := q) w) ∂standardGaussian ((n + q) + n * q)) ≤
      (∫ w : Reference.Space ((n + q) + n * q), ⨅ t : UnitSphere q, supportWidth z
        (gaussianMatrixAction (n := n) (q := q) (normGordonMatrix (n := n) (q := q) w) t) ∂standardGaussian ((n + q) + n * q)) +
      (L : ℝ) * ∫ w : Reference.Space ((n + q) + n * q), ‖normGordonH (n := n) (q := q) w‖ ∂standardGaussian ((n + q) + n * q) := by
  let a : UnitSphere q → V → Reference.Space ((n + q) + n * q) :=
    fun t v ↦ normGordonLeftCoeff L t (z v)
  let b : UnitSphere q → V → Reference.Space ((n + q) + n * q) :=
    fun t v ↦ normGordonRightCoeff t (z v)
  have htcont : Continuous (fun p : UnitSphere q × V ↦ (p.1 : Reference.Space q)) :=
    continuous_subtype_val.comp continuous_fst
  have hzcont : Continuous (fun p : UnitSphere q × V ↦ z p.2) := hz.comp continuous_snd
  have hac : Continuous (Function.uncurry a) :=
    appendVector_continuous.comp ((appendVector_continuous.comp
      (hzcont.prodMk (continuous_const.smul htcont))).prodMk continuous_const)
  have hbc : Continuous (Function.uncurry b) :=
    appendVector_continuous.comp (continuous_const.prodMk
      (tensorVector_continuous.comp (hzcont.prodMk htcont)))
  have hsep : ∀ l : Fin ((n + q) + n * q), (∀ t v, a t v l = 0) ∨ (∀ t v, b t v l = 0) := by
    intro l
    refine Fin.addCases ?_ ?_ l
    · intro i
      right
      intro t v
      simp [b, normGordonRightCoeff]
    · intro i
      left
      intro t v
      simp [a, normGordonLeftCoeff]
  have hwithin : ∀ (t : UnitSphere q) (v v' : V),
      ‖a t v - a t v'‖ ^ 2 ≤ ‖b t v - b t v'‖ ^ 2 := by
    intro t v v'
    exact (normGordon_same_row (n := n) (q := q) (L : ℝ) (t : Reference.Space q)
      (z v) (z v') (unitSphere_norm t)).le
  have hcross : ∀ (t t' : UnitSphere q), t ≠ t' → ∀ (v v' : V),
      ‖b t v - b t' v'‖ ^ 2 ≤ ‖a t v - a t' v'‖ ^ 2 := by
    intro t t' _ v v'
    exact normGordon_cross_row (n := n) (q := q) (L : ℝ) L.coe_nonneg
      (t : Reference.Space q) (t' : Reference.Space q) (z v) (z v')
      (unitSphere_norm t) (unitSphere_norm t') (hbound v) (hbound v')
  have hcomp := compact_gordon_comparison (U := UnitSphere q) (V := V)
    (d := (n + q) + n * q) a b hac hbc hsep hwithin hcross
  have hgc : Continuous (normGordonG (n := n) (q := q)) :=
    vectorLeft_continuous.comp vectorLeft_continuous
  have hhc : Continuous (normGordonH (n := n) (q := q)) :=
    vectorRight_continuous.comp vectorLeft_continuous
  have hgn (w : Reference.Space ((n + q) + n * q)) : ‖normGordonG w‖ ≤ ‖w‖ :=
    (vectorLeft_norm_le _).trans (vectorLeft_norm_le _)
  have hhn (w : Reference.Space ((n + q) + n * q)) : ‖normGordonH w‖ ≤ ‖w‖ :=
    (vectorRight_norm_le _).trans (vectorLeft_norm_le _)
  have hiH : Integrable (fun w : Reference.Space ((n + q) + n * q) ↦ ‖normGordonH w‖)
      (standardGaussian ((n + q) + n * q)) := by
    apply (standardGaussian_norm_integrable _).mono' hhc.norm.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun w ↦ by simpa only [norm_norm] using hhn w
  have hiG : Integrable (fun w : Reference.Space ((n + q) + n * q) ↦ supportWidth z (normGordonG w))
      (standardGaussian ((n + q) + n * q)) := by
    apply ((standardGaussian_norm_integrable _).const_mul L).mono'
      ((supportWidth_lipschitz z hbound).continuous.comp hgc).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro w
    rw [Real.norm_eq_abs]
    have hw : |supportWidth z (normGordonG w)| ≤ (L : ℝ) * ‖normGordonG w‖ :=
      abs_le.mpr (process_row_bounds (fun _ : Unit ↦ z) (fun _ v ↦ hbound v) (normGordonG w) ())
    exact hw.trans (mul_le_mul_of_nonneg_left (hgn w) L.coe_nonneg)
  change (∫ w, processMinMax (fun t : UnitSphere q ↦ fun v ↦ normGordonLeftCoeff L t (z v)) w
      ∂standardGaussian ((n + q) + n * q)) ≤
    ∫ w, processMinMax (fun t : UnitSphere q ↦ fun v ↦ normGordonRightCoeff t (z v)) w
      ∂standardGaussian ((n + q) + n * q) at hcomp
  simp_rw [normGordonLeft_processMinMax z L.coe_nonneg hbound,
    normGordonRight_processMinMax] at hcomp
  rw [integral_sub hiG (hiH.const_mul L), integral_const_mul] at hcomp
  linarith

/-- The closed dual unit ball of a real homogeneous norm, represented in the
original Euclidean space via the Riesz pairing. -/
def normPolar (p : AddGroupNorm (Reference.Space n)) : Set (Reference.Space n) :=
  {z | ∀ x, ⟪z, x⟫_ℝ ≤ p x}

lemma normPolar_closed (p : AddGroupNorm (Reference.Space n)) : IsClosed (normPolar p) := by
  have heq : normPolar p = ⋂ x : Reference.Space n, {z | ⟪z, x⟫_ℝ ≤ p x} := by
    ext z
    simp only [normPolar, mem_setOf_eq, mem_iInter]
  rw [heq]
  exact isClosed_iInter fun x ↦ isClosed_le (continuous_id.inner continuous_const) continuous_const

lemma normPolar_nonempty (p : AddGroupNorm (Reference.Space n)) : (normPolar p).Nonempty :=
  ⟨0, by intro x; simpa only [inner_zero_left] using apply_nonneg p x⟩

lemma normPolar_norm_le (p : AddGroupNorm (Reference.Space n)) {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ x, p x ≤ L * ‖x‖) {z : Reference.Space n} (hz : z ∈ normPolar p) : ‖z‖ ≤ L := by
  have h := (hz z).trans (hbound z)
  rw [real_inner_self_eq_norm_sq] at h
  by_cases hn : ‖z‖ = 0
  · simpa only [hn] using hL
  · have hpos := lt_of_le_of_ne (norm_nonneg z) (Ne.symm hn)
    nlinarith

lemma normPolar_compact (p : AddGroupNorm (Reference.Space n)) {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ x, p x ≤ L * ‖x‖) : IsCompact (normPolar p) := by
  apply (isCompact_closedBall (0 : Reference.Space n) L).of_isClosed_subset (normPolar_closed p)
  intro z hz
  simpa only [Metric.mem_closedBall, dist_zero_right] using normPolar_norm_le p hL hbound hz

/-- Attainment of the polar support functional, proved by Hahn–Banach. -/
lemma normPolar_support_attained (p : AddGroupNorm (Reference.Space n))
    (hp : ∀ (a : ℝ) x, p (a • x) = |a| * p x)
    {L : ℝ} (hbound : ∀ x, p x ≤ L * ‖x‖) (x : Reference.Space n) :
    ∃ z ∈ normPolar p, ⟪z, x⟫_ℝ = p x := by
  by_cases hx : x = 0
  · exact ⟨0, (by intro y; simpa only [inner_zero_left] using apply_nonneg p y), by simp [hx]⟩
  · let u : Reference.Space n := ‖x‖⁻¹ • x
    have hu : ‖u‖ = 1 := norm_smul_inv_norm (𝕜 := ℝ) hx
    obtain ⟨l, hlu, hlbound⟩ := supporting_linearMap p hp u hu
    have hlin (y : Reference.Space n) : ‖l y‖ ≤ L * ‖y‖ := (hlbound y).trans (hbound y)
    let lc := l.mkContinuous L hlin
    let z : Reference.Space n := (InnerProductSpace.toDual ℝ (Reference.Space n)).symm lc
    have hz (y : Reference.Space n) : ⟪z, y⟫_ℝ = l y := InnerProductSpace.toDual_symm_apply
    refine ⟨z, fun y ↦ (hz y).le.trans ((le_abs_self _).trans (hlbound y)), ?_⟩
    rw [hz]
    have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    change l (‖x‖⁻¹ • x) = p (‖x‖⁻¹ • x) at hlu
    rw [map_smul, smul_eq_mul, hp, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))] at hlu
    exact mul_left_cancel₀ (inv_ne_zero hnorm) hlu

lemma normPolar_support_eq (p : AddGroupNorm (Reference.Space n))
    (hp : ∀ (a : ℝ) x, p (a • x) = |a| * p x)
    {L : ℝ} (hbound : ∀ x, p x ≤ L * ‖x‖) (x : Reference.Space n) :
    (⨆ z : normPolar p, ⟪(z : Reference.Space n), x⟫_ℝ) = p x := by
  letI : Nonempty (normPolar p) := (normPolar_nonempty p).to_subtype
  apply le_antisymm (ciSup_le fun z ↦ z.property x)
  obtain ⟨z, hz, heq⟩ := normPolar_support_attained p hp hbound x
  have hbd : BddAbove (range fun z : normPolar p ↦ ⟪(z : Reference.Space n), x⟫_ℝ) :=
    ⟨p x, by rintro _ ⟨z, rfl⟩; exact z.property x⟩
  exact heq.symm.le.trans (le_ciSup hbd ⟨z, hz⟩)

/-- The genuine norm form of Gordon's minimax inequality used in the short
Paouris proof. Gaussian vector and matrix blocks are explicitly realized
inside a single standard Gaussian law, with no assumed minimax estimate. -/
theorem norm_gordon [NeZero q] (p : AddGroupNorm (Reference.Space n))
    (hp : ∀ (a : ℝ) x, p (a • x) = |a| * p x)
    {L : ℝ≥0} (hbound : ∀ x, p x ≤ (L : ℝ) * ‖x‖) :
    (∫ w, p (normGordonG (q := q) w) ∂standardGaussian ((n + q) + n * q)) ≤
      (∫ w, ⨅ t : UnitSphere q, p (gaussianMatrixAction (normGordonMatrix w) t)
        ∂standardGaussian ((n + q) + n * q)) +
      (L : ℝ) * ∫ w : Reference.Space ((n + q) + n * q), ‖normGordonH (n := n) (q := q) w‖ ∂standardGaussian ((n + q) + n * q) := by
  letI : CompactSpace (normPolar p) := isCompact_iff_compactSpace.mp (normPolar_compact p L.coe_nonneg hbound)
  letI : Nonempty (normPolar p) := (normPolar_nonempty p).to_subtype
  have h := supportWidth_gordon (q := q) (fun z : normPolar p ↦ (z : Reference.Space n))
    continuous_subtype_val (L := L) (fun z ↦ normPolar_norm_le p L.coe_nonneg hbound z.property)
  have heq (x : Reference.Space n) : supportWidth (fun z : normPolar p ↦ (z : Reference.Space n)) x = p x :=
    normPolar_support_eq p hp hbound x
  simpa only [heq] using h

end GaussianTilt.Paouris
