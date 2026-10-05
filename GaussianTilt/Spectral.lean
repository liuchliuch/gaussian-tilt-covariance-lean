import Mathlib
import GaussianTilt.Calculus
import GaussianTilt.NormTrace

/-!
# Finite spectral profiles and convex comparison

Deterministic lemmas used in Section 3.2.  The hypotheses concerning partial
sums are not claims that projected Paouris bounds have been proved.
-/

open scoped BigOperators
open Finset

namespace GaussianTilt

/-- The supporting-line calculation used to compare the Rényi expression
with endpoint relative entropy. -/
theorem convex_renyi_comparison {φ : ℝ → ℝ} {T r : ℝ}
    (hT : 0 < T) (hr : 1 < r) (hφ : ConvexOn ℝ Set.univ φ)
    (hd : DifferentiableAt ℝ φ T) :
    (φ T - r * φ (T / r)) / (r - 1) ≤ T * deriv φ T - φ T := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hs : T / r < T := (div_lt_self hT hr)
  have hsl := hφ.slope_le_deriv (Set.mem_univ _) (Set.mem_univ _) hs hd
  rw [slope_def_field] at hsl
  have hline := (div_le_iff₀ (sub_pos.mpr hs)).mp hsl
  apply (div_le_iff₀ (sub_pos.mpr hr)).mpr
  have hmul := mul_le_mul_of_nonneg_left hline hr0.le
  have hcancel : r * (T / r) = T := mul_div_cancel₀ T (ne_of_gt hr0)
  nlinarith [congrArg (fun z => z * deriv φ T) hcancel]

/-- Lemma 3.4: the Rényi divergence of the earlier genuine Gaussian tilt
from the base law is bounded by the endpoint's genuine relative entropy. -/
theorem gaussianTilt_renyi_le_entropy {n : ℕ} (P : CompactProbability n)
    {T r : ℝ} (hT : 0 < T) (hr : 1 < r) :
    P.renyi r (T / r) 0 ≤ P.entropy T := by
  have hr0 : r ≠ 0 := ne_of_gt (lt_trans zero_lt_one hr)
  rw [P.renyi_eq, P.entropy_eq_logPartition]
  simp only [sub_zero, zero_add, P.logPartition_zero, mul_zero, add_zero,
    mul_div_cancel₀ T hr0]
  exact convex_renyi_comparison hT hr P.convex_logPartition
    (P.hasDerivAt_logPartition T).differentiableAt

/-- The conjugate Hölder order used in the paper is always greater than one. -/
theorem conjugateOrder_gt_one {q : ℝ} (hq : 1 < q) : 1 < q / (q - 1) := by
  apply (lt_div_iff₀ (sub_pos.mpr hq)).mpr
  linarith

/-- Equivalent nearby-time form, with the paper's `T (1 - 1/q)` parameter. -/
theorem gaussianTilt_nearby_renyi_le_entropy {n : ℕ} (P : CompactProbability n)
    {T q : ℝ} (hT : 0 < T) (hq : 1 < q) :
    P.renyi (q / (q - 1)) (T * (1 - 1 / q)) 0 ≤ P.entropy T := by
  have hq0 : q ≠ 0 := ne_of_gt (lt_trans zero_lt_one hq)
  have hqm : q - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hq)
  have ht : T * (1 - 1 / q) = T / (q / (q - 1)) := by field_simp
  rw [ht]
  exact gaussianTilt_renyi_le_entropy P hT (conjugateOrder_gt_one hq)

open MeasureTheory in
/-- Compact support controls every finite density moment, including negative
precisions. No projected-moment inequality is assumed. -/
theorem density_memLp {n : ℕ} (P : CompactProbability n) (s : ℝ) (p : ENNReal) :
    MemLp (P.density s) p P.measure := by
  apply MemLp.of_bound (P.continuous_density s).aestronglyMeasurable
    (Real.exp (|s| * P.bound) / P.partition s)
  filter_upwards [P.ae_energy_le] with x hx
  rw [Real.norm_eq_abs, abs_of_pos (P.density_pos s x)]
  exact div_le_div_of_nonneg_right (P.weight_le s hx) (P.partition_pos s).le

open MeasureTheory in
/-- An exact ordinary-integral formula for the density moment. -/
theorem density_rpow_integral {n : ℕ} (P : CompactProbability n) (r s : ℝ) :
    (∫ x, P.density s x ^ r ∂P.measure) =
      Real.exp (P.logPartition (r * s) - r * P.logPartition s) := by
  have h := P.renyi_integral r s 0
  simp only [P.tilt_zero, sub_zero, zero_add, P.logPartition_zero,
    mul_zero, add_zero] at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards [P.rnDeriv_tilt_base s] with x hx
  rw [hx]

open MeasureTheory in
/-- The density Hölder cost is bounded by endpoint relative entropy. -/
theorem density_Lp_le_exp_entropy {n : ℕ} (P : CompactProbability n)
    {T q : ℝ} (hT : 0 < T) (hq : 1 < q) :
    (∫ x, P.density (T / (q / (q - 1))) x ^ (q / (q - 1)) ∂P.measure) ^
      (1 / (q / (q - 1))) ≤ Real.exp (P.entropy T / q) := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hqm : q - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hq)
  have hr0 : q / (q - 1) ≠ 0 := div_ne_zero hq0.ne' hqm
  rw [density_rpow_integral, ← Real.exp_mul, mul_div_cancel₀ T hr0]
  have heq :
      (P.logPartition T - q / (q - 1) * P.logPartition (T / (q / (q - 1)))) *
        (1 / (q / (q - 1))) =
      P.renyi (q / (q - 1)) (T / (q / (q - 1))) 0 / q := by
    rw [P.renyi_eq]
    simp only [sub_zero, zero_add, P.logPartition_zero, mul_zero, add_zero,
      mul_div_cancel₀ T hr0]
    field_simp
    ring
  rw [heq]
  apply Real.exp_le_exp.mpr
  exact div_le_div_of_nonneg_right
    (gaussianTilt_renyi_le_entropy P hT (conjugateOrder_gt_one hq)) hq0.le

open MeasureTheory in
/-- The genuine change-of-measure/Hölder step in Lemma 3.5. The only
premise on the observable is its natural nonnegativity and `L^q` membership;
there is no assumed bound on its tilted expectation. -/
theorem expectation_le_exp_entropy_mul_moment {n : ℕ} (P : CompactProbability n)
    {T q : ℝ} (hT : 0 < T) (hq : 1 < q) {f : Point n → ℝ}
    (hf0 : 0 ≤ᵐ[P.measure] f) (hf : MemLp f (ENNReal.ofReal q) P.measure) :
    P.expectation (T / (q / (q - 1))) f ≤
      Real.exp (P.entropy T / q) * (∫ x, f x ^ q ∂P.measure) ^ (1 / q) := by
  have hpq : (q / (q - 1)).HolderConjugate q :=
    (Real.HolderConjugate.conjExponent hq).symm
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Filter.Eventually.of_forall fun x => (P.density_pos (T / (q / (q - 1))) x).le)
    hf0 (density_memLp P _ _) hf
  have heq : (∫ x, P.density (T / (q / (q - 1))) x * f x ∂P.measure) =
      P.expectation (T / (q / (q - 1))) f := by
    unfold CompactProbability.density CompactProbability.expectation CompactProbability.weightedIntegral
    simp_rw [div_mul_eq_mul_div]
    rw [integral_div]
  rw [heq] at hh
  refine hh.trans (mul_le_mul_of_nonneg_right (density_Lp_le_exp_entropy P hT hq) ?_)
  exact Real.rpow_nonneg (integral_nonneg_of_ae
    (hf0.mono fun x hx => Real.rpow_nonneg hx q)) _

/-- A telescoping bound on the finite reciprocal-square series. -/
theorem sum_reciprocal_sq_le (n : ℕ) :
    (∑ i ∈ range n, (1 : ℝ) / ((i : ℝ) + 1) ^ 2) ≤
      2 - 2 / ((n : ℝ) + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [sum_range_succ]
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hp : 0 < (n : ℝ) + 1 := by positivity
    have hp' : 0 < (n : ℝ) + 2 := by positivity
    have hterm : (1 : ℝ) / ((n : ℝ) + 1) ^ 2 ≤
        2 / ((n : ℝ) + 1) - 2 / ((n : ℝ) + 2) := by
      field_simp
      nlinarith
    push_cast
    have hid : (n : ℝ) + 1 + 1 = (n : ℝ) + 2 := by ring
    rw [hid]
    linarith

/-- A universal upper bound, independent of the number of eigenvalues. -/
theorem sum_reciprocal_sq_le_two (n : ℕ) :
    (∑ i ∈ range n, (1 : ℝ) / ((i : ℝ) + 1) ^ 2) ≤ 2 := by
  have h := sum_reciprocal_sq_le n
  have hn : 0 ≤ 2 / ((n : ℝ) + 1) := by positivity
  linarith

/-- An ordered eigenvalue is bounded by the average of the preceding
partial sum. Indices are zero-based. -/
theorem profile_of_partial_sums {a : ℕ → ℝ} {n : ℕ} {C q : ℝ}
    (hordered : ∀ i j, i ≤ j → j < n → a j ≤ a i)
    (hpartial : ∀ k, 1 ≤ k → k ≤ n →
      (∑ i ∈ range k, a i) ≤ C * ((k : ℝ) + q ^ 2))
    {j : ℕ} (hj : j < n) :
    a j ≤ C * (1 + q ^ 2 / ((j : ℝ) + 1)) := by
  have hjp : 0 < (j : ℝ) + 1 := by positivity
  have hsum : ((j : ℝ) + 1) * a j ≤ ∑ i ∈ range (j + 1), a i := by
    calc
      ((j : ℝ) + 1) * a j = ∑ _i ∈ range (j + 1), a j := by simp
      _ ≤ ∑ i ∈ range (j + 1), a i := by
        exact sum_le_sum fun i hi => hordered i j (by have := mem_range.mp hi; omega) hj
  have hbound := hpartial (j + 1) (by omega) (by omega)
  have havg : a j ≤ C * (((j : ℝ) + 1) + q ^ 2) / ((j : ℝ) + 1) := by
    apply (le_div_iff₀ hjp).mpr
    push_cast at hbound
    nlinarith
  convert havg using 1 <;> field_simp

/-- Squaring and summing the spectral profile recovers the
Hilbert--Schmidt scale with an explicit constant. -/
theorem sum_sq_le_of_profile {a : ℕ → ℝ} {n : ℕ} {C q : ℝ}
    (hC : 0 ≤ C) (ha : ∀ i < n, 0 ≤ a i)
    (hprofile : ∀ i < n, a i ≤ C * (1 + q ^ 2 / ((i : ℝ) + 1))) :
    (∑ i ∈ range n, a i ^ 2) ≤ 4 * C ^ 2 * ((n : ℝ) + q ^ 4) := by
  have hpoint : ∀ i < n, a i ^ 2 ≤
      2 * C ^ 2 * (1 + q ^ 4 / ((i : ℝ) + 1) ^ 2) := by
    intro i hi
    have hb : 0 ≤ C * (1 + q ^ 2 / ((i : ℝ) + 1)) := by positivity
    have hs := pow_le_pow_left₀ (ha i hi) (hprofile i hi) 2
    have haux := sq_nonneg (1 - q ^ 2 / ((i : ℝ) + 1))
    have hid : (q ^ 2 / ((i : ℝ) + 1)) ^ 2 = q ^ 4 / ((i : ℝ) + 1) ^ 2 := by
      rw [div_pow]; ring
    have hmul := mul_nonneg (sq_nonneg C) haux
    rw [← hid]
    nlinarith
  have hsum := sum_le_sum (fun i hi => hpoint i (mem_range.mp hi))
  have heq : (∑ i ∈ range n, 2 * C ^ 2 *
      (1 + q ^ 4 / ((i : ℝ) + 1) ^ 2)) =
      2 * C ^ 2 * ((n : ℝ) + q ^ 4 *
        ∑ i ∈ range n, (1 : ℝ) / ((i : ℝ) + 1) ^ 2) := by
    simp only [div_eq_mul_inv, one_mul, mul_add, sum_add_distrib, ← mul_sum,
      sum_const, card_range, nsmul_eq_mul]
    ring
  rw [heq] at hsum
  have hr := sum_reciprocal_sq_le_two n
  have hmul := mul_le_mul_of_nonneg_left hr (show 0 ≤ q ^ 4 by positivity)
  have hmul' := mul_le_mul_of_nonneg_left hmul (show 0 ≤ 2 * C ^ 2 by positivity)
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith [mul_nonneg (sq_nonneg C) hn]

end GaussianTilt

namespace GaussianTilt

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The orthogonal projection onto a selected subset of an orthonormal
matrix eigenbasis. -/
def eigenProjection {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (s : Finset ι) :
    Matrix ι ι ℝ :=
  (hA.eigenvectorUnitary : Matrix ι ι ℝ) *
    Matrix.diagonal (fun i => if i ∈ s then 1 else 0) *
      star (hA.eigenvectorUnitary : Matrix ι ι ℝ)

lemma eigenProjection_isHermitian {A : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (s : Finset ι) : (eigenProjection hA s).IsHermitian := by
  exact ((Matrix.PosSemidef.diagonal (fun i => by split_ifs <;> norm_num)).mul_mul_conjTranspose_same
    (hA.eigenvectorUnitary : Matrix ι ι ℝ)).isHermitian

lemma eigenProjection_idempotent {A : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (s : Finset ι) :
    eigenProjection hA s * eigenProjection hA s = eigenProjection hA s := by
  let U : Matrix ι ι ℝ := hA.eigenvectorUnitary
  let D : Matrix ι ι ℝ := diagonal (fun i => if i ∈ s then 1 else 0)
  have hU : star U * U = 1 := unitary.coe_star_mul_self _
  have hD : D * D = D := by
    rw [diagonal_mul_diagonal]
    congr 1
    ext i
    simp [D]
  change (U * D * star U) * (U * D * star U) = U * D * star U
  calc
    _ = U * D * (star U * U) * D * star U := by noncomm_ring
    _ = U * D * star U := by rw [hU, mul_one, Matrix.mul_assoc U D D, hD]

lemma eigenProjection_rank {A : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (s : Finset ι) : (eigenProjection hA s).rank = s.card := by
  unfold eigenProjection
  rw [← unitary.coe_star,
    Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.UnitaryGroup.det_isUnit _),
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ (Matrix.UnitaryGroup.det_isUnit _),
    Matrix.rank_diagonal]
  simp

lemma trace_eigenProjection_mul {A : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (s : Finset ι) :
    Matrix.trace (eigenProjection hA s * A) = ∑ i ∈ s, hA.eigenvalues i := by
  let U : Matrix ι ι ℝ := hA.eigenvectorUnitary
  let D : Matrix ι ι ℝ := diagonal (fun i => if i ∈ s then 1 else 0)
  have hd : star U * A * U = diagonal hA.eigenvalues := by
    simpa only [Function.comp_apply] using hA.star_mul_self_mul_eq_diagonal
  change Matrix.trace ((U * D * star U) * A) = _
  calc
    _ = Matrix.trace ((U * D) * (star U * A)) := by congr 1; noncomm_ring
    _ = Matrix.trace ((star U * A) * (U * D)) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((star U * A * U) * D) := by congr 1; noncomm_ring
    _ = ∑ i ∈ s, hA.eigenvalues i := by
      rw [hd]
      simp [D, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]

/-- Every spectral subset satisfies the genuine projection bound. The premise
quantifies over all actual symmetric idempotent matrices and their matrix ranks. -/
theorem eigenvalue_sum_le_of_projected_trace {A : Matrix ι ι ℝ}
    (hA : A.IsHermitian) {C q : ℝ}
    (hproj : ∀ P : Matrix ι ι ℝ, P.IsHermitian → P * P = P →
      Matrix.trace (P * A) ≤ C * ((P.rank : ℝ) + q ^ 2))
    (s : Finset ι) :
    (∑ i ∈ s, hA.eigenvalues i) ≤ C * ((s.card : ℝ) + q ^ 2) := by
  have h := hproj (eigenProjection hA s) (eigenProjection_isHermitian hA s)
    (eigenProjection_idempotent hA s)
  simpa only [trace_eigenProjection_mul, eigenProjection_rank] using h

/-- Projected trace control transfers to subsets of the canonically sorted
real eigenvalues. -/
theorem sorted_eigenvalue_sum_le_of_projected_trace {A : Matrix ι ι ℝ}
    (hA : A.IsHermitian) {C q : ℝ}
    (hproj : ∀ P : Matrix ι ι ℝ, P.IsHermitian → P * P = P →
      Matrix.trace (P * A) ≤ C * ((P.rank : ℝ) + q ^ 2))
    (s : Finset (Fin (Fintype.card ι))) :
    (∑ i ∈ s, hA.eigenvalues₀ i) ≤ C * ((s.card : ℝ) + q ^ 2) := by
  let e : Fin (Fintype.card ι) ≃ ι := Fintype.equivOfCardEq (Fintype.card_fin _)
  have h := eigenvalue_sum_le_of_projected_trace hA hproj (s.map e.toEmbedding)
  simpa [Matrix.IsHermitian.eigenvalues, e] using h

/-- The full spectral profile for an actual Hermitian matrix, proved by
constructing its leading eigenspace projections. Index zero corresponds to
the largest eigenvalue. -/
theorem matrix_spectral_profile_of_projected_trace {A : Matrix ι ι ℝ}
    (hA : A.IsHermitian) {C q : ℝ}
    (hproj : ∀ P : Matrix ι ι ℝ, P.IsHermitian → P * P = P →
      Matrix.trace (P * A) ≤ C * ((P.rank : ℝ) + q ^ 2))
    (j : Fin (Fintype.card ι)) :
    hA.eigenvalues₀ j ≤ C * (1 + q ^ 2 / ((j.val : ℝ) + 1)) := by
  have hp : 0 < (j.val : ℝ) + 1 := by positivity
  have hsum : ((j.val : ℝ) + 1) * hA.eigenvalues₀ j ≤
      ∑ i ∈ Finset.Iic j, hA.eigenvalues₀ i := by
    calc
      _ = ∑ _i ∈ Finset.Iic j, hA.eigenvalues₀ j := by simp
      _ ≤ _ := Finset.sum_le_sum fun i hi => hA.eigenvalues₀_antitone (Finset.mem_Iic.mp hi)
  have hbound := sorted_eigenvalue_sum_le_of_projected_trace hA hproj (Finset.Iic j)
  simp only [Fin.card_Iic, Nat.cast_add, Nat.cast_one] at hbound
  have havg : hA.eigenvalues₀ j ≤ C * (((j.val : ℝ) + 1) + q ^ 2) / ((j.val : ℝ) + 1) := by
    apply (le_div_iff₀ hp).mpr
    nlinarith
  convert havg using 1 <;> field_simp

/-- The operator-norm consequence of actual rank-one projected trace bounds. -/
theorem matrix_opNorm_le_of_projected_trace {A : Matrix ι ι ℝ}
    (hA : A.PosSemidef) {C q : ℝ} (hC : 0 ≤ C)
    (hproj : ∀ P : Matrix ι ι ℝ, P.IsHermitian → P * P = P →
      Matrix.trace (P * A) ≤ C * ((P.rank : ℝ) + q ^ 2)) :
    ‖A‖ ≤ C * (1 + q ^ 2) := by
  have hspec := hA.isHermitian.spectral_theorem
  calc
    ‖A‖ = ‖Matrix.diagonal (RCLike.ofReal ∘ hA.isHermitian.eigenvalues)‖ := by
      conv_lhs => rw [hspec]
      rw [CStarRing.norm_mul_mem_unitary _ (unitary.star_mem _),
        CStarRing.norm_coe_unitary_mul]
      exact hA.isHermitian.eigenvectorUnitary.prop
    _ ≤ C * (1 + q ^ 2) := by
      apply diagonal_opNorm_le (by positivity)
      intro i
      change |hA.isHermitian.eigenvalues i| ≤ _
      rw [abs_of_nonneg (hA.eigenvalues_nonneg i)]
      simpa using eigenvalue_sum_le_of_projected_trace hA.isHermitian hproj {i}

/-- Trace of the square is the squared Euclidean Hilbert--Schmidt norm. -/
theorem trace_square_eq_sum_eigenvalues_sq {A : Matrix ι ι ℝ}
    (hA : A.IsHermitian) : Matrix.trace (A ^ 2) = ∑ i, hA.eigenvalues i ^ 2 := by
  let U : Matrix ι ι ℝ := hA.eigenvectorUnitary
  let D : Matrix ι ι ℝ := diagonal hA.eigenvalues
  have hU : star U * U = 1 := unitary.coe_star_mul_self _
  have hspec : A = U * D * star U := hA.spectral_theorem
  conv_lhs => rw [hspec, pow_two]
  calc
    Matrix.trace ((U * D * star U) * (U * D * star U)) =
        Matrix.trace (U * (D * (star U * U) * D) * star U) := by congr 1; noncomm_ring
    _ = Matrix.trace (U * (D * D) * star U) := by rw [hU, mul_one]
    _ = Matrix.trace (star U * U * (D * D)) := Matrix.trace_mul_cycle _ _ _
    _ = ∑ i, hA.eigenvalues i ^ 2 := by
      rw [hU, one_mul]
      simp [D, diagonal_mul_diagonal, trace_diagonal, pow_two]

/-- Sorted and unsorted spectral descriptions agree also for the square trace. -/
theorem trace_square_eq_sum_sorted_eigenvalues_sq {A : Matrix ι ι ℝ}
    (hA : A.IsHermitian) : Matrix.trace (A ^ 2) = ∑ i, hA.eigenvalues₀ i ^ 2 := by
  rw [trace_square_eq_sum_eigenvalues_sq hA]
  simp only [Matrix.IsHermitian.eigenvalues]
  exact Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
    (fun i => hA.eigenvalues₀ i ^ 2)

/-- The squared Hilbert--Schmidt estimate for an actual positive semidefinite
matrix. All leading eigenspace projections and their ranks are proved above. -/
theorem matrix_trace_square_le_of_projected_trace {A : Matrix ι ι ℝ}
    (hA : A.PosSemidef) {C q : ℝ} (hC : 0 ≤ C)
    (hproj : ∀ P : Matrix ι ι ℝ, P.IsHermitian → P * P = P →
      Matrix.trace (P * A) ≤ C * ((P.rank : ℝ) + q ^ 2)) :
    Matrix.trace (A ^ 2) ≤ 4 * C ^ 2 * ((Fintype.card ι : ℝ) + q ^ 4) := by
  let a : ℕ → ℝ := fun i => if hi : i < Fintype.card ι then
    hA.isHermitian.eigenvalues₀ ⟨i, hi⟩ else 0
  let e : Fin (Fintype.card ι) ≃ ι := Fintype.equivOfCardEq (Fintype.card_fin _)
  have ha (i : ℕ) (hi : i < Fintype.card ι) : 0 ≤ a i := by
    simpa [a, hi, Matrix.IsHermitian.eigenvalues, e] using
      hA.eigenvalues_nonneg (e ⟨i, hi⟩)
  have hprofile (i : ℕ) (hi : i < Fintype.card ι) :
      a i ≤ C * (1 + q ^ 2 / ((i : ℝ) + 1)) := by
    simpa [a, hi] using matrix_spectral_profile_of_projected_trace hA.isHermitian hproj ⟨i, hi⟩
  have hsum := sum_sq_le_of_profile hC ha hprofile
  rw [trace_square_eq_sum_sorted_eigenvalues_sq hA.isHermitian,
    Finset.sum_fin_eq_sum_range]
  convert hsum using 1
  apply Finset.sum_congr rfl
  intro i hi
  simp [a, Finset.mem_range.mp hi]

/-- Corollary 3.6's Hilbert--Schmidt consequence with an explicit constant.
This includes the zero-dimensional case. -/
theorem matrix_hilbertSchmidt_le_of_projected_trace {A : Matrix ι ι ℝ}
    (hA : A.PosSemidef) {C q : ℝ} (hC : 0 ≤ C)
    (hproj : ∀ P : Matrix ι ι ℝ, P.IsHermitian → P * P = P →
      Matrix.trace (P * A) ≤ C * ((P.rank : ℝ) + q ^ 2)) :
    Real.sqrt (Matrix.trace (A ^ 2)) ≤
      2 * C * Real.sqrt ((Fintype.card ι : ℝ) + q ^ 4) := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · have h := matrix_trace_square_le_of_projected_trace hA hC hproj
    have hs := Real.sq_sqrt (show 0 ≤ (Fintype.card ι : ℝ) + q ^ 4 by positivity)
    nlinarith

end
end GaussianTilt
