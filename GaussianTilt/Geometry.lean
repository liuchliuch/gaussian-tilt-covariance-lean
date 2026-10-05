import Mathlib

/-!
# The explicit raw body of Section 4

The space is written as transverse coordinates times one axial coordinate.
The norm-square is the Euclidean coordinate sum, independently of the default
product norm used to put a topology on this finite-dimensional space.
-/

noncomputable section
open Set Filter
open scoped BigOperators Topology

namespace GaussianTilt

abbrev RawPoint (d : ℕ) := (Fin d → ℝ) × ℝ

def transverseEnergy {d : ℕ} (p : RawPoint d) : ℝ := ∑ i, (p.1 i) ^ 2

def rawBodyWith (d : ℕ) (Δ : ℝ) : Set (RawPoint d) :=
  {p | (∀ i, |p.1 i| ≤ Real.sqrt 3) ∧
    transverseEnergy p + 2 * Δ * |p.2| ≤ (d : ℝ) - 2 * Δ}

def deviationScale (d : ℕ) : ℝ := (d : ℝ) ^ (3 / 5 : ℝ)

def rawBody (d : ℕ) : Set (RawPoint d) := rawBodyWith d (deviationScale d)

@[simp] theorem transverseEnergy_zero (d : ℕ) : transverseEnergy (0 : RawPoint d) = 0 := by
  simp [transverseEnergy]

theorem transverseEnergy_nonneg {d : ℕ} (p : RawPoint d) : 0 ≤ transverseEnergy p :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem continuous_transverseEnergy (d : ℕ) : Continuous (transverseEnergy (d := d)) := by
  unfold transverseEnergy
  fun_prop

theorem rawBodyWith_isClosed (d : ℕ) (Δ : ℝ) : IsClosed (rawBodyWith d Δ) := by
  have hcube : IsClosed {p : RawPoint d | ∀ i, |p.1 i| ≤ Real.sqrt 3} := by
    simp only [setOf_forall]
    apply isClosed_iInter
    intro i
    exact isClosed_le (by fun_prop) continuous_const
  exact hcube.inter (isClosed_le ((continuous_transverseEnergy d).add (by fun_prop))
    continuous_const)

theorem square_convex_combination {x y a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : (a * x + b * y) ^ 2 ≤ a * x ^ 2 + b * y ^ 2 := by
  have h : 0 ≤ a * b * (x - y) ^ 2 := mul_nonneg (mul_nonneg ha hb) (sq_nonneg _)
  nlinarith [sq_nonneg (x - y)]

theorem abs_convex_combination {x y a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |a * x + b * y| ≤ a * |x| + b * |y| := by
  simpa [abs_mul, abs_of_nonneg ha, abs_of_nonneg hb] using abs_add_le (a*x) (b*y)

theorem rawBodyWith_convex (d : ℕ) {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    Convex ℝ (rawBodyWith d Δ) := by
  intro p hp q hq a b ha hb hab
  constructor
  · intro i
    change |a * p.1 i + b * q.1 i| ≤ Real.sqrt 3
    calc
      _ ≤ a * |p.1 i| + b * |q.1 i| := abs_convex_combination ha hb
      _ ≤ a * Real.sqrt 3 + b * Real.sqrt 3 := add_le_add
        (mul_le_mul_of_nonneg_left (hp.1 i) ha) (mul_le_mul_of_nonneg_left (hq.1 i) hb)
      _ = Real.sqrt 3 := by rw [← add_mul, hab, one_mul]
  · have he : transverseEnergy (a • p + b • q) ≤
        a * transverseEnergy p + b * transverseEnergy q := by
      simp only [transverseEnergy, Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul]
      calc
        _ ≤ ∑ i, (a * (p.1 i)^2 + b * (q.1 i)^2) := Finset.sum_le_sum
          (fun i _ => square_convex_combination ha hb hab)
        _ = _ := by simp [Finset.sum_add_distrib, Finset.mul_sum]
    have hz : 2 * Δ * |(a • p + b • q).2| ≤
        2 * Δ * (a * |p.2| + b * |q.2|) :=
      mul_le_mul_of_nonneg_left (abs_convex_combination ha hb) (by positivity)
    have hp' := mul_le_mul_of_nonneg_left hp.2 ha
    have hq' := mul_le_mul_of_nonneg_left hq.2 hb
    nlinarith

theorem rawBodyWith_axial_bound {d : ℕ} {Δ : ℝ} (hΔ : 0 < Δ)
    {p : RawPoint d} (hp : p ∈ rawBodyWith d Δ) : |p.2| ≤ (d : ℝ) / (2 * Δ) := by
  apply (le_div_iff₀ (by positivity : 0 < 2 * Δ)).2
  have he := transverseEnergy_nonneg p
  nlinarith [hp.2]

theorem rawBodyWith_isCompact (d : ℕ) {Δ : ℝ} (hΔ : 0 < Δ) :
    IsCompact (rawBodyWith d Δ) := by
  apply (isCompact_Icc : IsCompact (Icc
    ((fun _ : Fin d => -Real.sqrt 3), -((d : ℝ)/(2*Δ)))
    ((fun _ : Fin d => Real.sqrt 3), (d : ℝ)/(2*Δ)))).of_isClosed_subset
    (rawBodyWith_isClosed d Δ)
  intro p hp
  have ht : ∀ i, -Real.sqrt 3 ≤ p.1 i ∧ p.1 i ≤ Real.sqrt 3 :=
    fun i => abs_le.mp (hp.1 i)
  have hz := abs_le.mp (rawBodyWith_axial_bound hΔ hp)
  exact ⟨⟨fun i => (ht i).1, hz.1⟩, ⟨fun i => (ht i).2, hz.2⟩⟩

theorem zero_mem_interior_rawBodyWith (d : ℕ) {Δ : ℝ}
    (hroom : 0 < (d : ℝ) - 2 * Δ) : (0 : RawPoint d) ∈ interior (rawBodyWith d Δ) := by
  let U : Set (RawPoint d) := {p | (∀ i, |p.1 i| < Real.sqrt 3) ∧
    transverseEnergy p + 2 * Δ * |p.2| < (d : ℝ) - 2 * Δ}
  have hU : IsOpen U := by
    change IsOpen ({p : RawPoint d | ∀ i, |p.1 i| < Real.sqrt 3} ∩
      {p | transverseEnergy p + 2 * Δ * |p.2| < (d : ℝ) - 2 * Δ})
    apply IsOpen.inter
    · simp only [setOf_forall]
      apply isOpen_iInter_of_finite
      intro i
      exact isOpen_lt (by fun_prop) continuous_const
    · exact isOpen_lt ((continuous_transverseEnergy d).add (by fun_prop)) continuous_const
  have hzero : (0 : RawPoint d) ∈ U := by
    constructor
    · intro i
      simpa using Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3)
    · simpa using hroom
  exact mem_interior.mpr ⟨U, fun p hp => ⟨fun i => (hp.1 i).le, hp.2.le⟩, hU, hzero⟩

/-- Independent coordinate reflections, encoded by a set of transverse indices and
an independent choice of axial sign. -/
def signChange {d : ℕ} (s : Fin d → Bool) (axial : Bool) (p : RawPoint d) : RawPoint d :=
  ((fun i => if s i then -p.1 i else p.1 i), if axial then -p.2 else p.2)

@[simp] theorem signChange_involutive {d : ℕ} (s : Fin d → Bool) (axial : Bool)
    (p : RawPoint d) : signChange s axial (signChange s axial p) = p := by
  ext i <;> simp [signChange] <;> split <;> simp_all

@[simp] theorem transverseEnergy_signChange {d : ℕ} (s : Fin d → Bool) (axial : Bool)
    (p : RawPoint d) : transverseEnergy (signChange s axial p) = transverseEnergy p := by
  apply Finset.sum_congr rfl
  intro i _
  simp only [signChange]
  split <;> simp

@[simp] theorem signChange_mem_rawBodyWith_iff {d : ℕ} (Δ : ℝ) (s : Fin d → Bool)
    (axial : Bool) (p : RawPoint d) :
    signChange s axial p ∈ rawBodyWith d Δ ↔ p ∈ rawBodyWith d Δ := by
  simp only [rawBodyWith, mem_setOf_eq, transverseEnergy_signChange]
  have hc : (∀ i, |(signChange s axial p).1 i| ≤ Real.sqrt 3) ↔
      ∀ i, |p.1 i| ≤ Real.sqrt 3 := by
    simp [signChange, apply_ite abs, abs_neg]
  rw [hc]
  simp [signChange, apply_ite abs, abs_neg]

def transversePermute {d : ℕ} (σ : Equiv.Perm (Fin d)) (p : RawPoint d) : RawPoint d :=
  ((fun i => p.1 (σ i)), p.2)

@[simp] theorem transverseEnergy_permute {d : ℕ} (σ : Equiv.Perm (Fin d)) (p : RawPoint d) :
    transverseEnergy (transversePermute σ p) = transverseEnergy p := by
  exact Equiv.sum_comp σ (fun i => (p.1 i)^2)

@[simp] theorem transversePermute_mem_rawBodyWith_iff {d : ℕ} (Δ : ℝ)
    (σ : Equiv.Perm (Fin d)) (p : RawPoint d) :
    transversePermute σ p ∈ rawBodyWith d Δ ↔ p ∈ rawBodyWith d Δ := by
  change ((∀ i, |p.1 (σ i)| ≤ Real.sqrt 3) ∧
      transverseEnergy (transversePermute σ p) + 2 * Δ * |p.2| ≤ (d : ℝ) - 2 * Δ) ↔ _
  rw [transverseEnergy_permute]
  apply and_congr _ Iff.rfl
  constructor
  · intro h i
    obtain ⟨j, rfl⟩ := σ.surjective i
    exact h j
  · intro h i
    exact h (σ i)

/-- A genuine convex body, with the stronger interior statement proved separately. -/
def rawConvexBodyWith (d : ℕ) {Δ : ℝ} (hΔ : 0 < Δ) (hroom : 0 < (d : ℝ) - 2*Δ) :
    ConvexBody (RawPoint d) where
  carrier := rawBodyWith d Δ
  convex' := rawBodyWith_convex d hΔ.le
  isCompact' := rawBodyWith_isCompact d hΔ
  nonempty' := ⟨0, interior_subset (zero_mem_interior_rawBodyWith d hroom)⟩


theorem deviationScale_pos {d : ℕ} (hd : 0 < d) : 0 < deviationScale d := by
  unfold deviationScale
  positivity

/-- The dimensional condition required for the explicit raw body holds eventually. -/
theorem eventually_rawBody_parameters :
    ∀ᶠ d : ℕ in atTop, 0 < deviationScale d ∧ 0 < (d : ℝ) - 2 * deviationScale d := by
  have hg : ∀ᶠ d : ℕ in atTop, 2 < (d : ℝ) ^ (2 / 5 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 5)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_gt_atTop 2)
  filter_upwards [hg, eventually_gt_atTop 0] with d hd hd0
  have hΔ := deviationScale_pos hd0
  refine ⟨hΔ, ?_⟩
  have hprod : deviationScale d * (d : ℝ) ^ (2 / 5 : ℝ) = d := by
    rw [deviationScale, ← Real.rpow_add (by positivity : (0 : ℝ) < d)]
    norm_num
  nlinarith

/-- Geometric portion of Lemma 4.2, for the paper's exact scale. -/
theorem eventually_rawBody_geometry : ∀ᶠ d : ℕ in atTop,
    IsCompact (rawBody d) ∧ Convex ℝ (rawBody d) ∧
      (0 : RawPoint d) ∈ interior (rawBody d) := by
  filter_upwards [eventually_rawBody_parameters] with d hd
  exact ⟨rawBodyWith_isCompact d hd.1, rawBodyWith_convex d hd.1.le,
    zero_mem_interior_rawBodyWith d hd.2⟩

end GaussianTilt
