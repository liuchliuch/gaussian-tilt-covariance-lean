import GaussianTilt.MomentMapRegularityDirichletDual

/-! # The actual finite atomic Dirichlet variational functional

The excess of finitely many lifted affine functions over the boundary
support function has compact slope support. Its integral is therefore a
genuine finite convex functional of the cell heights.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators Gradient ENNReal NNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}
variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

def boundarySupport (S : Set (E n)) : E n → ℝ := domainConjugate S (fun _ => 0)

def atomicExcess (S : Set (E n)) (X : ι → E n) (h : ι → ℝ) (p : E n) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => max 0 (inner ℝ p (X i) + h i - boundarySupport S p))

def atomicDirichletEnergy (S : Set (E n)) (X : ι → E n) (mass h : ι → ℝ) : ℝ :=
  (∫ p, atomicExcess S X h p) - ∑ i, mass i * h i

lemma boundarySupport_continuous {S : Set (E n)} (hS : IsCompact S) (hSn : S.Nonempty) :
    Continuous (boundarySupport S) := by
  exact continuousOn_univ.mp ((domainConjugate_convex hS hSn continuousOn_const).continuousOn isOpen_univ)

lemma boundarySupport_ge_inner {S : Set (E n)} (hS : IsCompact S) {x : E n} (hx : x ∈ S)
    (p : E n) : inner ℝ p x ≤ boundarySupport S p := by
  simpa only [sub_zero] using domainConjugate_fenchel_le hS (u := fun _ => (0 : ℝ)) continuousOn_const p hx

lemma boundarySupport_le_norm {S : Set (E n)} (hSn : S.Nonempty) {R : ℝ}
    (hR : ∀ x ∈ S, ‖x‖ ≤ R) (p : E n) : boundarySupport S p ≤ R * ‖p‖ := by
  apply csSup_le (domainConjugateValues_nonempty hSn (fun _ => 0) p)
  rintro _ ⟨x, hx, rfl⟩
  simp only [sub_zero]
  exact (real_inner_le_norm p x).trans (by nlinarith [mul_le_mul_of_nonneg_left (hR x hx) (norm_nonneg p)])

lemma boundarySupport_ge_inner_add_norm {S : Set (E n)} (hS : IsCompact S)
    {x : E n} {r : ℝ} (hr : 0 < r) (hb : Metric.closedBall x r ⊆ S) (p : E n) :
    inner ℝ p x + r * ‖p‖ ≤ boundarySupport S p := by
  by_cases hp : p = 0
  · subst p
    simpa using boundarySupport_ge_inner hS (hb (Metric.mem_closedBall_self hr.le)) (0 : E n)
  have hpn := norm_pos_iff.mpr hp
  have hz : x + (r / ‖p‖) • p ∈ S := by
    apply hb
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos (div_pos hr hpn)]
    exact le_of_eq (div_mul_cancel₀ r hpn.ne')
  have h := boundarySupport_ge_inner hS hz p
  rw [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq] at h
  have he : r / ‖p‖ * ‖p‖^2 = r * ‖p‖ := by field_simp
  rwa [he] at h

lemma atomicExcess_nonneg (S : Set (E n)) (X : ι → E n) (h : ι → ℝ) (p : E n) :
    0 ≤ atomicExcess S X h p := by
  let i : ι := Classical.arbitrary ι
  unfold atomicExcess
  exact (le_max_left _ _).trans (Finset.le_sup' (fun j : ι => max 0 (inner ℝ p (X j) + h j - boundarySupport S p)) (Finset.mem_univ i))

lemma atomicExcess_ge_atom (S : Set (E n)) (X : ι → E n) (h : ι → ℝ) (p : E n) (i : ι) :
    inner ℝ p (X i) + h i - boundarySupport S p ≤ atomicExcess S X h p := by
  unfold atomicExcess
  exact (le_max_right _ _).trans (Finset.le_sup' (fun j : ι => max 0 (inner ℝ p (X j) + h j - boundarySupport S p)) (Finset.mem_univ i))

lemma atomicExcess_le_height {S : Set (E n)} (hS : IsCompact S) {X : ι → E n}
    (hX : ∀ i, X i ∈ S) (h : ι → ℝ) (p : E n) : atomicExcess S X h p ≤ ‖h‖ := by
  apply Finset.sup'_le
  intro i _
  apply max_le (norm_nonneg h)
  have hs := boundarySupport_ge_inner hS (hX i) p
  have hh := (le_abs_self (h i)).trans (by simpa using norm_le_pi_norm h i)
  linarith

lemma atomicExcess_continuous {S : Set (E n)} (hS : IsCompact S) (hSn : S.Nonempty)
    (X : ι → E n) (h : ι → ℝ) : Continuous (atomicExcess S X h) := by
  apply Continuous.finset_sup'_apply
  intro i _
  exact continuous_const.max (((continuous_id.inner continuous_const).add continuous_const).sub
    (boundarySupport_continuous hS hSn))

lemma atomicExcess_eq_zero_outside {S : Set (E n)} (hS : IsCompact S) {X : ι → E n}
    {r : ℝ} (hr : 0 < r) (hb : ∀ i, Metric.closedBall (X i) r ⊆ S)
    (h : ι → ℝ) {p : E n} (hp : ‖h‖ / r < ‖p‖) : atomicExcess S X h p = 0 := by
  apply le_antisymm _ (atomicExcess_nonneg S X h p)
  apply Finset.sup'_le
  intro i _
  apply max_le le_rfl
  have hs := boundarySupport_ge_inner_add_norm hS hr (hb i) p
  have hh := (le_abs_self (h i)).trans (by simpa using norm_le_pi_norm h i)
  have hpr := (div_lt_iff₀ hr).mp hp
  nlinarith

/-- Compact slope support is derived from the actual interior-node balls. -/
theorem atomicExcess_integrable {S : Set (E n)} (hS : IsCompact S) {X : ι → E n}
    {r : ℝ} (hr : 0 < r) (hb : ∀ i, Metric.closedBall (X i) r ⊆ S) (h : ι → ℝ) :
    Integrable (atomicExcess S X h) := by
  have hSn : S.Nonempty := ⟨X (Classical.arbitrary ι), hb _ (Metric.mem_closedBall_self hr.le)⟩
  have hc := atomicExcess_continuous hS hSn X h
  have hs : HasCompactSupport (atomicExcess S X h) := by
    apply HasCompactSupport.intro (isCompact_closedBall (0 : E n) (‖h‖ / r))
    intro p hp
    apply atomicExcess_eq_zero_outside hS hr hb h
    simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hp
  exact hc.integrable_of_hasCompactSupport hs

lemma atomicExcess_convex_height (S : Set (E n)) (X : ι → E n) (p : E n) :
    ConvexOn ℝ univ (fun h => atomicExcess S X h p) := by
  refine ⟨convex_univ, ?_⟩
  intro h _ k _ a b ha hb hab
  apply Finset.sup'_le
  intro i _
  have hhi := atomicExcess_ge_atom S X h p i
  have hki := atomicExcess_ge_atom S X k p i
  have hz : 0 ≤ a * atomicExcess S X h p + b * atomicExcess S X k p :=
    add_nonneg (mul_nonneg ha (atomicExcess_nonneg S X h p)) (mul_nonneg hb (atomicExcess_nonneg S X k p))
  apply max_le hz
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have he : a * (inner ℝ p (X i) - boundarySupport S p) +
      b * (inner ℝ p (X i) - boundarySupport S p) = inner ℝ p (X i) - boundarySupport S p := by
    rw [← add_mul, hab, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left hhi ha, mul_le_mul_of_nonneg_left hki hb]

/-- The finite-height energy is genuinely convex, because all its defining
integrals were already proved finite. -/
theorem atomicDirichletEnergy_convex {S : Set (E n)} (hS : IsCompact S) {X : ι → E n}
    {r : ℝ} (hr : 0 < r) (hb : ∀ i, Metric.closedBall (X i) r ⊆ S) (mass : ι → ℝ) :
    ConvexOn ℝ univ (atomicDirichletEnergy S X mass) := by
  refine ⟨convex_univ, ?_⟩
  intro h _ k _ a b ha hb' hab
  have hi (h : ι → ℝ) := atomicExcess_integrable hS hr hb h
  have hconv := integral_mono (hi (a • h + b • k))
    (((hi h).const_mul a).add ((hi k).const_mul b)) (fun p =>
      (atomicExcess_convex_height S X p).2 (mem_univ h) (mem_univ k) ha hb' hab)
  simp only [Pi.add_apply] at hconv
  rw [integral_add ((hi h).const_mul a) ((hi k).const_mul b), integral_const_mul, integral_const_mul] at hconv
  have hlin : (∑ i, mass i * (a • h + b • k) i) =
      a * (∑ i, mass i * h i) + b * (∑ i, mass i * k i) := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
      Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring
  change (∫ p, atomicExcess S X (a • h + b • k) p) - _ ≤ _
  rw [hlin]
  dsimp only [atomicDirichletEnergy]
  simp only [smul_eq_mul]
  linarith

theorem atomicDirichletEnergy_continuous {S : Set (E n)} (hS : IsCompact S) {X : ι → E n}
    {r : ℝ} (hr : 0 < r) (hb : ∀ i, Metric.closedBall (X i) r ⊆ S) (mass : ι → ℝ) :
    Continuous (atomicDirichletEnergy S X mass) :=
  continuousOn_univ.mp ((atomicDirichletEnergy_convex hS hr hb mass).continuousOn isOpen_univ)

end GaussianTilt.MomentMapRegularity
