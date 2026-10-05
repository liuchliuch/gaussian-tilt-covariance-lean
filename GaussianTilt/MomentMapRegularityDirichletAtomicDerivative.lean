import GaussianTilt.MomentMapRegularityDirichletAtomicEnvelope

/-! # Coordinate derivatives of the actual atomic envelope -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators Gradient ENNReal NNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}
variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

def heightPerturb (h : ι → ℝ) (i : ι) (t : ℝ) : ι → ℝ := h + t • (Pi.single i (1 : ℝ) : ι → ℝ)

def atomicCell (S : Set (E n)) (X : ι → E n) (h : ι → ℝ) (i : ι) : Set (E n) :=
  {p | boundarySupport S p < inner ℝ p (X i) + h i ∧
    ∀ j, j ≠ i → inner ℝ p (X j) + h j < inner ℝ p (X i) + h i}

lemma atomicCell_measurable {S : Set (E n)} (hS : IsCompact S) (hSn : S.Nonempty)
    (X : ι → E n) (h : ι → ℝ) (i : ι) : MeasurableSet (atomicCell S X h i) := by
  change MeasurableSet ({p | boundarySupport S p < inner ℝ p (X i) + h i} ∩
    {p | ∀ j, j ≠ i → inner ℝ p (X j) + h j < inner ℝ p (X i) + h i})
  apply MeasurableSet.inter
  · exact measurableSet_lt (boundarySupport_continuous hS hSn).measurable (by fun_prop)
  · simp only [setOf_forall]
    exact MeasurableSet.iInter (fun j => MeasurableSet.iInter (fun _ => measurableSet_lt (by fun_prop) (by fun_prop)))

lemma atomicLift_eq_atom_of_cell (S : Set (E n)) (X : ι → E n) (h : ι → ℝ)
    {p : E n} {i : ι} (hp : p ∈ atomicCell S X h i) :
    atomicLift S X h p = inner ℝ p (X i) + h i := by
  apply le_antisymm _ (atomicLift_ge_atom S X h p i)
  apply Finset.sup'_le
  intro j _
  apply max_le hp.1.le
  by_cases hji : j = i
  · subst j; rfl
  · exact (hp.2 j hji).le

lemma atomicExcess_lipschitz_coordinate (S : Set (E n)) (X : ι → E n) (h : ι → ℝ)
    (i : ι) (p : E n) : LipschitzWith 1 (fun t => atomicExcess S X (heightPerturb h i t) p) := by
  have hone (s t : ℝ) : atomicExcess S X (heightPerturb h i s) p ≤
      atomicExcess S X (heightPerturb h i t) p + |s - t| := by
    apply Finset.sup'_le
    intro j _
    apply max_le (by have hz := atomicExcess_nonneg S X (heightPerturb h i t) p; positivity)
    have hh := atomicExcess_ge_atom S X (heightPerturb h i t) p j
    by_cases hji : j = i
    · subst j
      simp only [heightPerturb, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at hh ⊢
      linarith [le_abs_self (s - t)]
    · simp only [heightPerturb, Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hji,
        smul_eq_mul, mul_zero, add_zero] at hh ⊢
      linarith [abs_nonneg (s - t)]
  rw [← Real.toNNReal_one]
  apply LipschitzWith.of_dist_le'
  intro s t
  simp only [Real.dist_eq, NNReal.coe_one, one_mul, abs_sub_le_iff]
  constructor
  · linarith [hone s t]
  · have ht := hone t s
    rw [abs_sub_comm t s] at ht
    linarith

lemma atomicExcess_deriv_at_boundary_branch (S : Set (E n)) (X : ι → E n) (h : ι → ℝ)
    (i : ι) {p : E n} (hp : ∀ j, inner ℝ p (X j) + h j < boundarySupport S p) :
    HasDerivAt (fun t => atomicExcess S X (heightPerturb h i t) p) 0 0 := by
  have hev : ∀ᶠ t : ℝ in 𝓝 0, ∀ j, inner ℝ p (X j) + heightPerturb h i t j < boundarySupport S p := by
    apply Filter.eventually_all.mpr
    intro j
    have hc : Continuous (fun t : ℝ => inner ℝ p (X j) + heightPerturb h i t j) := by unfold heightPerturb; fun_prop
    exact hc.continuousAt.eventually (eventually_lt_nhds (by simpa [heightPerturb] using hp j))
  apply (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
  filter_upwards [hev] with t ht
  apply le_antisymm _ (atomicExcess_nonneg S X _ p)
  apply Finset.sup'_le
  intro j _
  exact max_le le_rfl (by linarith [ht j])

lemma atomicExcess_deriv_at_atom_branch (S : Set (E n)) (X : ι → E n) (h : ι → ℝ)
    (i : ι) {p : E n} {j : ι} (hp : p ∈ atomicCell S X h j) :
    HasDerivAt (fun t => atomicExcess S X (heightPerturb h i t) p) (if j = i then 1 else 0) 0 := by
  have hB : ∀ᶠ t : ℝ in 𝓝 0,
      boundarySupport S p < inner ℝ p (X j) + heightPerturb h i t j := by
    have hc : Continuous (fun t : ℝ => inner ℝ p (X j) + heightPerturb h i t j) := by unfold heightPerturb; fun_prop
    exact hc.continuousAt.eventually (eventually_gt_nhds (by simpa [heightPerturb] using hp.1))
  have hJ : ∀ᶠ t : ℝ in 𝓝 0, ∀ k, k ≠ j →
      inner ℝ p (X k) + heightPerturb h i t k < inner ℝ p (X j) + heightPerturb h i t j := by
    apply Filter.eventually_all.mpr
    intro k
    by_cases hkj : k = j
    · subst k; exact Eventually.of_forall (fun _ h => False.elim (h rfl))
    · have hc : Continuous (fun t : ℝ => (inner ℝ p (X j) + heightPerturb h i t j) -
          (inner ℝ p (X k) + heightPerturb h i t k)) := by unfold heightPerturb; fun_prop
      have hzero : 0 < (inner ℝ p (X j) + heightPerturb h i 0 j) -
          (inner ℝ p (X k) + heightPerturb h i 0 k) := by
        simpa [heightPerturb] using sub_pos.mpr (hp.2 k hkj)
      have ht := hc.continuousAt.eventually (eventually_gt_nhds hzero)
      filter_upwards [ht] with t hkt _
      exact sub_pos.mp hkt
  have heq : (fun t => atomicExcess S X (heightPerturb h i t) p) =ᶠ[𝓝 0]
      (fun t => inner ℝ p (X j) + h j + t * (if j = i then 1 else 0) - boundarySupport S p) := by
    filter_upwards [hB, hJ] with t hbt hjt
    have hval := atomicLift_eq_atom_of_cell S X (heightPerturb h i t) (p := p) (i := j) ⟨hbt, hjt⟩
    rw [atomicLift_eq_boundary_add_excess] at hval
    have hpert : heightPerturb h i t j = h j + t * (if j = i then 1 else 0) := by simp [heightPerturb, Pi.single_apply, eq_comm]
    rw [hpert] at hval
    linarith
  have h1 : HasDerivAt (fun t : ℝ => t * (if j = i then (1 : ℝ) else 0))
      (if j = i then 1 else 0) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const (if j = i then (1 : ℝ) else 0)
  exact ((h1.const_add (inner ℝ p (X j) + h j)).sub_const
    (boundarySupport S p)).congr_of_eventuallyEq heq

/-- Coordinate envelope differentiation holds at almost every slope, with
the derivative exactly the indicator of the constructed atomic cell. -/
theorem atomicExcess_ae_hasDerivAt_coordinate [NeZero n] {S : Set (E n)} (hS : IsCompact S)
    {X : ι → E n} (hX : Function.Injective X) {r : ℝ} (hr : 0 < r)
    (hb : ∀ j, Metric.closedBall (X j) r ⊆ S) (h : ι → ℝ) (i : ι) :
    ∀ᵐ p ∂volume, HasDerivAt (fun t => atomicExcess S X (heightPerturb h i t) p)
      ((atomicCell S X h i).indicator (fun _ => (1 : ℝ)) p) 0 := by
  filter_upwards [atomicLift_ae_unique_branch hS hX hr hb h] with p hp
  rcases hp with ⟨_, hB⟩ | ⟨j, _, hBj, hJj⟩
  · have hn : p ∉ atomicCell S X h i := fun hc => (hB i).not_ge hc.1.le
    rw [indicator_of_notMem hn]
    exact atomicExcess_deriv_at_boundary_branch S X h i hB
  · have hj : p ∈ atomicCell S X h j := ⟨hBj, hJj⟩
    have hd := atomicExcess_deriv_at_atom_branch S X h i hj
    by_cases hji : j = i
    · subst j
      simpa [indicator_of_mem hj] using hd
    · have hn : p ∉ atomicCell S X h i := by
        intro hi
        exact (hi.2 j hji).not_ge (hJj i (Ne.symm hji)).le
      simpa [hji, indicator_of_notMem hn] using hd

end GaussianTilt.MomentMapRegularity
