import GaussianTilt.MomentMapRegularityDirichletAtomicMinimum

/-! # A.e. uniqueness of the actual finite Dirichlet envelope branch

Uniqueness is derived from a.e. differentiation of the convex slope envelope.
Interior nodes exclude a tie with the boundary support branch away from the
origin. No exceptional-set or uniqueness premise is assumed.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators Gradient ENNReal NNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}
variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

def atomicLift (S : Set (E n)) (X : ι → E n) (h : ι → ℝ) (p : E n) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => max (boundarySupport S p) (inner ℝ p (X i) + h i))

lemma atomicLift_ge_boundary (S : Set (E n)) (X : ι → E n) (h : ι → ℝ) (p : E n) :
    boundarySupport S p ≤ atomicLift S X h p := by
  unfold atomicLift
  exact (le_max_left _ _).trans
    (Finset.le_sup' (fun i : ι => max (boundarySupport S p) (inner ℝ p (X i) + h i))
      (Finset.mem_univ (Classical.arbitrary ι)))

lemma atomicLift_ge_atom (S : Set (E n)) (X : ι → E n) (h : ι → ℝ) (p : E n) (i : ι) :
    inner ℝ p (X i) + h i ≤ atomicLift S X h p := by
  unfold atomicLift
  exact (le_max_right _ _).trans
    (Finset.le_sup' (fun j : ι => max (boundarySupport S p) (inner ℝ p (X j) + h j)) (Finset.mem_univ i))

lemma atomicLift_eq_boundary_add_excess (S : Set (E n)) (X : ι → E n) (h : ι → ℝ) (p : E n) :
    atomicLift S X h p = boundarySupport S p + atomicExcess S X h p := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro i _
    apply max_le
    · linarith [atomicExcess_nonneg S X h p]
    · linarith [atomicExcess_ge_atom S X h p i]
  · obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun i : ι => max 0 (inner ℝ p (X i) + h i - boundarySupport S p))
    change atomicExcess S X h p = _ at hi
    rw [hi]
    rcases le_total (inner ℝ p (X i) + h i - boundarySupport S p) 0 with hle | hge
    · rw [max_eq_left hle, add_zero]
      exact atomicLift_ge_boundary S X h p
    · rw [max_eq_right hge]
      have h := atomicLift_ge_atom S X h p i
      linarith

lemma atomicLift_convex {S : Set (E n)} (hS : IsCompact S) (hSn : S.Nonempty)
    (X : ι → E n) (h : ι → ℝ) : ConvexOn ℝ univ (atomicLift S X h) := by
  have hs : ConvexOn ℝ univ (boundarySupport S) := domainConjugate_convex hS hSn continuousOn_const
  refine ⟨convex_univ, ?_⟩
  intro p _ q _ a b ha hb hab
  apply Finset.sup'_le
  intro i _
  apply max_le
  · have hc := hs.2 (mem_univ p) (mem_univ q) ha hb hab
    have hp := mul_le_mul_of_nonneg_left (atomicLift_ge_boundary S X h p) ha
    have hq := mul_le_mul_of_nonneg_left (atomicLift_ge_boundary S X h q) hb
    simp only [smul_eq_mul] at hc ⊢
    linarith
  · have hp := mul_le_mul_of_nonneg_left (atomicLift_ge_atom S X h p i) ha
    have hq := mul_le_mul_of_nonneg_left (atomicLift_ge_atom S X h q i) hb
    have he : a * h i + b * h i = h i := by rw [← add_mul, hab, one_mul]
    simp only [inner_add_left, real_inner_smul_left, smul_eq_mul]
    nlinarith

lemma boundarySupport_attained {S : Set (E n)} (hS : IsCompact S) (hSn : S.Nonempty) (p : E n) :
    ∃ x ∈ S, boundarySupport S p = inner ℝ p x := by
  obtain ⟨x, hx, hs⟩ := exists_supportsOn_compact hS hSn (u := fun _ => (0 : ℝ)) continuousOn_const p
  exact ⟨x, hx, by simpa only [sub_zero] using domainConjugate_eq_of_support hx hs⟩

lemma atomicLift_supports_active_atom (S : Set (E n)) (X : ι → E n) (h : ι → ℝ)
    {p : E n} {i : ι} (hi : atomicLift S X h p = inner ℝ p (X i) + h i) :
    SupportsAt (atomicLift S X h) (X i) p := by
  intro q
  rw [hi, inner_sub_right]
  have hq := atomicLift_ge_atom S X h q i
  linarith [real_inner_comm (X i) q, real_inner_comm (X i) p]

lemma atomicLift_supports_active_boundary {S : Set (E n)} (hS : IsCompact S)
    (X : ι → E n) (h : ι → ℝ) {p z : E n} (hz : z ∈ S)
    (hval : boundarySupport S p = inner ℝ p z)
    (hp : atomicLift S X h p = boundarySupport S p) : SupportsAt (atomicLift S X h) z p := by
  intro q
  rw [hp, hval, inner_sub_right]
  have hq := (boundarySupport_ge_inner hS hz q).trans (atomicLift_ge_boundary S X h q)
  linarith [real_inner_comm z q, real_inner_comm z p]

lemma atomicLift_no_boundary_atom_tie {S : Set (E n)} (hS : IsCompact S) (hSn : S.Nonempty)
    {X : ι → E n} {r : ℝ} (hr : 0 < r) (hb : ∀ i, Metric.closedBall (X i) r ⊆ S)
    (h : ι → ℝ) {p : E n} (hp : p ≠ 0) (hd : DifferentiableAt ℝ (atomicLift S X h) p)
    (hval : atomicLift S X h p = boundarySupport S p) (i : ι) :
    inner ℝ p (X i) + h i ≠ boundarySupport S p := by
  intro heq
  obtain ⟨z, hz, hzval⟩ := boundarySupport_attained hS hSn p
  have h1 := supporting_vector_eq_gradient hd (atomicLift_supports_active_atom S X h (hval.trans heq.symm))
  have h2 := supporting_vector_eq_gradient hd (atomicLift_supports_active_boundary hS X h hz hzval hval)
  have hxz : X i = z := h1.symm.trans h2
  have hgap := boundarySupport_ge_inner_add_norm hS hr (hb i) p
  rw [hxz, hzval] at hgap
  have hp' := norm_pos_iff.mpr hp
  nlinarith

/-- The unique active branch is either the boundary support or exactly one
atomic plane. Its exceptional set is proved Lebesgue null. -/
theorem atomicLift_ae_unique_branch [NeZero n] {S : Set (E n)} (hS : IsCompact S)
    {X : ι → E n} (hX : Function.Injective X) {r : ℝ} (hr : 0 < r)
    (hb : ∀ i, Metric.closedBall (X i) r ⊆ S) (h : ι → ℝ) :
    ∀ᵐ p ∂volume,
      (atomicLift S X h p = boundarySupport S p ∧ ∀ i, inner ℝ p (X i) + h i < boundarySupport S p) ∨
      ∃ i, atomicLift S X h p = inner ℝ p (X i) + h i ∧
        boundarySupport S p < inner ℝ p (X i) + h i ∧
        ∀ j, j ≠ i → inner ℝ p (X j) + h j < inner ℝ p (X i) + h i := by
  have hSn : S.Nonempty := ⟨X (Classical.arbitrary ι), hb _ (Metric.mem_closedBall_self hr.le)⟩
  have hp0 : ∀ᵐ p : E n ∂volume, p ≠ 0 := by
    apply ae_iff.mpr
    simp
  filter_upwards [MomentMapCoercivity.convex_ae_differentiable (atomicLift_convex hS hSn X h), hp0]
    with p hd hp
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun j : ι => max (boundarySupport S p) (inner ℝ p (X j) + h j))
  change atomicLift S X h p = _ at hi
  rcases le_total (inner ℝ p (X i) + h i) (boundarySupport S p) with hiB | hBi
  · rw [max_eq_left hiB] at hi
    refine Or.inl ⟨hi, fun j => ?_⟩
    have hj := atomicLift_ge_atom S X h p j
    rw [hi] at hj
    exact lt_of_le_of_ne hj (atomicLift_no_boundary_atom_tie hS hSn hr hb h hp hd hi j)
  · rw [max_eq_right hBi] at hi
    have hBne : boundarySupport S p ≠ inner ℝ p (X i) + h i := by
      intro heq
      exact atomicLift_no_boundary_atom_tie hS hSn hr hb h hp hd (hi.trans heq.symm) i heq.symm
    refine Or.inr ⟨i, hi, lt_of_le_of_ne hBi hBne, ?_⟩
    intro j hji
    have hj := atomicLift_ge_atom S X h p j
    rw [hi] at hj
    apply lt_of_le_of_ne hj
    intro heq
    have h1 := supporting_vector_eq_gradient hd (atomicLift_supports_active_atom S X h hi)
    have h2 := supporting_vector_eq_gradient hd (atomicLift_supports_active_atom S X h (hi.trans heq.symm))
    exact hji (hX (h2.symm.trans h1))

end GaussianTilt.MomentMapRegularity
