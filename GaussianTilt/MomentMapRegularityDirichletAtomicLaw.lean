import GaussianTilt.MomentMapRegularityDirichletAtomicPotential

/-! # Exact atomic Alexandrov law of the constructed Dirichlet potential -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators Gradient ENNReal NNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}
variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

def atomicNodeIndices (X : ι → E n) (A : Set (E n)) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => X i ∈ A)

lemma boundarySupport_maximizer_not_interior {S : Set (E n)} (hS : IsCompact S)
    {p z : E n} (hp : p ≠ 0) (hval : boundarySupport S p = inner ℝ p z) : z ∉ interior S := by
  intro hz
  obtain ⟨r, hr, hb⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hz)
  have hcb : Metric.closedBall z (r / 2) ⊆ S :=
    (Metric.closedBall_subset_ball (half_lt_self hr)).trans hb
  have h := boundarySupport_ge_inner_add_norm hS (half_pos hr) hcb p
  rw [hval] at h
  nlinarith [norm_pos_iff.mpr hp]

lemma atomicCell_subset_slopeBall {S : Set (E n)} (hS : IsCompact S)
    {X : ι → E n} {r : ℝ} (hr : 0 < r) (hb : ∀ i, Metric.closedBall (X i) r ⊆ S)
    (h : ι → ℝ) (i : ι) : atomicCell S X h i ⊆ Metric.ball 0 (atomicSlopeRadius h r) := by
  intro p hp
  have hgap := boundarySupport_ge_inner_add_norm hS hr (hb i) p
  have hheight := (le_abs_self (h i)).trans (by simpa using norm_le_pi_norm h i)
  rw [Metric.mem_ball, dist_zero_right]
  apply (lt_div_iff₀ hr).mpr
  have hc := hp.1
  nlinarith

lemma atomicCells_disjoint (S : Set (E n)) (X : ι → E n) (h : ι → ℝ) :
    Pairwise (fun i j => Disjoint (atomicCell S X h i) (atomicCell S X h j)) := by
  intro i j hij
  apply disjoint_left.mpr
  intro p hi hj
  exact (hi.2 j (Ne.symm hij)).not_ge (hj.2 i hij).le

/-- Interior supporting images agree a.e. with the union of the explicitly
constructed atomic cells whose source nodes belong to the given set. -/
theorem atomic_potential_subgradientImage_ae_cells [NeZero n] {S : Set (E n)}
    (hS : IsCompact S) {X : ι → E n} (hX : Function.Injective X) {r : ℝ} (hr : 0 < r)
    (hb : ∀ i, Metric.closedBall (X i) r ⊆ S) (h : ι → ℝ)
    (A : Set (E n)) (hA : A ⊆ interior S) :
    subgradientImageOn S (atomicDirichletPotential S X h r) A =ᵐ[volume]
      ⋃ i ∈ atomicNodeIndices X A, atomicCell S X h i := by
  classical
  let B := atomicSlopeRadius h r
  let g := atomicLift S X h
  let u := atomicDirichletPotential S X h r
  have hB : 0 < B := atomicSlopeRadius_pos h hr
  have hSn : S.Nonempty := ⟨X (Classical.arbitrary ι), hb _ (Metric.mem_closedBall_self hr.le)⟩
  have hgc : ConvexOn ℝ univ g := atomicLift_convex hS hSn X h
  have hg : Continuous g := atomicLift_continuous hS hSn X h
  have hu : ConvexOn ℝ univ u := atomicDirichletPotential_convex hS hSn X h hr
  have huL : LipschitzWith B.toNNReal u := atomicDirichletPotential_lipschitz hS hSn X h hr
  have hpzero : ∀ᵐ p : E n ∂volume, p ≠ 0 := by apply ae_iff.mpr; simp
  have hsphere : ∀ᵐ p : E n ∂volume, ‖p‖ ≠ B := by
    apply ae_iff.mpr
    have hz := (convex_closedBall (0 : E n) B).addHaar_frontier volume
    rw [frontier_closedBall (0 : E n) hB.ne'] at hz
    simpa only [not_not, Metric.sphere, dist_zero_right] using hz
  filter_upwards [MomentMapCoercivity.convex_ae_differentiable hgc,
    atomicLift_ae_unique_branch hS hX hr hb h, hpzero, hsphere] with p hd hbranch hp0 hpB
  apply propext
  constructor
  · rintro ⟨x, hx, hs⟩
    have hglobal : SupportsAt u p x := (supportsOn_iff_supportsAt_of_mem_interior hu (hA hx)).mp hs
    have hpclosed := supportsAt_norm_le huL hglobal
    rw [Real.coe_toNNReal B hB.le] at hpclosed
    have hpball : p ∈ Metric.ball (0 : E n) B := by
      rw [Metric.mem_ball, dist_zero_right]
      exact lt_of_le_of_ne hpclosed hpB
    have hxgrad : x = gradient g p := (truncated_conjugate_support_iff_gradient hB hgc hg hpball hd).mp hglobal
    rcases hbranch with ⟨hboundary, _⟩ | ⟨i, hival, hiB, hiJ⟩
    · obtain ⟨z, hz, hzval⟩ := boundarySupport_attained hS hSn p
      have hgs := atomicLift_supports_active_boundary hS X h hz hzval hboundary
      have hzgrad : gradient g p = z := supporting_vector_eq_gradient hd hgs
      have hxz := hxgrad.trans hzgrad
      exact False.elim (boundarySupport_maximizer_not_interior hS hp0 hzval (hxz ▸ hA hx))
    · have hgs := atomicLift_supports_active_atom S X h hival
      have higrad : gradient g p = X i := supporting_vector_eq_gradient hd hgs
      have hxi : X i ∈ A := (hxgrad.trans higrad) ▸ hx
      exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨(show i ∈ atomicNodeIndices X A by simpa [atomicNodeIndices] using hxi), hiB, hiJ⟩⟩
  · intro hpc
    obtain ⟨i, hpi⟩ := mem_iUnion.mp hpc
    obtain ⟨hi, hcell⟩ := mem_iUnion.mp hpi
    have hpball := atomicCell_subset_slopeBall hS hr hb h i hcell
    have hs := atomicLift_supports_active_atom S X h (atomicLift_eq_atom_of_cell S X h hcell)
    have hrec := truncated_conjugate_reciprocal hB hg (Metric.ball_subset_closedBall hpball) hs
    exact ⟨X i, (show X i ∈ A by simpa [atomicNodeIndices] using hi), supportsOn_of_supportsAt hrec.2⟩

/-- The finite potential's entire interior Alexandrov mass is exactly the
sum of the volumes of its active cells. -/
theorem atomicDirichletPotential_image_volume [NeZero n] {S : Set (E n)}
    (hS : IsCompact S) {X : ι → E n} (hX : Function.Injective X) {r : ℝ} (hr : 0 < r)
    (hb : ∀ i, Metric.closedBall (X i) r ⊆ S) (h : ι → ℝ)
    (A : Set (E n)) (hA : A ⊆ interior S) :
    volume (subgradientImageOn S (atomicDirichletPotential S X h r) A) =
      ∑ i ∈ atomicNodeIndices X A, volume (atomicCell S X h i) := by
  classical
  have hSn : S.Nonempty := ⟨X (Classical.arbitrary ι), hb _ (Metric.mem_closedBall_self hr.le)⟩
  rw [measure_congr (atomic_potential_subgradientImage_ae_cells hS hX hr hb h A hA)]
  apply measure_biUnion_finset
  · intro i hi j hj hij
    exact atomicCells_disjoint S X h hij
  · intro i _
    exact atomicCell_measurable hS hSn X h i

def atomicMeasure (X : ι → E n) (mass : ι → ℝ) : Measure (E n) :=
  ∑ i, ENNReal.ofReal (mass i) • Measure.dirac (X i)

lemma atomicMeasure_apply (X : ι → E n) (mass : ι → ℝ) {A : Set (E n)} (hA : MeasurableSet A) :
    atomicMeasure X mass A = ∑ i ∈ atomicNodeIndices X A, ENNReal.ofReal (mass i) := by
  classical
  simp [atomicMeasure, Measure.coe_finset_sum, Measure.dirac_apply' _ hA, atomicNodeIndices, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : X i ∈ A <;> simp [hi]

/-- Every positive finite interior atomic measure is the actual interior
Alexandrov measure of a constructed continuous convex zero-boundary
potential. No Dirichlet existence or regularity theorem is assumed. -/
theorem exists_atomic_dirichlet_solution [NeZero n] {S : Set (E n)}
    (hS : IsCompact S) (hSc : Convex ℝ S)
    (X : ι → E n) (hX : Function.Injective X) (hXi : ∀ i, X i ∈ interior S)
    (mass : ι → ℝ) (hmass : ∀ i, 0 < mass i) :
    ∃ u : E n → ℝ, Continuous u ∧ ConvexOn ℝ univ u ∧
      (∀ x ∈ frontier S, u x = 0) ∧
      ∀ A : Set (E n), MeasurableSet A → A ⊆ interior S →
        volume (subgradientImageOn S u A) = atomicMeasure X mass A := by
  classical
  obtain ⟨h, hpos, hcell⟩ := exists_atomic_cell_heights hS X hX hXi mass hmass
  have hXC : IsCompact (Set.range X) := (Set.finite_range X).isCompact
  have hXI : Set.range X ⊆ interior S := by rintro _ ⟨i, rfl⟩; exact hXi i
  obtain ⟨r, hr, hthick⟩ := hXC.exists_cthickening_subset_open isOpen_interior hXI
  have hb : ∀ i, Metric.closedBall (X i) r ⊆ S := fun i =>
    ((Metric.closedBall_subset_cthickening (Set.mem_range_self i) r).trans hthick).trans interior_subset
  have hSn : S.Nonempty := ⟨X (Classical.arbitrary ι), interior_subset (hXi _)⟩
  refine ⟨atomicDirichletPotential S X h r,
    (atomicDirichletPotential_lipschitz hS hSn X h hr).continuous,
    atomicDirichletPotential_convex hS hSn X h hr,
    atomicDirichletPotential_boundary hS hSn hSc hr hb h, ?_⟩
  intro A hAm hAS
  rw [atomicDirichletPotential_image_volume hS hX hr hb h A hAS, atomicMeasure_apply X mass hAm]
  exact Finset.sum_congr rfl (fun i _ => hcell i)

end GaussianTilt.MomentMapRegularity
