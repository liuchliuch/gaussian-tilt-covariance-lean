import GaussianTilt.MomentMapRegularityDirichletAtomicEuler

/-! # The actual finite atomic zero-boundary Dirichlet potential

A finite-ball Legendre transform of the solved slope envelope is a globally
finite convex Lipschitz function. Interior atomic cells lie strictly inside
the truncating ball; at its boundary only the original body support remains.
This yields the zero boundary values without assuming a Dirichlet solution.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators Gradient ENNReal NNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}
variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

lemma domainConjugate_lipschitz {S : Set (E n)} (hS : IsCompact S) (hSn : S.Nonempty)
    {u : E n → ℝ} (hu : ContinuousOn u S) {R : ℝ} (hR : ∀ p ∈ S, ‖p‖ ≤ R) :
    LipschitzWith R.toNNReal (domainConjugate S u) := by
  have hone (x y : E n) : domainConjugate S u x ≤ domainConjugate S u y + R * ‖x - y‖ := by
    apply csSup_le (domainConjugateValues_nonempty hSn _ _)
    rintro _ ⟨p, hp, rfl⟩
    have hfen := domainConjugate_fenchel_le hS hu y hp
    have hi := real_inner_le_norm (x - y) p
    have hn := mul_le_mul_of_nonneg_left (hR p hp) (norm_nonneg (x - y))
    rw [inner_sub_left] at hi
    nlinarith
  apply LipschitzWith.of_dist_le'
  intro x y
  rw [Real.dist_eq, dist_eq_norm, abs_sub_le_iff]
  have hx := hone x y
  have hy := hone y x
  rw [norm_sub_rev y x] at hy
  constructor <;> linarith

lemma truncated_conjugate_reciprocal {g : E n → ℝ} {B : ℝ} (hB : 0 < B)
    (hg : Continuous g) {p x : E n} (hp : p ∈ Metric.closedBall 0 B)
    (hs : SupportsAt g x p) :
    domainConjugate (Metric.closedBall 0 B) g x = inner ℝ x p - g p ∧
      SupportsAt (domainConjugate (Metric.closedBall 0 B) g) p x := by
  have he := domainConjugate_eq_of_support hp (supportsOn_of_supportsAt hs)
  refine ⟨he, fun y => ?_⟩
  rw [he, inner_sub_right]
  have hf := domainConjugate_fenchel_le (isCompact_closedBall _ _) hg.continuousOn y hp
  linarith [real_inner_comm x p, real_inner_comm y p]

lemma truncated_conjugate_support_iff_gradient {g : E n → ℝ} {B : ℝ} (hB : 0 < B)
    (hgc : ConvexOn ℝ univ g) (hg : Continuous g) {p x : E n}
    (hp : p ∈ Metric.ball 0 B) (hd : DifferentiableAt ℝ g p) :
    SupportsAt (domainConjugate (Metric.closedBall 0 B) g) p x ↔ x = gradient g p := by
  have hrec := truncated_conjugate_reciprocal hB hg (Metric.ball_subset_closedBall hp)
    (convex_gradient_support hgc hd)
  constructor
  · intro hs
    apply Eq.symm
    apply supporting_vector_eq_gradient_of_eventually hd
    filter_upwards [Metric.isOpen_ball.mem_nhds hp] with q hq
    have hfen := domainConjugate_fenchel_le (isCompact_closedBall (0 : E n) B)
      hg.continuousOn x (Metric.ball_subset_closedBall hq)
    have h1 := hs (gradient g p)
    have h2 := hrec.2 x
    rw [hrec.1] at h1 h2
    simp only [inner_sub_right] at h1 h2 ⊢
    linarith [real_inner_comm x p, real_inner_comm x q, real_inner_comm (gradient g p) p]
  · rintro rfl
    exact hrec.2

def atomicSlopeRadius (h : ι → ℝ) (r : ℝ) : ℝ := (‖h‖ + 1) / r

def atomicDirichletPotential (S : Set (E n)) (X : ι → E n) (h : ι → ℝ) (r : ℝ) : E n → ℝ :=
  domainConjugate (Metric.closedBall 0 (atomicSlopeRadius h r)) (atomicLift S X h)

lemma atomicSlopeRadius_pos (h : ι → ℝ) {r : ℝ} (hr : 0 < r) : 0 < atomicSlopeRadius h r := by
  unfold atomicSlopeRadius
  positivity

lemma atomicLift_continuous {S : Set (E n)} (hS : IsCompact S) (hSn : S.Nonempty)
    (X : ι → E n) (h : ι → ℝ) : Continuous (atomicLift S X h) :=
  continuousOn_univ.mp ((atomicLift_convex hS hSn X h).continuousOn isOpen_univ)

lemma atomicDirichletPotential_lipschitz {S : Set (E n)} (hS : IsCompact S) (hSn : S.Nonempty)
    (X : ι → E n) (h : ι → ℝ) {r : ℝ} (hr : 0 < r) :
    LipschitzWith (atomicSlopeRadius h r).toNNReal (atomicDirichletPotential S X h r) :=
  domainConjugate_lipschitz (isCompact_closedBall _ _)
    ⟨0, Metric.mem_closedBall_self (atomicSlopeRadius_pos h hr).le⟩
    (atomicLift_continuous hS hSn X h).continuousOn (fun p hp => by simpa using hp)

lemma atomicDirichletPotential_convex {S : Set (E n)} (hS : IsCompact S) (hSn : S.Nonempty)
    (X : ι → E n) (h : ι → ℝ) {r : ℝ} (hr : 0 < r) :
    ConvexOn ℝ univ (atomicDirichletPotential S X h r) :=
  domainConjugate_convex (isCompact_closedBall _ _)
    ⟨0, Metric.mem_closedBall_self (atomicSlopeRadius_pos h hr).le⟩
    (atomicLift_continuous hS hSn X h).continuousOn

lemma atomicDirichletPotential_nonpos_on {S : Set (E n)} (hS : IsCompact S)
    (X : ι → E n) (h : ι → ℝ) {r : ℝ} (hr : 0 < r) {x : E n} (hx : x ∈ S) :
    atomicDirichletPotential S X h r x ≤ 0 := by
  apply csSup_le (domainConjugateValues_nonempty
    ⟨0, Metric.mem_closedBall_self (atomicSlopeRadius_pos h hr).le⟩ _ _)
  rintro _ ⟨p, hp, rfl⟩
  have hi := (boundarySupport_ge_inner hS hx p).trans (atomicLift_ge_boundary S X h p)
  linarith [real_inner_comm x p]

lemma atomicDirichletPotential_pos_off {S : Set (E n)} (hS : IsCompact S) (hSn : S.Nonempty)
    (hSc : Convex ℝ S) {X : ι → E n} {r : ℝ} (hr : 0 < r)
    (hb : ∀ i, Metric.closedBall (X i) r ⊆ S) (h : ι → ℝ) {x : E n} (hx : x ∉ S) :
    0 < atomicDirichletPotential S X h r x := by
  obtain ⟨f, a, hfa, hax⟩ := geometric_hahn_banach_closed_point hSc hS.isClosed hx
  let v : E n := (InnerProductSpace.toDual ℝ (E n)).symm f
  have hfv (y : E n) : inner ℝ v y = f y := by
    change (InnerProductSpace.toDual ℝ (E n)) v y = f y
    simp [v]
  have hv : v ≠ 0 := by
    intro hv0
    obtain ⟨z, hz⟩ := hSn
    have hx0 := hfv x
    have hz0 := hfv z
    rw [hv0, inner_zero_left] at hx0 hz0
    linarith [hfa z hz]
  let B := atomicSlopeRadius h r
  have hB : 0 < B := atomicSlopeRadius_pos h hr
  let q := (B / ‖v‖) • v
  have hqnorm : ‖q‖ = B := by
    rw [show q = (B / ‖v‖) • v from rfl, norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos hB (norm_pos_iff.mpr hv))]
    exact div_mul_cancel₀ B (norm_ne_zero_iff.mpr hv)
  have hq : q ∈ Metric.closedBall (0 : E n) B := by simpa using hqnorm.le
  have hexc : atomicExcess S X h q = 0 := by
    apply atomicExcess_eq_zero_outside hS hr hb h
    rw [hqnorm]
    dsimp [B, atomicSlopeRadius]
    exact div_lt_div_of_pos_right (by linarith) hr
  have hqval : atomicLift S X h q = boundarySupport S q := by rw [atomicLift_eq_boundary_add_excess, hexc, add_zero]
  obtain ⟨z, hz, hsz⟩ := boundarySupport_attained hS hSn q
  have hsep : inner ℝ q z < inner ℝ q x := by
    simp only [q, real_inner_smul_left, hfv]
    exact mul_lt_mul_of_pos_left ((hfa z hz).trans hax) (div_pos hB (norm_pos_iff.mpr hv))
  have hfen := domainConjugate_fenchel_le (isCompact_closedBall (0 : E n) B)
    (atomicLift_continuous hS hSn X h).continuousOn x hq
  rw [hqval, hsz] at hfen
  change 0 < domainConjugate (Metric.closedBall 0 B) (atomicLift S X h) x
  linarith [real_inner_comm x q]

/-- Zero boundary values are proved using separation outside the body and
continuity, rather than inserted into the finite potential's definition. -/
theorem atomicDirichletPotential_boundary {S : Set (E n)} (hS : IsCompact S) (hSn : S.Nonempty)
    (hSc : Convex ℝ S) {X : ι → E n} {r : ℝ} (hr : 0 < r)
    (hb : ∀ i, Metric.closedBall (X i) r ⊆ S) (h : ι → ℝ) :
    ∀ x ∈ frontier S, atomicDirichletPotential S X h r x = 0 := by
  have hu := (atomicDirichletPotential_lipschitz hS hSn X h hr).continuous
  have hcl : closure Sᶜ ⊆ {x | 0 ≤ atomicDirichletPotential S X h r x} := by
    apply closure_minimal
    · intro x hx
      exact (atomicDirichletPotential_pos_off hS hSn hSc hr hb h hx).le
    · exact isClosed_le continuous_const hu
  intro x hx
  apply le_antisymm (atomicDirichletPotential_nonpos_on hS X h hr (hS.isClosed.frontier_subset hx))
  apply hcl
  exact (show x ∈ closure S ∩ closure Sᶜ from (frontier_eq_closure_inter_closure (s := S)) ▸ hx).2

end GaussianTilt.MomentMapRegularity
