import GaussianTilt.MomentMapRegularityGeometry

/-! # The genuine interior Legendre potential

Compact tilted sections provide a finite, attained convex conjugate on the
open target. Fenchel equality and reciprocal gradients are proved directly.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators Gradient
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

def conjugateValues (φ : E n → ℝ) (p : E n) : Set ℝ :=
  Set.range (fun x => inner ℝ p x - φ x)

def conjugate (φ : E n → ℝ) (p : E n) : ℝ := sSup (conjugateValues φ p)

lemma conjugateValues_nonempty (φ : E n → ℝ) (p : E n) :
    (conjugateValues φ p).Nonempty := Set.range_nonempty _

lemma conjugateValues_bddAbove_of_support {φ : E n → ℝ} {p x : E n}
    (hx : ∀ y, φ x + inner ℝ p (y - x) ≤ φ y) :
    BddAbove (conjugateValues φ p) := by
  refine ⟨inner ℝ p x - φ x, ?_⟩
  rintro _ ⟨y, rfl⟩
  have h := hx y
  rw [inner_sub_right] at h
  linarith

lemma conjugate_eq_of_support {φ : E n → ℝ} {p x : E n}
    (hx : ∀ y, φ x + inner ℝ p (y - x) ≤ φ y) :
    conjugate φ p = inner ℝ p x - φ x := by
  apply le_antisymm
  · apply csSup_le (conjugateValues_nonempty φ p)
    rintro _ ⟨y, rfl⟩
    have h := hx y
    rw [inner_sub_right] at h
    linarith
  · exact le_csSup (conjugateValues_bddAbove_of_support hx) ⟨x, rfl⟩

lemma conjugate_fenchel_le {φ : E n → ℝ} {p : E n}
    (hp : BddAbove (conjugateValues φ p)) (x : E n) :
    inner ℝ p x - φ x ≤ conjugate φ p := le_csSup hp ⟨x, rfl⟩

lemma conjugate_convexOn {φ : E n → ℝ} {K : Set (E n)} (hK : Convex ℝ K)
    (hfinite : ∀ p ∈ K, BddAbove (conjugateValues φ p)) :
    ConvexOn ℝ K (conjugate φ) := by
  refine ⟨hK, ?_⟩
  intro p hp q hq a b ha hb hab
  apply csSup_le (conjugateValues_nonempty φ _)
  rintro _ ⟨x, rfl⟩
  have hp' := mul_le_mul_of_nonneg_left (conjugate_fenchel_le (hfinite p hp) x) ha
  have hq' := mul_le_mul_of_nonneg_left (conjugate_fenchel_le (hfinite q hq) x) hb
  simp only [inner_add_left, real_inner_smul_left, smul_eq_mul]
  have hsum : a * φ x + b * φ x = φ x := by nlinarith [congrArg (fun t : ℝ => t * φ x) hab]
  linarith

/-- A supporting vector at a differentiability point must equal the actual
gradient. This also applies to the newly constructed conjugate. -/
lemma supporting_vector_eq_gradient {φ : E n → ℝ} {p x : E n}
    (hd : DifferentiableAt ℝ φ x)
    (hs : ∀ y, φ x + inner ℝ p (y - x) ≤ φ y) : gradient φ x = p := by
  let F : E n → ℝ := fun y => φ y - inner ℝ p y
  have hmin : IsLocalMin F x := by
    apply Filter.Eventually.of_forall
    intro y
    change φ x - inner ℝ p x ≤ φ y - inner ℝ p y
    have h := hs y
    rw [inner_sub_right] at h
    linarith
  have hdF : HasFDerivAt F ((InnerProductSpace.toDual ℝ (E n)) (gradient φ x) -
      innerSL ℝ p) x := hd.hasGradientAt.hasFDerivAt.sub (innerSL ℝ p).hasFDerivAt
  have hz : (InnerProductSpace.toDual ℝ (E n)) (gradient φ x) = innerSL ℝ p := by
    apply sub_eq_zero.mp
    rw [← hdF.fderiv]
    exact hmin.fderiv_eq_zero
  exact (InnerProductSpace.toDual ℝ (E n)).injective hz

/-- The finite convex Legendre potential is genuinely continuous on the
whole open target; attainment is inherited from actual moment transport. -/
theorem conjugate_regular_on_target {φ V : E n → ℝ}
    (hφ : Continuous φ) (hc : ConvexOn ℝ univ φ) {K : Set (E n)}
    (hK : IsOpen K) (hKc : Convex ℝ K) (hV : ContinuousOn V K)
    (hmap : (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x)))).map
      (gradient φ) = volume.withDensity (fun x => ENNReal.ofReal
        (K.indicator (fun y => Real.exp (-V y)) x))) :
    (∀ p ∈ K, BddAbove (conjugateValues φ p)) ∧
      ConvexOn ℝ K (conjugate φ) ∧ ContinuousOn (conjugate φ) K ∧
      ∀ p ∈ K, ∃ x, conjugate φ p = inner ℝ p x - φ x := by
  have hg : Measurable (gradient φ) :=
    (InnerProductSpace.toDual ℝ (E n)).symm.continuous.measurable.comp (measurable_fderiv ℝ φ)
  have hs : ∀ p ∈ K, ∃ x, ∀ y, φ x + inner ℝ p (y - x) ≤ φ y := by
    intro p hp
    exact interior_target_subgradient hφ hc hK hg.aemeasurable
      ((withDensity_absolutelyContinuous volume _).ae_le
        (MomentMapCoercivity.convex_ae_differentiable hc)) hmap
      (fun q hq ε hε => target_ball_pos hK hV hq hε) hp
  have hb : ∀ p ∈ K, BddAbove (conjugateValues φ p) := by
    intro p hp
    obtain ⟨x, hx⟩ := hs p hp
    exact conjugateValues_bddAbove_of_support hx
  have hcv := conjugate_convexOn hKc hb
  refine ⟨hb, hcv, ?_, ?_⟩
  · simpa [hK.interior_eq] using hcv.continuousOn_interior
  · intro p hp
    obtain ⟨x, hx⟩ := hs p hp
    exact ⟨x, conjugate_eq_of_support hx⟩

end GaussianTilt.MomentMapRegularity
