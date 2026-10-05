import GaussianTilt.MomentMapLinearDirichletSpace

/-!
# A constructed weak zero-boundary Laplace inverse

The domain energy is proved coercive from the actual Poincaré inequality.
Riesz and the cached proved Lax--Milgram theorem then construct the solution,
its uniqueness and its norm bound. This is the Laplace start of a later
nondivergence-form continuation argument, not an identification of the two
operators.
-/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin
variable {n : ℕ}

/-- The actual weak solution to `-Δu=f` with zero boundary data, constructed
inside the closure of genuine interior-supported smooth test jets. -/
def weakDirichletLaplaceSolution {Ω : Set (CoordinateSpace n)} (i : Fin n)
    {R : ℝ} (hR : 0 ≤ R) (hΩ : ∀ x ∈ Ω, |x i| ≤ R)
    (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n))) : dirichletSobolev Ω :=
  (dirichletEnergy_isCoercive i hR hΩ).continuousLinearEquivOfBilin.symm
    ((InnerProductSpace.toDual ℝ (dirichletSobolev Ω)).symm
      ((innerSL ℝ f).comp (dirichletValue Ω)))

/-- The constructed weak solution satisfies the genuine gradient equation
against every element of the actual zero-boundary Sobolev space. -/
theorem weakDirichletLaplaceSolution_equation {Ω : Set (CoordinateSpace n)} (i : Fin n)
    {R : ℝ} (hR : 0 ≤ R) (hΩ : ∀ x ∈ Ω, |x i| ≤ R)
    (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n))) (v : dirichletSobolev Ω) :
    dirichletEnergy Ω (weakDirichletLaplaceSolution i hR hΩ f) v =
      inner ℝ f (dirichletValue Ω v) := by
  let c := dirichletEnergy_isCoercive i hR hΩ
  let F := (InnerProductSpace.toDual ℝ (dirichletSobolev Ω)).symm
    ((innerSL ℝ f).comp (dirichletValue Ω))
  have he : c.continuousLinearEquivOfBilin (weakDirichletLaplaceSolution i hR hΩ f) = F :=
    c.continuousLinearEquivOfBilin.apply_symm_apply F
  calc
    _ = inner ℝ (c.continuousLinearEquivOfBilin (weakDirichletLaplaceSolution i hR hΩ f)) v :=
      (c.continuousLinearEquivOfBilin_apply _ _).symm
    _ = inner ℝ F v := by rw [he]
    _ = _ := InnerProductSpace.toDual_symm_apply

/-- The actual weak equation, with every derivative coordinate explicit. -/
theorem weakDirichletLaplaceSolution_coordinates {Ω : Set (CoordinateSpace n)} (i : Fin n)
    {R : ℝ} (hR : 0 ≤ R) (hΩ : ∀ x ∈ Ω, |x i| ≤ R)
    (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n))) (v : dirichletSobolev Ω) :
    (∑ j : Fin n, inner ℝ ((weakDirichletLaplaceSolution i hR hΩ f).1 j.succ) (v.1 j.succ)) =
      inner ℝ f (v.1 0) := by
  simpa only [dirichletEnergy_apply] using weakDirichletLaplaceSolution_equation i hR hΩ f v

/-- Uniqueness follows from the proved coercive operator equivalence. -/
theorem weakDirichletLaplaceSolution_unique {Ω : Set (CoordinateSpace n)} (i : Fin n)
    {R : ℝ} (hR : 0 ≤ R) (hΩ : ∀ x ∈ Ω, |x i| ≤ R)
    (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n))) (u : dirichletSobolev Ω)
    (hu : ∀ v : dirichletSobolev Ω, dirichletEnergy Ω u v = inner ℝ f (dirichletValue Ω v)) :
    u = weakDirichletLaplaceSolution i hR hΩ f := by
  let c := dirichletEnergy_isCoercive i hR hΩ
  apply c.continuousLinearEquivOfBilin.injective
  apply ext_inner_right ℝ
  intro v
  rw [c.continuousLinearEquivOfBilin_apply, c.continuousLinearEquivOfBilin_apply, hu,
    weakDirichletLaplaceSolution_equation]

lemma norm_dirichletValue_le (Ω : Set (CoordinateSpace n)) (u : dirichletSobolev Ω) :
    ‖dirichletValue Ω u‖ ≤ ‖u‖ :=
  PiLp.norm_apply_le u.1 0

/-- A genuine quantitative bound for the weak inverse, using the full H¹
norm of its constructed value/gradient jet. -/
theorem norm_weakDirichletLaplaceSolution_le {Ω : Set (CoordinateSpace n)} (i : Fin n)
    {R : ℝ} (hR : 0 ≤ R) (hΩ : ∀ x ∈ Ω, |x i| ≤ R)
    (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n))) :
    ‖weakDirichletLaplaceSolution i hR hΩ f‖ ≤ (1 + 4 * R ^ 2) * ‖f‖ := by
  let u := weakDirichletLaplaceSolution i hR hΩ f
  let D := 1 + 4 * R ^ 2
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have he := weakDirichletLaplaceSolution_equation i hR hΩ f u
  have hh := dirichlet_norm_sq_le_energy i hR hΩ u
  rw [he] at hh
  have hi : inner ℝ f (dirichletValue Ω u) ≤ ‖f‖ * ‖u‖ :=
    (real_inner_le_norm f _).trans (mul_le_mul_of_nonneg_left (norm_dirichletValue_le Ω u) (norm_nonneg f))
  have hbound : ‖u‖ ^ 2 ≤ D * ‖f‖ * ‖u‖ := hh.trans
    ((mul_le_mul_of_nonneg_left hi hD).trans_eq (by ring))
  by_cases hz : ‖u‖ = 0
  · change ‖u‖ ≤ D * ‖f‖
    rw [hz]
    positivity
  · have hp : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    change ‖u‖ ≤ D * ‖f‖
    apply (mul_le_mul_left hp).mp
    nlinarith

/-- Existence and uniqueness of the actual bounded-domain weak zero-boundary
Laplace problem, with no solution or surjectivity supplied as an input. -/
theorem exists_unique_weakDirichletLaplaceSolution {Ω : Set (CoordinateSpace n)} (i : Fin n)
    {R : ℝ} (hR : 0 ≤ R) (hΩ : ∀ x ∈ Ω, |x i| ≤ R)
    (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n))) :
    ∃! u : dirichletSobolev Ω, ∀ v : dirichletSobolev Ω,
      (∑ j : Fin n, inner ℝ (u.1 j.succ) (v.1 j.succ)) = inner ℝ f (v.1 0) := by
  refine ⟨weakDirichletLaplaceSolution i hR hΩ f,
    weakDirichletLaplaceSolution_coordinates i hR hΩ f, ?_⟩
  intro u hu
  apply weakDirichletLaplaceSolution_unique i hR hΩ f u
  intro v
  simpa only [dirichletEnergy_apply] using hu v

/-- The weak Laplace inverse is an actual continuous linear operator. -/
def weakDirichletLaplaceInverse {Ω : Set (CoordinateSpace n)} (i : Fin n)
    {R : ℝ} (hR : 0 ≤ R) (hΩ : ∀ x ∈ Ω, |x i| ≤ R) :
    Lp ℝ 2 (volume : Measure (CoordinateSpace n)) →L[ℝ] dirichletSobolev Ω :=
  LinearMap.mkContinuous
    { toFun := weakDirichletLaplaceSolution i hR hΩ
      map_add' := by
        intro f g
        symm
        apply weakDirichletLaplaceSolution_unique i hR hΩ (f + g)
        intro v
        simp only [map_add, ContinuousLinearMap.add_apply, inner_add_left,
          weakDirichletLaplaceSolution_equation]
      map_smul' := by
        intro c f
        symm
        apply weakDirichletLaplaceSolution_unique i hR hΩ (c • f)
        intro v
        simp only [map_smul, ContinuousLinearMap.smul_apply, real_inner_smul_left,
          weakDirichletLaplaceSolution_equation, smul_eq_mul, RingHom.id_apply] }
    (1 + 4 * R ^ 2) (norm_weakDirichletLaplaceSolution_le i hR hΩ)

/-- Every genuinely bounded domain has a bounded linear weak zero-boundary
Laplace inverse. The strip radius and inverse bound are constructed. -/
theorem exists_bounded_weakDirichletLaplaceInverse [NeZero n]
    {Ω : Set (CoordinateSpace n)} (hΩ : Bornology.IsBounded Ω) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : Lp ℝ 2 (volume : Measure (CoordinateSpace n)) →L[ℝ] dirichletSobolev Ω,
      (∀ f, ‖T f‖ ≤ C * ‖f‖) ∧
      (∀ f (v : dirichletSobolev Ω), (∑ j : Fin n, inner ℝ ((T f).1 j.succ) (v.1 j.succ)) = inner ℝ f (v.1 0)) ∧
      (∀ f (u : dirichletSobolev Ω), (∀ v : dirichletSobolev Ω,
        (∑ j : Fin n, inner ℝ (u.1 j.succ) (v.1 j.succ)) = inner ℝ f (v.1 0)) → u = T f) := by
  obtain ⟨M, hM⟩ := hΩ.exists_norm_le
  let R := |M| + 1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hstrip : ∀ x ∈ Ω, |x (0 : Fin n)| ≤ R := by
    intro x hx
    have hi : |x (0 : Fin n)| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x (0 : Fin n)
    have hh := hM x hx
    dsimp [R]
    linarith [le_abs_self M]
  refine ⟨1 + 4 * R ^ 2, by positivity, weakDirichletLaplaceInverse 0 hR hstrip, ?_, ?_, ?_⟩
  · exact norm_weakDirichletLaplaceSolution_le 0 hR hstrip
  · exact weakDirichletLaplaceSolution_coordinates 0 hR hstrip
  · intro f u hu
    apply weakDirichletLaplaceSolution_unique 0 hR hstrip f u
    intro v
    simpa only [dirichletEnergy_apply] using hu v

end GaussianTilt.MomentMapLinearDirichlet
