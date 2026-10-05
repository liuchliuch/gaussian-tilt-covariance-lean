import GaussianTilt.MomentMapLinearDirichletCoordinateJetFields
import GaussianTilt.MomentMapLinearDirichletHolderInterior

/-! # Exact-exponent Euclidean Hölder transfer of actual coordinate jet fields -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 500000
set_option maxSynthPendingDepth 1000
open Set Filter Matrix
open scoped Topology ContDiff BigOperators Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapRegularity GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapSchauder
variable {n : ℕ}

/-- Passing from Euclidean coordinates to the raw max-norm coordinates
has norm at most one, so the forcing exponent is retained exactly. -/
lemma boundedHolderOn_comp_coordinateEquiv {F : Type*} [NormedAddCommGroup F]
    {S : Set (CoordinateSpace n)} {g : CoordinateSpace n→F} {α : ℝ} (hα : 0≤α)
    (hg : BoundedHolderOn α g S) :
    BoundedHolderOn α (g ∘ dirichletCoordinateEquiv n) ((dirichletCoordinateEquiv n) ⁻¹' S) := by
  obtain ⟨C,hC,hb,hh⟩ := hg
  refine ⟨C,hC,fun x hx=>hb _ hx,?_⟩
  intro x hx y hy
  apply (hh _ hx _ hy).trans
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.rpow_le_rpow (norm_nonneg _) _ hα
  change ‖dirichletCoordinateEquiv n x-dirichletCoordinateEquiv n y‖≤‖x-y‖
  rw [← map_sub]
  exact norm_dirichletCoordinateEquiv_le _

lemma continuousOn_euclideanFirstField {S : Set (CoordinateSpace n)}
    {G : CoordinateSpace n → CoordinateSpace n} (hG : ContinuousOn G S) :
    ContinuousOn (euclideanFirstField G) ((dirichletCoordinateEquiv n) ⁻¹' S) :=
  (firstFieldLinearPullback (dirichletCoordinateEquiv n).toContinuousLinearMap).continuous.comp_continuousOn
    ((coordinateCovector (n:=n)).continuous.comp_continuousOn
      (hG.comp (dirichletCoordinateEquiv n).continuous.continuousOn (fun _ hx=>hx)))

lemma continuousOn_euclideanSecondField {S : Set (CoordinateSpace n)}
    {H : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} (hH : ContinuousOn H S) :
    ContinuousOn (euclideanSecondField H) ((dirichletCoordinateEquiv n) ⁻¹' S) :=
  (secondFieldLinearPullback (dirichletCoordinateEquiv n).toContinuousLinearMap).continuous.comp_continuousOn
    ((coordinateHessianBilinear (n:=n)).continuous.comp_continuousOn
      (hH.comp (dirichletCoordinateEquiv n).continuous.continuousOn (fun _ hx=>hx)))

/-- The first Euclidean covector field inherits the actual same-exponent
bounded Hölder modulus from the raw first-gradient representative. -/
theorem boundedHolderOn_euclideanFirstField {S : Set (CoordinateSpace n)}
    {G : CoordinateSpace n → CoordinateSpace n} {α : ℝ} (hα : 0≤α)
    (hG : BoundedHolderOn α G S) :
    BoundedHolderOn α (euclideanFirstField G) ((dirichletCoordinateEquiv n) ⁻¹' S) :=
  ((boundedHolderOn_comp_coordinateEquiv hα hG).map (coordinateCovector (n:=n))).map
    (firstFieldLinearPullback (dirichletCoordinateEquiv n).toContinuousLinearMap)

/-- The true bilinear second Euclidean field inherits the same exponent,
with both coordinate slots transferred by actual continuous linear maps. -/
theorem boundedHolderOn_euclideanSecondField {S : Set (CoordinateSpace n)}
    {H : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {α : ℝ} (hα : 0≤α)
    (hH : BoundedHolderOn α H S) :
    BoundedHolderOn α (euclideanSecondField H) ((dirichletCoordinateEquiv n) ⁻¹' S) :=
  ((boundedHolderOn_comp_coordinateEquiv hα hH).map (coordinateHessianBilinear (n:=n))).map
    (secondFieldLinearPullback (dirichletCoordinateEquiv n).toContinuousLinearMap)

/-- A pairwise second-field bound in precisely the metric convention of
`JetPatchEmbedding`, obtained from the actual transferred field. -/
theorem exists_euclideanSecondField_holder_bound {S : Set (CoordinateSpace n)}
    {H : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {α : ℝ} (hα : 0≤α)
    (hH : BoundedHolderOn α H S) :
    ∃ C : ℝ,0≤C ∧ ∀ x∈(dirichletCoordinateEquiv n) ⁻¹' S,∀ y∈(dirichletCoordinateEquiv n) ⁻¹' S,
      ‖euclideanSecondField H x-euclideanSecondField H y‖≤C*dist x y^α := by
  obtain ⟨C,hC,_,hh⟩ := boundedHolderOn_euclideanSecondField hα hH
  exact ⟨C,hC,fun x hx y hy=>by simpa only [dist_eq_norm] using hh x hx y hy⟩

end GaussianTilt.MomentMapLinearDirichlet
