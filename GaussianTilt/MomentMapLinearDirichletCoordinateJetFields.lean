import GaussianTilt.MomentMapLinearDirichletTangentialNormalClosed
import GaussianTilt.MomentMapLinearDirichletCoordinates
import GaussianTilt.MomentMapSchauderBoundedHolder

/-! # Genuine raw coordinate rows as first and bilinear derivative fields

The bilinear order is the derivative direction first and evaluation
argument second, exactly as in the Fréchet jet space.
-/
noncomputable section
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 500000
set_option maxSynthPendingDepth 1000
open Set Filter Matrix
open scoped Topology ContDiff BigOperators Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapRegularity GaussianTilt.MomentMapElliptic
variable {n : ℕ}

/-- A literal continuous linear map from the row matrix to the true
bilinear derivative of the coordinate covector field. -/
def coordinateHessianBilinear : Matrix (Fin n) (Fin n) ℝ →L[ℝ]
    (CoordinateSpace n →L[ℝ] CoordinateSpace n →L[ℝ] ℝ) :=
  ∑ k : Fin n, ∑ i : Fin n,
    ((ContinuousLinearMap.proj i : CoordinateSpace n→L[ℝ]ℝ).comp
      (ContinuousLinearMap.proj k : Matrix (Fin n) (Fin n) ℝ→L[ℝ]CoordinateSpace n)).smulRight
      ((ContinuousLinearMap.proj i : CoordinateSpace n→L[ℝ]ℝ).smulRight
        (ContinuousLinearMap.proj k : CoordinateSpace n→L[ℝ]ℝ))

lemma coordinateHessianBilinear_apply (H : Matrix (Fin n) (Fin n) ℝ) (v w : CoordinateSpace n) :
    coordinateHessianBilinear H v w=∑ k : Fin n,∑ i : Fin n,H k i*v i*w k := by
  simp [coordinateHessianBilinear,mul_assoc]
  rfl

lemma coordinateHessianBilinear_eq (H : Matrix (Fin n) (Fin n) ℝ) :
    coordinateHessianBilinear H=coordinateCovector.comp (ContinuousLinearMap.pi (fun k=>coordinateCovector (H k))) := by
  ext v w
  rw [coordinateHessianBilinear_apply,ContinuousLinearMap.comp_apply,coordinateCovector_apply]
  simp only [ContinuousLinearMap.pi_apply,coordinateCovector_apply,Finset.sum_mul]

/-- Actual coordinate-row derivatives give the genuine Fréchet
derivative of the first covector field. -/
theorem hasFDerivAt_coordinateCovector_of_rows
    {G : CoordinateSpace n → CoordinateSpace n} {H : Matrix (Fin n) (Fin n) ℝ} {x : CoordinateSpace n}
    (hd : ∀ k,HasFDerivAt (fun y=>G y k) (coordinateCovector (H k)) x) :
    HasFDerivAt (fun y=>coordinateCovector (G y)) (coordinateHessianBilinear H) x := by
  have hg : HasFDerivAt G (ContinuousLinearMap.pi (fun k=>coordinateCovector (H k))) x :=
    hasFDerivAt_pi.mpr hd
  simpa only [coordinateHessianBilinear_eq,Function.comp_def] using
    (coordinateCovector (n:=n)).hasFDerivAt.comp x hg

/-- The row-to-bilinear conversion also holds for genuine closed-domain
within derivatives, without an extension of the unknown. -/
theorem hasFDerivWithinAt_coordinateCovector_of_rows
    {S : Set (CoordinateSpace n)} {G : CoordinateSpace n → CoordinateSpace n}
    {H : Matrix (Fin n) (Fin n) ℝ} {x : CoordinateSpace n}
    (hd : ∀ k,HasFDerivWithinAt (fun y=>G y k) (coordinateCovector (H k)) S x) :
    HasFDerivWithinAt (fun y=>coordinateCovector (G y)) (coordinateHessianBilinear H) S x := by
  have hg : HasFDerivWithinAt G (ContinuousLinearMap.pi (fun k=>coordinateCovector (H k))) S x :=
    hasFDerivWithinAt_pi.mpr hd
  simpa only [coordinateHessianBilinear_eq,Function.comp_def] using
    (coordinateCovector (n:=n)).hasFDerivAt.comp_hasFDerivWithinAt x hg

section Pullback
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Pull a scalar covector through an actual fixed continuous linear map. -/
def firstFieldLinearPullback (L : E→L[ℝ]F) : (F→L[ℝ]ℝ)→L[ℝ](E→L[ℝ]ℝ) :=
  (ContinuousLinearMap.compL ℝ E F ℝ).flip L

/-- Pull both slots of a bilinear covector through that same linear map. -/
def secondFieldLinearPullback (L : E→L[ℝ]F) : (F→L[ℝ]F→L[ℝ]ℝ)→L[ℝ](E→L[ℝ]E→L[ℝ]ℝ) :=
  (ContinuousLinearMap.compL ℝ E (F→L[ℝ]ℝ) (E→L[ℝ]ℝ) (firstFieldLinearPullback L)).comp
    ((ContinuousLinearMap.compL ℝ E F (F→L[ℝ]ℝ)).flip L)

@[simp] lemma firstFieldLinearPullback_apply (L : E→L[ℝ]F) (D : F→L[ℝ]ℝ) :
    firstFieldLinearPullback L D=D.comp L := rfl

@[simp] lemma secondFieldLinearPullback_apply (L : E→L[ℝ]F) (H : F→L[ℝ]F→L[ℝ]ℝ) (v w : E) :
    secondFieldLinearPullback L H v w=H (L v) (L w) := rfl

lemma secondFieldLinearPullback_eq (L : E→L[ℝ]F) (H : F→L[ℝ]F→L[ℝ]ℝ) :
    secondFieldLinearPullback L H=(firstFieldLinearPullback L).comp (H.comp L) := rfl

end Pullback

/-- Euclidean first field associated with the genuine raw gradient. -/
def euclideanFirstField (G : CoordinateSpace n → CoordinateSpace n) (x : KernelSpace n) :
    KernelSpace n→L[ℝ]ℝ :=
  firstFieldLinearPullback (dirichletCoordinateEquiv n).toContinuousLinearMap
    (coordinateCovector (G (dirichletCoordinateEquiv n x)))

/-- Euclidean second field with the exact derivative/evaluation slot order. -/
def euclideanSecondField (H : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ) (x : KernelSpace n) :
    KernelSpace n→L[ℝ]KernelSpace n→L[ℝ]ℝ :=
  secondFieldLinearPullback (dirichletCoordinateEquiv n).toContinuousLinearMap
    (coordinateHessianBilinear (H (dirichletCoordinateEquiv n x)))

theorem hasFDerivAt_euclidean_value_of_coordinate_field
    {u : CoordinateSpace n→ℝ} {G : CoordinateSpace n → CoordinateSpace n} {x : KernelSpace n}
    (hd : HasFDerivAt u (coordinateCovector (G (dirichletCoordinateEquiv n x))) (dirichletCoordinateEquiv n x)) :
    HasFDerivAt (u ∘ dirichletCoordinateEquiv n) (euclideanFirstField G x) x :=
  hd.comp x (dirichletCoordinateEquiv n).hasFDerivAt

theorem hasFDerivAt_euclidean_first_of_coordinate_rows
    {G : CoordinateSpace n → CoordinateSpace n} {H : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    {x : KernelSpace n}
    (hd : ∀ k,HasFDerivAt (fun y=>G y k) (coordinateCovector (H (dirichletCoordinateEquiv n x) k))
      (dirichletCoordinateEquiv n x)) :
    HasFDerivAt (euclideanFirstField G) (euclideanSecondField H x) x := by
  have hh := (hasFDerivAt_coordinateCovector_of_rows hd).comp x (dirichletCoordinateEquiv n).hasFDerivAt
  exact (firstFieldLinearPullback (dirichletCoordinateEquiv n).toContinuousLinearMap).hasFDerivAt.comp x hh

theorem hasFDerivWithinAt_euclidean_value_of_coordinate_field
    {S : Set (CoordinateSpace n)} {u : CoordinateSpace n→ℝ} {G : CoordinateSpace n → CoordinateSpace n}
    {x : KernelSpace n}
    (hd : HasFDerivWithinAt u (coordinateCovector (G (dirichletCoordinateEquiv n x))) S (dirichletCoordinateEquiv n x)) :
    HasFDerivWithinAt (u ∘ dirichletCoordinateEquiv n) (euclideanFirstField G x) ((dirichletCoordinateEquiv n) ⁻¹' S) x :=
  hd.comp x (dirichletCoordinateEquiv n).hasFDerivAt.hasFDerivWithinAt (fun _ hx=>hx)

theorem hasFDerivWithinAt_euclidean_first_of_coordinate_rows
    {S : Set (CoordinateSpace n)} {G : CoordinateSpace n → CoordinateSpace n}
    {H : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {x : KernelSpace n}
    (hd : ∀ k,HasFDerivWithinAt (fun y=>G y k) (coordinateCovector (H (dirichletCoordinateEquiv n x) k))
      S (dirichletCoordinateEquiv n x)) :
    HasFDerivWithinAt (euclideanFirstField G) (euclideanSecondField H x) ((dirichletCoordinateEquiv n) ⁻¹' S) x := by
  have hh := (hasFDerivWithinAt_coordinateCovector_of_rows hd).comp x
    (dirichletCoordinateEquiv n).hasFDerivAt.hasFDerivWithinAt (fun _ hx=>hx)
  exact (firstFieldLinearPullback (dirichletCoordinateEquiv n).toContinuousLinearMap).hasFDerivAt.comp_hasFDerivWithinAt x hh

end GaussianTilt.MomentMapLinearDirichlet
