import GaussianTilt.MomentMapLinearDirichletVariableBoundaryCenters

/-! # Literal natural coefficient and load data for weak boundary regularity -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped Topology ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapSchauder
variable {n : ℕ}

/-- This record contains only actual coefficient bounds and a literal
Hölder modulus. It contains no PDE solvability or regularity conclusion. -/
structure WeakBallCoefficientBounds
    (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ) (KA R lam Λ D β : ℝ) : Prop where
  nonneg : 0 ≤ KA
  measurable : ∀ i k,AEStronglyMeasurable (fun x=>A x i k) volume
  bound : ∀ i k,∀ᵐ x∂volume,|A x i k|≤KA
  positive : ∀ x : KernelSpace n,‖x‖≤R → (A (dirichletCoordinateEquiv n x)).PosDef
  lower : ∀ x : KernelSpace n,‖x‖≤R → ∀ v : KernelSpace n,
    lam*‖v‖^2≤euclideanQuadratic (A (dirichletCoordinateEquiv n x)) v
  upper : ∀ x : KernelSpace n,‖x‖≤R → ∀ v : KernelSpace n,
    euclideanQuadratic (A (dirichletCoordinateEquiv n x)) v≤Λ*‖v‖^2
  holder : ∀ x : KernelSpace n,‖x‖≤R → ∀ y : KernelSpace n,‖y‖≤R → ∀ i k,
    |A (dirichletCoordinateEquiv n x) i k-A (dirichletCoordinateEquiv n y) i k|≤D*‖x-y‖^β

/-- The vector load has a genuine pointwise Hölder representative, related
to its L² class by the displayed actual AE identity. -/
structure WeakHalfBallLoadBounds (j : Fin n) (R β F H : ℝ)
    (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n)))
    (G : Fin n → Lp ℝ 2 (volume : Measure (CoordinateSpace n)))
    (g : KernelSpace n → Fin n → ℝ) : Prop where
  scalar_nonneg : 0 ≤ F
  vector_nonneg : 0 ≤ H
  scalar_bound : ∀ᵐ x∂volume,x∈coordinateHalfBall j R → |f x|≤F
  vector_ae : ∀ i,∀ᵐ x∂volume,x∈coordinateHalfBall j R → G i x=g ((dirichletCoordinateEquiv n).symm x) i
  vector_holder : ∀ x : KernelSpace n,‖x‖≤R → 0≤x j →
    ∀ y : KernelSpace n,‖y‖≤R → 0≤y j → ∀ i,|g x i-g y i|≤H*‖x-y‖^β

lemma WeakBallCoefficientBounds.centered {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    {KA R lam Λ D β : ℝ} (hA : WeakBallCoefficientBounds A KA R lam Λ D β)
    (j : Fin n) (a : KernelSpace n) (ha : ‖a‖≤R) :
    ∀ i k,∀ᵐ x∂volume,x∈coordinateHalfBall j R →
      |A (dirichletCoordinateEquiv n a) i k-A x i k|≤D*‖(dirichletCoordinateEquiv n).symm x-a‖^β := by
  intro i k
  apply ae_of_all
  intro x hx
  have hh := hA.holder ((dirichletCoordinateEquiv n).symm x) hx.1.le a ha i k
  simpa only [ContinuousLinearEquiv.apply_symm_apply,abs_sub_comm] using hh

lemma WeakHalfBallLoadBounds.centered {j : Fin n} {R β F H : ℝ}
    {f : Lp ℝ 2 (volume : Measure (CoordinateSpace n))}
    {G : Fin n → Lp ℝ 2 (volume : Measure (CoordinateSpace n))}
    {g : KernelSpace n → Fin n → ℝ} (hg : WeakHalfBallLoadBounds j R β F H f G g)
    (a : KernelSpace n) (ha : ‖a‖≤R) (haj : 0≤a j) :
    ∀ i,∀ᵐ x∂volume,x∈coordinateHalfBall j R →
      |G i x-g a i|≤H*‖(dirichletCoordinateEquiv n).symm x-a‖^β := by
  intro i
  filter_upwards [hg.vector_ae i] with x hx hxR
  rw [hx hxR]
  exact hg.vector_holder _ hxR.1.le hxR.2.le a ha haj i

end GaussianTilt.MomentMapLinearDirichlet
