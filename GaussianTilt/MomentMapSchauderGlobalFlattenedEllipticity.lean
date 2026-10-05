import GaussianTilt.MomentMapSchauderGlobalFlattenedFields
import GaussianTilt.MomentMapSchauderUniformEllipticity

/-! # Actual symmetry and compact-family center ellipticity in a fixed chart -/
noncomputable section
set_option maxHeartbeats 1500000
open Set Matrix
open scoped Topology ContDiff BigOperators Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapLinearDirichlet
variable {n : ℕ}

/-- The true matrix sandwich preserves pointwise symmetry at every chart
point, independently of any coefficient differentiability. -/
lemma flattenedPrincipal_isSymm
    (w : KernelSpace n→ℝ) (a : KernelSpace n) (q : Fin n) (s : ℝ)
    (ψ : KernelSpace n → KernelSpace n) (A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ)
    (z : KernelSpace n) (hA : (A (ψ z)).IsSymm) :
    (flattenedPrincipal w a q s ψ A z).IsSymm := by
  unfold Matrix.IsSymm flattenedPrincipal
  rw [Matrix.transpose_mul,Matrix.transpose_mul,Matrix.transpose_transpose,hA.eq]
  exact (Matrix.mul_assoc _ _ _).symm

/-- Only continuity of the original coefficient at the fixed physical
center is needed for continuity of the transformed center matrix. -/
lemma continuousOn_flattenedPrincipal_at_zero {T : Type*} [TopologicalSpace T]
    {P : Set T} (w : KernelSpace n→ℝ) (a : KernelSpace n) (q : Fin n) (s : ℝ)
    (ψ : KernelSpace n → KernelSpace n) (hψ0 : ψ 0=a)
    {A : T → KernelSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hA : ContinuousOn (fun t=>A t a) P) :
    ContinuousOn (fun t=>flattenedPrincipal w a q s ψ (A t) 0) P := by
  let J := scaledChartJacobian w a q s ψ 0
  have hc : Continuous (fun M : Matrix (Fin n) (Fin n) ℝ=>J*M*Jᵀ) :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  simpa only [flattenedPrincipal,hψ0] using hc.comp_continuousOn hA

/-- Uniform Euclidean ellipticity is constructed for the entire compact
coefficient family in one fixed boundary chart. No inverse norm bound or
uniform ellipticity estimate is assumed. -/
theorem exists_uniform_flattenedPrincipal_ellipticity_at_zero
    {T : Type*} [TopologicalSpace T] {P : Set T} (hP : IsCompact P)
    {w : KernelSpace n→ℝ} (hw : ContDiff ℝ ∞ w) (a : KernelSpace n) (q : Fin n)
    {s : ℝ} (hs : 0<s) (ψ : KernelSpace n → KernelSpace n) (hψ0 : ψ 0=a)
    {A : T → KernelSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hA : ContinuousOn (fun t=>A t a) P) (hpos : ∀ t∈P,(A t a).PosDef)
    (hq : fderiv ℝ w a (EuclideanSpace.basisFun (Fin n) ℝ q)≠0) :
    ∃ lam Λ : ℝ,0<lam ∧ 0<Λ ∧ ∀ t∈P,∀ v : KernelSpace n,
      lam*‖v‖^2≤euclideanQuadratic (flattenedPrincipal w a q s ψ (A t) 0) v ∧
      euclideanQuadratic (flattenedPrincipal w a q s ψ (A t) 0) v≤Λ*‖v‖^2 := by
  exact exists_uniform_ellipticity_on_compact hP
    (continuousOn_flattenedPrincipal_at_zero w a q s ψ hψ0 hA)
    (fun t ht=>flattenedPrincipal_posDef_at_zero hw a q hs ψ hψ0 (A t) (hpos t ht) hq)

end GaussianTilt.MomentMapSchauder
