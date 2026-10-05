import GaussianTilt.MomentMapLinearDirichletVariableWeakBootstrapLoads
import GaussianTilt.MomentMapLinearDirichletEuclideanWeakGradient

/-! # Genuine Euclidean Campanato fields in raw weak-boundary coordinates -/
noncomputable section
open Set MeasureTheory Filter Matrix
open scoped Topology ContDiff ENNReal BigOperators
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapRegularity GaussianTilt.MomentMapSchauder
variable {n : ℕ}
set_option maxHeartbeats 1700000
set_option maxSynthPendingDepth 1000

/-- A genuinely constructed continuous Campanato field, with its proved
modulus and AE agreement, becomes the actual coordinate weak-gradient
representative required by normal recovery. -/
theorem exists_coordinate_holder_weak_gradient (u:VolumeJet n)
    {S U:Set (KernelSpace n)} (hS:IsCompact S) {L:KernelSpace n → KernelSpace n}
    (hL:ContinuousOn L S) {β H:ℝ} (hβ:0≤β) (hH:0≤H)
    (hLH:∀x∈S,∀y∈S,‖L x-L y‖≤H*‖x-y‖^β)
    (hLU:∀ᵐ x∂(volume:Measure (KernelSpace n)),x∈U → L x=euclideanWeakGradient u x) :
    ∃q:CoordinateSpace n → CoordinateSpace n,
      BoundedHolderOn β q ((dirichletCoordinateEquiv n).symm ⁻¹' S) ∧
      ContinuousOn q ((dirichletCoordinateEquiv n).symm ⁻¹' S) ∧
      (∀i,∀ᵐ x∂volume,(dirichletCoordinateEquiv n).symm x∈U → q x i=u i.succ x) ∧
      ∀x,q x=dirichletCoordinateEquiv n (L ((dirichletCoordinateEquiv n).symm x)) := by
  obtain ⟨B,hB⟩ := hS.exists_bound_of_continuousOn hL
  have hLH' : BoundedHolderOn β L S := by
    refine ⟨max B 0+H,by positivity,?_,?_⟩
    · intro x hx
      exact (hB x hx).trans ((le_max_left B 0).trans (le_add_of_nonneg_right hH))
    · intro x hx y hy
      exact (hLH x hx y hy).trans (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left (le_max_right B 0)) (Real.rpow_nonneg (norm_nonneg _) β))
  let q := fun x:CoordinateSpace n=>dirichletCoordinateEquiv n (L ((dirichletCoordinateEquiv n).symm x))
  have hh : BoundedHolderOn β q ((dirichletCoordinateEquiv n).symm ⁻¹' S) :=
    (boundedHolderOn_comp_lipschitz hβ hLH'
      (dirichletCoordinateEquiv n).symm.lipschitz.lipschitzOnWith (fun _ hx=>hx)).map
        (dirichletCoordinateEquiv n).toContinuousLinearMap
  have hqc : ContinuousOn q ((dirichletCoordinateEquiv n).symm ⁻¹' S) :=
    (dirichletCoordinateEquiv n).continuous.comp_continuousOn
      (hL.comp (dirichletCoordinateEquiv n).symm.continuous.continuousOn (fun _ hx=>hx))
  refine ⟨q,hh,hqc,?_,fun _=>rfl⟩
  intro i
  have hμ : MeasurePreserving (dirichletCoordinateEquiv n).symm volume volume  := PiLp.volume_preserving_toLp (Fin n)
  filter_upwards [hμ.quasiMeasurePreserving.ae hLU] with x hx hxU
  have hi := congrArg (fun y:KernelSpace n=>y i) (hx hxU)
  simpa only [q,euclideanWeakGradient_apply,ContinuousLinearEquiv.apply_symm_apply] using hi

/-- Uniform positivity of the actual chart quadratic form gives the
strictly positive normal coefficient needed for the true flux recovery. -/
lemma normal_coefficient_lower_of_ellipticity {A:Matrix (Fin n) (Fin n) ℝ} {lam:ℝ}
    (hell:∀z:Fin n → ℝ,lam*(∑i:Fin n,(z i)^2)≤z ⬝ᵥ (A *ᵥ z)) (q:Fin n) : lam≤A q q := by
  have hh := hell (Pi.single q 1)
  simpa [dotProduct,Matrix.mulVec,Pi.single_apply] using hh

end GaussianTilt.MomentMapLinearDirichlet
