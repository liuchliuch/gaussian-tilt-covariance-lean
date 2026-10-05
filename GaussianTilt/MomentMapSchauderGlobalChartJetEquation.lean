import GaussianTilt.MomentMapSchauderGlobalFlattenedEquation
import GaussianTilt.MomentMapSchauderGlobalPatchGeometry
import GaussianTilt.MomentMapSchauderBoundaryVariableJetEstimate

/-! # Genuine closed-jet equation in the actual curved boundary chart -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 2400000
open Set Filter Matrix
open scoped Topology ContDiff BigOperators
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapLinearDirichlet GaussianTilt.HolderSpace
variable {n : ℕ}

lemma flattenedDrift_eq (w : KernelSpace n → ℝ) (j : Fin n) (s : ℝ)
    (ψ : KernelSpace n → KernelSpace n) (A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ)
    (z : KernelSpace n) : flattenedDrift w j s ψ A z=
      (-s⁻¹*euclideanEllipticOperator (A (ψ z)) w (ψ z)) • EuclideanSpace.basisFun (Fin n) ℝ j := by
  unfold flattenedDrift
  congr 1
  simp only [scaledChartCurvature,matrixContraction,euclideanEllipticOperator,
    euclideanHessianMatrix,Matrix.smul_apply,smul_eq_mul,Finset.mul_sum,neg_mul,Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The PDE is transferred using the true local inverse and actual
interior derivatives. Continuity then gives the stored-field equation
on the entire closed half-ball, including the plane. -/
theorem chart_jet_flattened_equation
    {S O : Set (KernelSpace n)} (hS : Convex ℝ S) (hO : IsOpen O)
    {α : ℝ} (hα : 0 < α) (J : Jet (KernelSpace n) ℝ hS α)
    (q : Fin n) (V : Jet (KernelSpace n) ℝ (convex_flatClosedPatch q 1) α)
    {w : KernelSpace n → ℝ} (hw : ContDiff ℝ ∞ w) (a : KernelSpace n) (s : ℝ)
    {ψ : KernelSpace n → KernelSpace n}
    (hmap : MapsTo ψ (interior (flatClosedPatch q 1)) (interior S))
    (hsource : ∀ z ∈ Metric.closedBall (0 : KernelSpace n) 1, ψ z ∈ O)
    (hright : ∀ z ∈ Metric.closedBall (0 : KernelSpace n) 1, scaledFlatteningMap w a q s (ψ z)=z)
    (hleft : ∀ x ∈ O, ‖scaledFlatteningMap w a q s x‖ ≤ 1 → ψ (scaledFlatteningMap w a q s x)=x)
    (hvalue : ∀ z : flatClosedPatch q 1,
      value (flatClosedPatch q 1) ℝ α (jetValue (KernelSpace n) ℝ (convex_flatClosedPatch q 1) α V) z=
        extendValue α (jetValue (KernelSpace n) ℝ hS α J) (ψ z))
    (A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ) (f : KernelSpace n → ℝ)
    (hAc : ∀ i k, ContinuousOn (fun z => flattenedPrincipal w a q s ψ A z i k) (flatClosedPatch q 1))
    (hbc : ContinuousOn (flattenedDrift w q s ψ A) (flatClosedPatch q 1))
    (hfc : ContinuousOn (f ∘ ψ) (flatClosedPatch q 1))
    (heq : ∀ x ∈ interior S,
      euclideanEllipticOperator (A x) (extendValue α (jetValue (KernelSpace n) ℝ hS α J)) x=f x) :
    ∀ z ∈ flatClosedPatch q 1,
      matrixContraction (flattenedPrincipal w a q s ψ A z)
        (bilinearEntryMatrix (flatJetSecond q 1 α V z))+
        flatJetFirst q 1 α V z (flattenedDrift w q s ψ A z)=f (ψ z) := by
  let u := extendValue α (jetValue (KernelSpace n) ℝ hS α J)
  let v := extendValue α (jetValue (KernelSpace n) ℝ (convex_flatClosedPatch q 1) α V)
  apply closed_jet_equation_of_interior (convex_flatClosedPatch q 1)
    (isCompact_flatClosedPatch q 1).isClosed (flatClosedPatch_nonempty_interior q zero_lt_one)
    hα V _ _ (f ∘ ψ) hAc hbc hfc
  intro z hz
  have hzS : z ∈ flatClosedPatch q 1 := interior_subset hz
  have hpz : scaledFlatteningMap w a q s (ψ z)=z := hright z hzS.1
  have hN : u =ᶠ[𝓝 (ψ z)] (v ∘ scaledFlatteningMap w a q s) :=
    chart_value_recovery_germ hO (contDiff_scaledFlatteningMap hw a q s).continuous
      (fun x hx ht => hleft x hx (flat_patch_norm ht))
      (fun y hy => by rw [show v y=value (flatClosedPatch q 1) ℝ α
        (jetValue (KernelSpace n) ℝ (convex_flatClosedPatch q 1) α V) ⟨y,hy⟩ from extendValue_mem α _ hy]; exact hvalue ⟨y,hy⟩)
      (hsource z hzS.1) (by rwa [hpz])
  have hv : ContDiffAt ℝ 2 v (scaledFlatteningMap w a q s (ψ z)) := by
    rw [hpz]
    exact (jet_contDiffOn_two (convex_flatClosedPatch q 1) hα V).contDiffAt (isOpen_interior.mem_nhds hz)
  have hc := ellipticOperator_comp_scaled_flattening_at (A (ψ z)) a q s
    (contDiff_infty.mp hw 2).contDiffAt hv
  have hLu : euclideanEllipticOperator (A (ψ z)) u (ψ z)=
      euclideanEllipticOperator (A (ψ z)) (v ∘ scaledFlatteningMap w a q s) (ψ z) := by
    unfold euclideanEllipticOperator
    rw [hN.fderiv.fderiv_eq]
  have hf := heq (ψ z) (hmap hz)
  change euclideanEllipticOperator (A (ψ z)) u (ψ z)=f (ψ z) at hf
  rw [hLu,hc,hpz] at hf
  rw [flattenedPrincipal_eq hw,flattenedDrift_eq]
  exact hf

end GaussianTilt.MomentMapSchauder
