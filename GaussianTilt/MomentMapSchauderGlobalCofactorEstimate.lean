import GaussianTilt.MomentMapSchauderGlobalEstimate
import GaussianTilt.MomentMapSchauderGlobalCofactorFields
import GaussianTilt.MomentMapHolderCofactorBarrier

/-! # The actual uniform cofactor Dirichlet homotopy inverse estimate

This is the global a priori input to linear continuation. It is derived
from the genuine global Schauder estimate and the quadratic C⁰ barrier;
no inverse or surjectivity hypothesis appears here.
-/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 2400000
open Set Matrix
open scoped Topology ContDiff BoundedContinuousFunction
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapLinearDirichlet GaussianTilt.HolderSpace GaussianTilt.MomentMapRegularity GaussianTilt.Letwin
variable {n : ℕ}

/-- One inverse-norm constant is constructed before every homotopy
parameter and every unknown zero-boundary jet. -/
theorem exists_smooth_domain_cofactor_homotopy_uniform_estimate [NeZero n]
    {S A : Set (KernelSpace n)} (d : SmoothInnerDomain S A)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (j : Jet (CoordinateSpace n) ℝ d.coordinate_body_convex α)
    (hpd : ∀ x : {y | d.coordinateDefining y ≤ 0}, (hessianMatrix d.coordinate_body_convex α j x).PosDef) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ k : zeroBoundary (CoordinateSpace n) ℝ d.coordinate_body_convex α,
      ‖k‖ ≤ C*‖ellipticDirichletHomotopy d.coordinate_body_convex α
        (identityFields {y | d.coordinateDefining y ≤ 0} α)
        (cofactorFields {y | d.coordinateDefining y ≤ 0} α (hessianFields d.coordinate_body_convex α j)) t k‖ := by
  obtain ⟨M,hM,hAt,hAp,hAb,hAH⟩ := euclideanCofactorHomotopy_global_family d hα.le j hpd
  have hAs : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ d.body, (euclideanCofactorHomotopy d α j t x).IsSymm := by
    intro t ht x hx
    simpa only [Matrix.IsSymm,Matrix.IsHermitian,Matrix.conjTranspose_eq_transpose_of_trivial] using (hAp t ht x hx).1
  obtain ⟨Cs,hCs,hest⟩ := exists_smooth_domain_global_schauder_estimate isCompact_Icc d hα hα1 hM hM
    (euclideanCofactorHomotopy d α j) hAt hAp hAs hAb hAH
  obtain ⟨B,hB,hbarrier⟩ := exists_cofactorHomotopy_uniform_c0_inverse d.coordinate_body_convex d.coordinate_body_compact hα j hpd
  obtain ⟨Ctrans,D,hCtrans,hD,htransport⟩ := d.exists_coordinate_euclidean_jet_transport hα hα1.le
  refine ⟨D*Cs*(B+2),by positivity,?_⟩
  intro t ht k
  obtain ⟨v,hvn,hkn,hvu,_,_⟩ := htransport k
  let g := ellipticDirichletHomotopy d.coordinate_body_convex α
    (identityFields {y | d.coordinateDefining y ≤ 0} α)
    (cofactorFields {y | d.coordinateDefining y ≤ 0} α (hessianFields d.coordinate_body_convex α j)) t k
  let N := ‖g‖
  have hN : 0 ≤ N := norm_nonneg _
  let f := fun x : KernelSpace n => extendValue α g (coordinateEquiv n x)
  have hvalue : ∀ x : d.body,
      |value d.body ℝ α (jetValue (KernelSpace n) ℝ d.convex_body α v.1) x| ≤ B*N := by
    intro x
    rw [hvu x,extendValue_mem α _ (coordinate_mem_smooth_body d x.2)]
    exact (BoundedContinuousFunction.norm_coe_le_norm
      (value {y | d.coordinateDefining y ≤ 0} ℝ α (jetValue (CoordinateSpace n) ℝ d.coordinate_body_convex α k.1))
      ⟨coordinateEquiv n x,coordinate_mem_smooth_body d x.2⟩).trans (hbarrier t ht k)
  have hf : ∀ x ∈ d.body, |f x| ≤ N := by
    intro x hx
    rw [show f x=value {y | d.coordinateDefining y ≤ 0} ℝ α g
      ⟨coordinateEquiv n x,coordinate_mem_smooth_body d hx⟩ from extendValue_mem α _ (coordinate_mem_smooth_body d hx)]
    exact norm_value_apply_le _ ℝ α g _
  have hfH : ∀ x ∈ d.body, ∀ y ∈ d.body, |f x-f y| ≤ N*‖x-y‖^α := by
    intro x hx y hy
    have he (z : KernelSpace n) (hz : z ∈ d.body) : f z=value {y | d.coordinateDefining y ≤ 0} ℝ α g
        ⟨coordinateEquiv n z,coordinate_mem_smooth_body d hz⟩ := extendValue_mem α _ (coordinate_mem_smooth_body d hz)
    rw [he x hx,he y hy]
    apply (norm_value_sub_le _ ℝ α g _ _).trans
    apply mul_le_mul_of_nonneg_left _ hN
    apply Real.rpow_le_rpow dist_nonneg _ hα.le
    rw [Subtype.dist_eq,dist_eq_norm,← map_sub]
    exact norm_dirichletCoordinateEquiv_le _
  have heq : ∀ x ∈ interior d.body, euclideanEllipticOperator (euclideanCofactorHomotopy d α j t x)
      (extendValue α (jetValue (KernelSpace n) ℝ d.convex_body α v.1)) x=f x := by
    intro x hx
    have hh := d.coordinate_transport_elliptic_equation hα k v hvu
      (cofactorHomotopyFields d.coordinate_body_convex α j t) hx
    simpa only [euclideanCofactorHomotopy,f,g,cofactorHomotopy_operator_eq] using hh
  have hv := hest t ht v f (B*N) N N (mul_nonneg hB hN) hN hN hvalue hf hfH heq
  calc
    ‖k‖ ≤ D*‖v‖ := hkn
    _ ≤ D*(Cs*(B*N+N+N)) := mul_le_mul_of_nonneg_left hv hD
    _ = D*Cs*(B+2)*‖g‖ := by dsimp [N]; ring

end GaussianTilt.MomentMapSchauder
