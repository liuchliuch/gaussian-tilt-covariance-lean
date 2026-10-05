import GaussianTilt.MomentMapHolderCofactorEllipticity
import GaussianTilt.MomentMapHolderCoordinateOperatorTransport
import GaussianTilt.MomentMapLinearDirichletHolderInterior

/-! # Actual Euclidean cofactor homotopy data for the global boundary estimate

All coefficient constants are fixed before the homotopy parameter and
unknown test jet. The fields are the literal raw Banach cofactor fields
pulled through the canonical coordinate equivalence.
-/
noncomputable section
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 500000
set_option maxSynthPendingDepth 1000
open Set Matrix
open scoped Topology ContDiff BigOperators Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.HolderSpace GaussianTilt.Letwin GaussianTilt.MomentMapRegularity
open GaussianTilt.MomentMapLinearDirichlet GaussianTilt.MomentMapElliptic
variable {n : ℕ} {S A : Set (E n)}

/-- The actual coefficient field seen by the Euclidean boundary chart. -/
def euclideanCofactorHomotopy (d : SmoothInnerDomain S A) (α : ℝ)
    (j : Jet (CoordinateSpace n) ℝ d.coordinate_body_convex α)
    (t : ℝ) (x : E n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i k=>extendValue α (cofactorHomotopyFields d.coordinate_body_convex α j t i k) (coordinateEquiv n x)

lemma coordinate_mem_smooth_body (d : SmoothInnerDomain S A) {x : E n} (hx : x∈d.body) :
    coordinateEquiv n x∈{y | d.coordinateDefining y≤0} := by
  rw [d.coordinate_body_eq]
  exact mem_image_of_mem _ hx

lemma euclideanCofactorHomotopy_value (d : SmoothInnerDomain S A) (α : ℝ)
    (j : Jet (CoordinateSpace n) ℝ d.coordinate_body_convex α) (t : ℝ) {x : E n} (hx : x∈d.body) :
    euclideanCofactorHomotopy d α j t x=
      (1-t) • (1 : Matrix (Fin n) (Fin n) ℝ)+
        t • (hessianMatrix d.coordinate_body_convex α j ⟨coordinateEquiv n x,coordinate_mem_smooth_body d hx⟩).adjugate := by
  rw [← value_cofactorHomotopyFields]
  ext i k
  exact extendValue_mem α _ (coordinate_mem_smooth_body d hx)

/-- At every physical body point the full parameter family is genuinely
continuous; only the explicit cofactor homotopy is used. -/
theorem continuous_euclideanCofactorHomotopy_parameter
    (d : SmoothInnerDomain S A) (α : ℝ)
    (j : Jet (CoordinateSpace n) ℝ d.coordinate_body_convex α) {x : E n} (hx : x∈d.body) :
    Continuous (fun t : ℝ=>euclideanCofactorHomotopy d α j t x) := by
  have he : (fun t : ℝ=>euclideanCofactorHomotopy d α j t x)=
      (fun t : ℝ=>(1-t) • (1 : Matrix (Fin n) (Fin n) ℝ)+
        t • (hessianMatrix d.coordinate_body_convex α j ⟨coordinateEquiv n x,coordinate_mem_smooth_body d hx⟩).adjugate) :=
    funext (fun t=>euclideanCofactorHomotopy_value d α j t hx)
  rw [he]
  fun_prop

theorem euclideanCofactorHomotopy_posDef
    (d : SmoothInnerDomain S A) (α : ℝ)
    (j : Jet (CoordinateSpace n) ℝ d.coordinate_body_convex α)
    (hpd : ∀ x : {y | d.coordinateDefining y≤0},(hessianMatrix d.coordinate_body_convex α j x).PosDef)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) {x : E n} (hx : x∈d.body) :
    (euclideanCofactorHomotopy d α j t x).PosDef := by
  rw [euclideanCofactorHomotopy_value d α j t hx]
  exact posDef_identity_homotopy (posDef_adjugate (hpd _)) ht

/-- The actual Banach coefficient bounds transport with no exponent loss;
the coordinate max norm is bounded by the Euclidean norm. -/
theorem exists_euclideanCofactorHomotopy_uniform_holder_bound
    (d : SmoothInnerDomain S A) {α : ℝ} (hα : 0≤α)
    (j : Jet (CoordinateSpace n) ℝ d.coordinate_body_convex α) :
    ∃ C : ℝ,0≤C ∧ ∀ t∈Icc (0:ℝ) 1,
      (∀ x∈d.body,∀ i k,|euclideanCofactorHomotopy d α j t x i k|≤C) ∧
      (∀ x∈d.body,∀ y∈d.body,∀ i k,
        |euclideanCofactorHomotopy d α j t x i k-euclideanCofactorHomotopy d α j t y i k|≤C*‖x-y‖^α) := by
  obtain ⟨C,hC,hbound⟩ := exists_cofactorHomotopy_uniform_holder_bound d.coordinate_body_convex α j
  refine ⟨C,hC,?_⟩
  intro t ht
  have he (x : E n) (hx : x∈d.body) (i k : Fin n) :
      euclideanCofactorHomotopy d α j t x i k=
        value {y | d.coordinateDefining y≤0} ℝ α (cofactorHomotopyFields d.coordinate_body_convex α j t i k)
          ⟨coordinateEquiv n x,coordinate_mem_smooth_body d hx⟩ :=
    extendValue_mem α _ (coordinate_mem_smooth_body d hx)
  constructor
  · intro x hx i k
    rw [he x hx i k]
    exact (hbound t ht i k).1 _
  · intro x hx y hy i k
    rw [he x hx i k,he y hy i k]
    apply ((hbound t ht i k).2 _ _).trans
    apply mul_le_mul_of_nonneg_left _ hC
    apply Real.rpow_le_rpow dist_nonneg _ hα
    rw [Subtype.dist_eq,dist_eq_norm,← map_sub]
    exact norm_dirichletCoordinateEquiv_le _

/-- One ready-to-use compact-parameter family for the global Dirichlet
Schauder estimate, with all its matrix hypotheses derived. -/
theorem euclideanCofactorHomotopy_global_family
    (d : SmoothInnerDomain S A) {α : ℝ} (hα : 0≤α)
    (j : Jet (CoordinateSpace n) ℝ d.coordinate_body_convex α)
    (hpd : ∀ x : {y | d.coordinateDefining y≤0},(hessianMatrix d.coordinate_body_convex α j x).PosDef) :
    ∃ C : ℝ,0≤C ∧
      (∀ x∈d.body,ContinuousOn (fun t : ℝ=>euclideanCofactorHomotopy d α j t x) (Icc (0:ℝ) 1)) ∧
      (∀ t∈Icc (0:ℝ) 1,∀ x∈d.body,(euclideanCofactorHomotopy d α j t x).PosDef) ∧
      (∀ t∈Icc (0:ℝ) 1,∀ x∈d.body,∀ i k,|euclideanCofactorHomotopy d α j t x i k|≤C) ∧
      (∀ t∈Icc (0:ℝ) 1,∀ x∈d.body,∀ y∈d.body,∀ i k,
        |euclideanCofactorHomotopy d α j t x i k-euclideanCofactorHomotopy d α j t y i k|≤C*‖x-y‖^α) := by
  obtain ⟨C,hC,hbound⟩ := exists_euclideanCofactorHomotopy_uniform_holder_bound d hα j
  exact ⟨C,hC,fun x hx=>(continuous_euclideanCofactorHomotopy_parameter d α j hx).continuousOn,
    fun t ht x hx=>euclideanCofactorHomotopy_posDef d α j hpd ht hx,
    fun t ht=>(hbound t ht).1,fun t ht=>(hbound t ht).2⟩

end GaussianTilt.MomentMapSchauder
