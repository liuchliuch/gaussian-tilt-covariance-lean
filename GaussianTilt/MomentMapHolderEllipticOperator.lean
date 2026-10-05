import GaussianTilt.MomentMapHolderMongeAmpereInverse
import GaussianTilt.MomentMapClassicalDirichletOperator
import GaussianTilt.MomentMapLinearDirichletContinuation

/-! # Actual Hölder-space elliptic operators and their linear homotopies -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 500000
open Set Matrix
open scoped Topology BigOperators BoundedContinuousFunction ContDiff
namespace GaussianTilt.HolderSpace
open GaussianTilt.Letwin GaussianTilt.MomentMapRegularity
variable {n : ℕ}

def hessianFieldEntryCLM {S : Set (Coord (n := n))} (hS : Convex ℝ S) (α : ℝ)
    (i k : Fin n) : Jet Coord ℝ hS α →L[ℝ] Space S ℝ α :=
  ((ContinuousLinearMap.proj k).comp (ContinuousLinearMap.proj i)).comp (hessianFields hS α)

/-- Literal trace(A D²u) as a bounded operator on the actual Hölder jets. -/
def ellipticJetOperator {S : Set (Coord (n := n))} (hS : Convex ℝ S) (α : ℝ)
    (A : Fin n → Fin n → Space S ℝ α) : Jet Coord ℝ hS α →L[ℝ] Space S ℝ α :=
  ∑ i, ∑ k, (productCLM S α (A i k)).comp (hessianFieldEntryCLM hS α k i)

lemma ellipticJetOperator_apply_value {S : Set (Coord (n := n))} (hS : Convex ℝ S) (α : ℝ)
    (A : Fin n → Fin n → Space S ℝ α) (j : Jet Coord ℝ hS α) (x : S) :
    value S ℝ α (ellipticJetOperator hS α A j) x =
      Matrix.trace ((show Matrix (Fin n) (Fin n) ℝ from fun i k => value S ℝ α (A i k) x) * hessianMatrix hS α j x) := by
  simp only [ellipticJetOperator, ContinuousLinearMap.sum_apply, map_sum,
    BoundedContinuousFunction.sum_apply, ContinuousLinearMap.comp_apply, productCLM_apply,
    value_product, BoundedContinuousFunction.mul_apply, hessianFieldEntryCLM,
    ContinuousLinearMap.proj_apply, hessianMatrix, Matrix.trace, Matrix.diag, Matrix.mul_apply]

def ellipticDirichletOperator {S : Set (Coord (n := n))} (hS : Convex ℝ S) (α : ℝ)
    (A : Fin n → Fin n → Space S ℝ α) : zeroBoundary Coord ℝ hS α →L[ℝ] Space S ℝ α :=
  (ellipticJetOperator hS α A).comp (zeroBoundary Coord ℝ hS α).subtypeL

lemma ellipticDirichletOperator_apply_value {S : Set (Coord (n := n))} (hS : Convex ℝ S) (α : ℝ)
    (A : Fin n → Fin n → Space S ℝ α) (j : zeroBoundary Coord ℝ hS α) (x : S) :
    value S ℝ α (ellipticDirichletOperator hS α A j) x =
      Matrix.trace ((show Matrix (Fin n) (Fin n) ℝ from fun i k => value S ℝ α (A i k) x) * hessianMatrix hS α j.1 x) :=
  ellipticJetOperator_apply_value hS α A j.1 x

lemma ellipticDirichletOperator_eq_actual {S : Set (Coord (n := n))} (hS : Convex ℝ S)
    {α : ℝ} (hα : 0 < α) (A : Fin n → Fin n → Space S ℝ α)
    (j : zeroBoundary Coord ℝ hS α) (x : S) (hx : (x : Coord) ∈ interior S) :
    value S ℝ α (ellipticDirichletOperator hS α A j) x =
      linearizedMA (show Matrix (Fin n) (Fin n) ℝ from fun i k => value S ℝ α (A i k) x)
        (extendValue α (jetValue Coord ℝ hS α j.1)) x := by
  rw [ellipticDirichletOperator_apply_value, hessianMatrix_eq_actual hS hα j.1 x hx]
  rfl

/-- The actual straight-line path in bounded operator norm. -/
def ellipticDirichletHomotopy {S : Set (Coord (n := n))} (hS : Convex ℝ S) (α : ℝ)
    (A B : Fin n → Fin n → Space S ℝ α) (t : ℝ) :
    zeroBoundary Coord ℝ hS α →L[ℝ] Space S ℝ α :=
  (1-t) • ellipticDirichletOperator hS α A + t • ellipticDirichletOperator hS α B

lemma continuous_ellipticDirichletHomotopy {S : Set (Coord (n := n))} (hS : Convex ℝ S) (α : ℝ)
    (A B : Fin n → Fin n → Space S ℝ α) : Continuous (ellipticDirichletHomotopy hS α A B) := by
  letI : NormedSpace ℝ (zeroBoundary (Coord (n := n)) ℝ hS α) :=
    Submodule.normedSpace (zeroBoundary (Coord (n := n)) ℝ hS α)
  unfold ellipticDirichletHomotopy
  exact ((continuous_const.sub continuous_id).smul continuous_const).add
    (continuous_id.smul continuous_const)

lemma ellipticDirichletHomotopy_apply_value {S : Set (Coord (n := n))} (hS : Convex ℝ S) (α : ℝ)
    (A B : Fin n → Fin n → Space S ℝ α) (t : ℝ)
    (j : zeroBoundary Coord ℝ hS α) (x : S) :
    value S ℝ α (ellipticDirichletHomotopy hS α A B t j) x =
      Matrix.trace (((1-t) • (show Matrix (Fin n) (Fin n) ℝ from fun i k => value S ℝ α (A i k) x) +
        t • (show Matrix (Fin n) (Fin n) ℝ from fun i k => value S ℝ α (B i k) x)) * hessianMatrix hS α j.1 x) := by
  simp only [ellipticDirichletHomotopy, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    map_add, map_smul, BoundedContinuousFunction.add_apply, BoundedContinuousFunction.smul_apply,
    ellipticDirichletOperator_apply_value, Matrix.add_mul, Matrix.smul_mul,
    Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]

/-- Once the actual global boundary estimate is established, the starting
inverse propagates to the target elliptic operator without a solvability premise. -/
theorem ellipticDirichletOperator_bijective_of_uniform_estimate
    {S : Set (Coord (n := n))} (hS : Convex ℝ S) (α : ℝ)
    (A B : Fin n → Fin n → Space S ℝ α) {C : ℝ} (hC : 0 ≤ C)
    (hestimate : ∀ t ∈ Icc (0 : ℝ) 1, ∀ j : zeroBoundary Coord ℝ hS α,
      ‖j‖ ≤ C * ‖ellipticDirichletHomotopy hS α A B t j‖)
    (hstart : Function.Surjective (ellipticDirichletOperator hS α A)) :
    Function.Bijective (ellipticDirichletOperator hS α B) := by
  letI : NormedSpace ℝ (zeroBoundary (Coord (n := n)) ℝ hS α) :=
    Submodule.normedSpace (zeroBoundary (Coord (n := n)) ℝ hS α)
  have h := GaussianTilt.MomentMapLinearDirichlet.linear_dirichlet_method_of_continuity
    (X := zeroBoundary (Coord (n := n)) ℝ hS α) (Y := Space S ℝ α)
    (ellipticDirichletHomotopy hS α A B) (continuous_ellipticDirichletHomotopy hS α A B)
    hC hestimate (by simpa only [ellipticDirichletHomotopy, sub_zero, one_smul, zero_smul, add_zero] using hstart)
    1 (by norm_num)
  simpa only [ellipticDirichletHomotopy, sub_self, zero_smul, one_smul, zero_add] using h

end GaussianTilt.HolderSpace
