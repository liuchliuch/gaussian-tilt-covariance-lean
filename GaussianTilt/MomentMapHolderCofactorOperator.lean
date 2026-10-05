import GaussianTilt.MomentMapHolderEllipticOperator

/-! # Genuine Hölder cofactor coefficients and the exact MA derivative -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 500000
open Set Matrix
open scoped Topology BigOperators BoundedContinuousFunction ContDiff
namespace GaussianTilt.HolderSpace
variable {n : ℕ}

/-- Cofactors are actual Hölder fields, constructed by the determinant
polynomial after replacing a row. -/
def cofactorFields (X : Type*) [MetricSpace X] (α : ℝ)
    (A : Fin n → Fin n → Space X ℝ α) (i j : Fin n) : Space X ℝ α :=
  determinant X α (Function.update A j (fun k => constant X α ((Pi.single i (1 : ℝ) : Fin n → ℝ) k)))

lemma value_cofactorFields (X : Type*) [MetricSpace X] (α : ℝ)
    (A : Fin n → Fin n → Space X ℝ α) (x : X) (i j : Fin n) :
    value X ℝ α (cofactorFields X α A i j) x =
      (show Matrix (Fin n) (Fin n) ℝ from fun k l => value X ℝ α (A k l) x).adjugate i j := by
  rw [cofactorFields, value_determinant, Matrix.adjugate_apply]
  congr 1
  ext k l
  by_cases hk : k = j
  · subst k
    simp [Matrix.updateRow]
  · simp [Matrix.updateRow, hk]

/-- The actual Fréchet derivative of the zero-boundary Monge–Ampère map is
exactly the constructed cofactor elliptic operator, as a Banach-space map. -/
theorem dirichletMongeAmpere_fderiv_eq_cofactorOperator
    {S : Set (Coord (n := n))} (hS : Convex ℝ S) (α : ℝ)
    (j : zeroBoundary Coord ℝ hS α) :
    fderiv ℝ (dirichletMongeAmpere hS α 0) j =
      ellipticDirichletOperator hS α (cofactorFields S α (hessianFields hS α j.1)) := by
  apply ContinuousLinearMap.ext
  intro k
  apply value_injective S ℝ α
  apply BoundedContinuousFunction.ext
  intro x
  rw [dirichletMongeAmpere_fderiv_apply_value, ellipticDirichletOperator_apply_value]
  simp only [zero_add]
  congr 2
  ext i l
  exact (value_cofactorFields S α (hessianFields hS α j.1) x i l).symm

/-- The identity coefficients are actual constant Hölder fields. -/
def identityFields (X : Type*) [MetricSpace X] (α : ℝ) : Fin n → Fin n → Space X ℝ α :=
  fun i j => constant X α ((1 : Matrix (Fin n) (Fin n) ℝ) i j)

lemma value_identityFields (X : Type*) [MetricSpace X] (α : ℝ) (x : X) :
    (fun i j : Fin n => value X ℝ α (identityFields X α i j) x) = (1 : Matrix (Fin n) (Fin n) ℝ) := rfl

lemma identity_ellipticDirichletOperator_apply_value
    {S : Set (Coord (n := n))} (hS : Convex ℝ S) (α : ℝ)
    (j : zeroBoundary Coord ℝ hS α) (x : S) :
    value S ℝ α (ellipticDirichletOperator hS α (identityFields S α) j) x =
      Matrix.trace (hessianMatrix hS α j.1 x) := by
  rw [ellipticDirichletOperator_apply_value, value_identityFields, Matrix.one_mul]

/-- The cofactor derivative is genuinely bijective after the proved linear
boundary estimate and the actual Laplace starting inverse are supplied. -/
theorem dirichletMongeAmpere_fderiv_bijective_of_uniform_estimate
    {S : Set (Coord (n := n))} (hS : Convex ℝ S) (α : ℝ)
    (j : zeroBoundary Coord ℝ hS α) {C : ℝ} (hC : 0 ≤ C)
    (hestimate : ∀ t ∈ Icc (0 : ℝ) 1, ∀ k : zeroBoundary Coord ℝ hS α,
      ‖k‖ ≤ C * ‖ellipticDirichletHomotopy hS α (identityFields S α)
        (cofactorFields S α (hessianFields hS α j.1)) t k‖)
    (hstart : Function.Surjective (ellipticDirichletOperator hS α (identityFields S α))) :
    Function.Bijective (fderiv ℝ (dirichletMongeAmpere hS α 0) j) := by
  rw [dirichletMongeAmpere_fderiv_eq_cofactorOperator]
  exact ellipticDirichletOperator_bijective_of_uniform_estimate hS α _ _ hC hestimate hstart

end GaussianTilt.HolderSpace
