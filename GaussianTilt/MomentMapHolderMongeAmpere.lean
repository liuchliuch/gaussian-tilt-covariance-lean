import GaussianTilt.MomentMapHolderDeterminant
import GaussianTilt.MomentMapHolderJetEmbedding
import GaussianTilt.LetwinPositivity

/-! # The genuine Banach-space Monge–Ampère map and its elliptic derivative -/
noncomputable section
open Set Matrix
open scoped Topology BoundedContinuousFunction ContDiff Matrix.Norms.Elementwise
namespace GaussianTilt.HolderSpace
open GaussianTilt.Letwin
variable {n : ℕ}
abbrev Coord := CoordinateSpace n

/-- The coordinate Hessian entry, with the actual order of the two Fréchet arguments. -/
def hessianEntry (i j : Fin n) :
    (Coord (n := n) →L[ℝ] Coord (n := n) →L[ℝ] ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ (Pi.single i 1)).comp
    (ContinuousLinearMap.apply ℝ (Coord (n := n) →L[ℝ] ℝ) (Pi.single j 1))

def hessianFields {S : Set (Coord (n := n))} (hS : Convex ℝ S) (α : ℝ) :
    Jet (Coord (n := n)) ℝ hS α →L[ℝ] (Fin n → Fin n → Space S ℝ α) :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.pi (fun j =>
    (map S (Coord (n := n) →L[ℝ] Coord (n := n) →L[ℝ] ℝ) ℝ α (hessianEntry i j)).comp
      (jetSecond (Coord (n := n)) ℝ hS α)))

def hessianMatrix {S : Set (Coord (n := n))} (hS : Convex ℝ S) (α : ℝ)
    (j : Jet (Coord (n := n)) ℝ hS α) (x : S) : Matrix (Fin n) (Fin n) ℝ :=
  fun i k => value S ℝ α (hessianFields hS α j i k) x

lemma hessianMatrix_eq_actual {S : Set (Coord (n := n))} (hS : Convex ℝ S) {α : ℝ}
    (hα : 0 < α) (j : Jet (Coord (n := n)) ℝ hS α) (x : S) (hx : (x : Coord) ∈ interior S) :
    hessianMatrix hS α j x = coordinateHessian (extendValue α (jetValue Coord ℝ hS α j)) x := by
  ext i k
  rw [coordinateHessian_eq_secondFDerivAt
    ((jet_contDiffOn_two hS hα j).contDiffAt (isOpen_interior.mem_nhds hx)),
    jet_second_eq_fderiv_fderiv hS hα j hx, extendValue_mem α _ x.2]
  rfl

def mongeAmpere {S : Set (Coord (n := n))} (hS : Convex ℝ S) (α : ℝ)
    (j : Jet (Coord (n := n)) ℝ hS α) : Space S ℝ α :=
  determinant S α (hessianFields hS α j)

/-- The actual determinant of the true Hessian is a C∞ map between the
constructed complete function spaces. -/
theorem contDiff_mongeAmpere {S : Set (Coord (n := n))} (hS : Convex ℝ S) (α : ℝ) :
    ContDiff ℝ ∞ (mongeAmpere hS α) :=
  (contDiff_determinant S α).comp (hessianFields hS α).contDiff

lemma value_mongeAmpere {S : Set (Coord (n := n))} (hS : Convex ℝ S) (α : ℝ)
    (j : Jet (Coord (n := n)) ℝ hS α) (x : S) :
    value S ℝ α (mongeAmpere hS α j) x = (hessianMatrix hS α j x).det :=
  value_determinant S α _ x

/-- The Banach-space derivative is the literal cofactor elliptic operator,
with no linearization premise. -/
theorem mongeAmpere_fderiv_apply_value {S : Set (Coord (n := n))} (hS : Convex ℝ S) (α : ℝ)
    (j k : Jet (Coord (n := n)) ℝ hS α) (x : S) :
    value S ℝ α (fderiv ℝ (mongeAmpere hS α) j k) x =
      Matrix.trace ((hessianMatrix hS α j x).adjugate * hessianMatrix hS α k x) := by
  change value S ℝ α (fderiv ℝ (determinant S α ∘ hessianFields hS α) j k) x = _
  rw [fderiv_comp j ((contDiff_infty.mp (contDiff_determinant S α) 1).differentiable le_rfl _)
    (hessianFields hS α).differentiableAt, (hessianFields hS α).fderiv, ContinuousLinearMap.comp_apply]
  exact determinant_fderiv_apply_value S α _ _ x

/-- The affine zero-boundary Dirichlet domain is an actual Banach subspace. -/
def dirichletMongeAmpere {S : Set (Coord (n := n))} (hS : Convex ℝ S) (α : ℝ)
    (base : Jet (Coord (n := n)) ℝ hS α) (j : zeroBoundary (Coord (n := n)) ℝ hS α) : Space S ℝ α :=
  mongeAmpere hS α (base + j.1)

theorem contDiff_dirichletMongeAmpere {S : Set (Coord (n := n))} (hS : Convex ℝ S) (α : ℝ)
    (base : Jet (Coord (n := n)) ℝ hS α) : ContDiff ℝ ∞ (dirichletMongeAmpere hS α base) :=
  (contDiff_mongeAmpere hS α).comp (contDiff_const.add (zeroBoundary Coord ℝ hS α).subtypeL.contDiff)

end GaussianTilt.HolderSpace
