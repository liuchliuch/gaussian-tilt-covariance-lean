import GaussianTilt.MomentMapLinearDirichletFlatteningOperator

/-! # The actual PDE and zero boundary values in genuine flattened coordinates -/
noncomputable section
open Matrix Set Filter
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapSchauder
variable {n : ℕ}

lemma euclideanEllipticOperator_congr_nhds {u v : KernelSpace n → ℝ} {x : KernelSpace n}
    (he : u =ᶠ[𝓝 x] v) (A : Matrix (Fin n) (Fin n) ℝ) :
    euclideanEllipticOperator A u x = euclideanEllipticOperator A v x := by
  simp only [euclideanEllipticOperator, he.fderiv.fderiv.self_of_nhds]

lemma regularLevelFlatteningChart_hasFDerivAt_inverse {w : KernelSpace n → ℝ}
    (hw : ContDiff ℝ ∞ w) (a : KernelSpace n) (j : Fin n)
    (hj : fderiv ℝ w a (EuclideanSpace.basisFun (Fin n) ℝ j) ≠ 0)
    {z : KernelSpace n} (hz : z ∈ (regularLevelFlatteningChart hw a j hj).target)
    (hn : fderiv ℝ w ((regularLevelFlatteningChart hw a j hj).symm z)
      (EuclideanSpace.basisFun (Fin n) ℝ j) ≠ 0) :
    HasFDerivAt (regularLevelFlatteningChart hw a j hj).symm
      (boundaryRowInverseLinear (-fderiv ℝ w ((regularLevelFlatteningChart hw a j hj).symm z)) j) z := by
  exact (regularLevelFlatteningChart hw a j hj).hasFDerivAt_symm hz
    (f' := flatteningDerivativeEquiv w ((regularLevelFlatteningChart hw a j hj).symm z) j hn)
      (hasFDerivAt_flatteningMap (hw.differentiable (by simp) _) a j)

/-- At every admissible chart point the original local C² function gives
an actual locally C² pullback satisfying the exact transformed PDE. -/
theorem ellipticOperator_flattened_pullback {w u : KernelSpace n → ℝ}
    (hw : ContDiff ℝ ∞ w) (a : KernelSpace n) (j : Fin n)
    (hj : fderiv ℝ w a (EuclideanSpace.basisFun (Fin n) ℝ j) ≠ 0)
    {x : KernelSpace n} (hx : x ∈ (regularLevelFlatteningChart hw a j hj).source)
    (hn : fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ j) ≠ 0)
    (hu : ContDiffAt ℝ 2 u x) (A : Matrix (Fin n) (Fin n) ℝ) :
    let Ψ := regularLevelFlatteningChart hw a j hj
    let v := u ∘ Ψ.symm
    ContDiffAt ℝ 2 v (Ψ x) ∧
      euclideanEllipticOperator A u x =
        euclideanEllipticOperator (flatteningCoefficient A w j x) v (Ψ x) -
          euclideanEllipticOperator A w x * fderiv ℝ v (Ψ x) (EuclideanSpace.basisFun (Fin n) ℝ j) := by
  dsimp only
  let Ψ := regularLevelFlatteningChart hw a j hj
  let v := u ∘ Ψ.symm
  have hz : Ψ x ∈ Ψ.target := Ψ.map_source hx
  have hback : Ψ.symm (Ψ x) = x := Ψ.left_inv hx
  have hnormal : fderiv ℝ w ((regularLevelFlatteningChart hw a j hj).symm (Ψ x))
      (EuclideanSpace.basisFun (Fin n) ℝ j) ≠ 0 := by
    change fderiv ℝ w (Ψ.symm (Ψ x)) (EuclideanSpace.basisFun (Fin n) ℝ j) ≠ 0
    rw [hback]
    exact hn
  have hinv := regularLevelFlatteningChart_inverse_contDiffAt hw a j hj hz hnormal
  have hi2 : ContDiffAt ℝ 2 Ψ.symm (Ψ x) := contDiffAt_infty.mp hinv 2
  have hu_at : ContDiffAt ℝ 2 u (Ψ.symm (Ψ x)) := by rw [hback]; exact hu
  have hv : ContDiffAt ℝ 2 v (Ψ x) := hu_at.comp (Ψ x) hi2
  refine ⟨hv, ?_⟩
  have he : (v ∘ flatteningMap w a j) =ᶠ[𝓝 x] u := by
    filter_upwards [Ψ.open_source.mem_nhds hx] with y hy
    change u (Ψ.symm (flatteningMap w a j y)) = u y
    rw [show flatteningMap w a j y = Ψ y from rfl, Ψ.left_inv hy]
  rw [← euclideanEllipticOperator_congr_nhds he A]
  exact ellipticOperator_comp_flattening_at A a j (contDiff_infty.mp hw 2).contDiffAt hv

/-- Literal zero level-set data pull back to literal zero flat-boundary
data. The inverse's range membership is supplied by the actual chart. -/
theorem flattened_pullback_zero_boundary {w u : KernelSpace n → ℝ}
    (hw : ContDiff ℝ ∞ w) (a : KernelSpace n) (j : Fin n)
    (hj : fderiv ℝ w a (EuclideanSpace.basisFun (Fin n) ℝ j) ≠ 0)
    (hzero : ∀ x ∈ (regularLevelFlatteningChart hw a j hj).source, w x = w a → u x = 0)
    {z : KernelSpace n} (hz : z ∈ (regularLevelFlatteningChart hw a j hj).target) (hzj : z j = 0) :
    u ((regularLevelFlatteningChart hw a j hj).symm z) = 0 := by
  apply hzero _ ((regularLevelFlatteningChart hw a j hj).map_target hz)
  rw [regularLevelFlatteningChart_inverse_level hw a j hj hz, hzj, sub_zero]

end GaussianTilt.MomentMapLinearDirichlet
