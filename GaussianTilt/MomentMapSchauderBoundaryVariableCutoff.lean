import GaussianTilt.MomentMapSchauderBoundaryVariableAbsorption
import GaussianTilt.MomentMapSchauderCutoffForcing
import GaussianTilt.MomentMapSchauderBoundedHolder

/-! # Actual cutoff Hessian fields and the boundary PDE commutator -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 2200000
open Set Filter Matrix
open scoped Topology ContDiff BigOperators
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

def boundaryCutoffSecond (χ u : KernelSpace n → ℝ) (D : KernelSpace n → KernelSpace n →L[ℝ] ℝ)
    (B : KernelSpace n → KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ) (x : KernelSpace n) :
    KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ :=
  χ x • B x+u x • fderiv ℝ (fderiv ℝ χ) x+
    (fderiv ℝ χ x).smulRight (D x)+(D x).smulRight (fderiv ℝ χ x)

lemma secondFrechet_mul_apply_at {u χ : KernelSpace n → ℝ} {x : KernelSpace n}
    (hu : ContDiffAt ℝ 2 u x) (hχ : ContDiff ℝ 2 χ) (v w : KernelSpace n) :
    fderiv ℝ (fderiv ℝ (fun y => χ y*u y)) x v w=
      χ x*fderiv ℝ (fderiv ℝ u) x v w+u x*fderiv ℝ (fderiv ℝ χ) x v w+
      fderiv ℝ χ x v*fderiv ℝ u x w+fderiv ℝ u x v*fderiv ℝ χ x w := by
  obtain ⟨u',hu',he⟩ := exists_global_contDiff_eventuallyEq 2 hu
  have he' : (fun y => χ y*u' y) =ᶠ[𝓝 x] (fun y => χ y*u y) := Filter.EventuallyEq.mul Filter.EventuallyEq.rfl he
  rw [← he'.fderiv.fderiv_eq,secondFrechet_mul_apply hu' hχ,he.fderiv.fderiv_eq,he.fderiv_eq,he.self_of_nhds]

/-- The displayed closure field is exactly the actual product Hessian
where the original fields are actual derivatives. -/
lemma boundaryCutoffSecond_eq_actual {u χ : KernelSpace n → ℝ}
    {D : KernelSpace n → KernelSpace n →L[ℝ] ℝ}
    {B : KernelSpace n → KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ}
    {x : KernelSpace n} (hu : ContDiffAt ℝ 2 u x) (hχ : ContDiff ℝ 2 χ)
    (hD : D x=fderiv ℝ u x) (hB : B x=fderiv ℝ (fderiv ℝ u) x) :
    boundaryCutoffSecond χ u D B x=fderiv ℝ (fderiv ℝ (fun y => χ y*u y)) x := by
  ext v w
  rw [secondFrechet_mul_apply_at hu hχ]
  simp only [boundaryCutoffSecond,hD,hB,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply,smul_eq_mul]

lemma boundaryCutoffSecond_zero_off {u χ : KernelSpace n → ℝ}
    {D : KernelSpace n → KernelSpace n →L[ℝ] ℝ}
    {B : KernelSpace n → KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ}
    {S : Set (KernelSpace n)} (hs : tsupport χ ⊆ S) {x : KernelSpace n} (hx : x ∉ S) :
    boundaryCutoffSecond χ u D B x=0 := by
  obtain ⟨h0,h1,h2⟩ := cutoff_jets_zero_off hs hx
  simp only [boundaryCutoffSecond,h0,h1,h2,zero_smul,smul_zero,add_zero,zero_add]
  ext v w
  simp

/-- Initial finite Hölder regularity of the cutoff Hessian is derived
from the actual three closure fields and the smooth cutoff. -/
lemma boundedHolderOn_boundaryCutoffSecond {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    {S : Set (KernelSpace n)} (hS : IsCompact S) (hSc : Convex ℝ S)
    {u χ : KernelSpace n → ℝ} (hχ : ContDiff ℝ ∞ χ)
    {D : KernelSpace n → KernelSpace n →L[ℝ] ℝ}
    {B : KernelSpace n → KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ}
    (hu : BoundedHolderOn α u S) (hD : BoundedHolderOn α D S) (hB : BoundedHolderOn α B S) :
    BoundedHolderOn α (boundaryCutoffSecond χ u D B) S := by
  have hχ0 := boundedHolderOn_of_contDiff (contDiff_infty.mp hχ 1) hS hSc hα hα1
  have hχ1 := boundedHolderOn_of_contDiff (contDiff_infty.mp (hχ.fderiv_right (m := ∞) (by simp)) 1) hS hSc hα hα1
  have hχ2 := boundedHolderOn_of_contDiff (contDiff_infty.mp
    ((hχ.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)) 1) hS hSc hα hα1
  exact (((hχ0.smul hB).add (hu.smul hχ2)).add
    ((hχ1.map (ContinuousLinearMap.smulRightL ℝ (KernelSpace n) (KernelSpace n →L[ℝ] ℝ))).clm_apply hD)).add
    ((hD.map (ContinuousLinearMap.smulRightL ℝ (KernelSpace n) (KernelSpace n →L[ℝ] ℝ))).clm_apply hχ1)

def boundaryCutoffRemainder (χ u : KernelSpace n → ℝ)
    (D : KernelSpace n → KernelSpace n →L[ℝ] ℝ) (x : KernelSpace n) : Matrix (Fin n) (Fin n) ℝ := fun i k =>
  fderiv ℝ (fderiv ℝ χ) x (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ k)*u x+
    2*(fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ i)*D x (EuclideanSpace.basisFun (Fin n) ℝ k))

/-- The exact commutator contains only the original value and first
field. No derivative of the merely Hölder coefficient is introduced. -/
lemma boundaryCutoffSecond_contraction (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    (χ u : KernelSpace n → ℝ) (D : KernelSpace n → KernelSpace n →L[ℝ] ℝ)
    (B : KernelSpace n → KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ) (x : KernelSpace n) :
    matrixContraction A (bilinearEntryMatrix (boundaryCutoffSecond χ u D B x))=
      χ x*matrixContraction A (bilinearEntryMatrix (B x))+matrixContraction A (boundaryCutoffRemainder χ u D x) := by
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  have hswap : (∑ i, ∑ k, A i k*(D x (e i)*fderiv ℝ χ x (e k)))=
      ∑ i, ∑ k, A i k*(fderiv ℝ χ x (e i)*D x (e k)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    rw [hA.apply i k]
    ring
  simp only [matrixContraction,bilinearEntryMatrix,boundaryCutoffSecond,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.smulRight_apply,smul_eq_mul,mul_add,Finset.sum_add_distrib]
  rw [hswap]
  simp only [boundaryCutoffRemainder,Finset.mul_sum,mul_add,Finset.sum_add_distrib]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

end GaussianTilt.MomentMapSchauder
