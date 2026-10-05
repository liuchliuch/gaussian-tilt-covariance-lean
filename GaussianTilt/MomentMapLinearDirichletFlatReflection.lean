import GaussianTilt.MomentMapLinearDirichletHolderHessian
import GaussianTilt.MomentMapSchauderEuclideanOperator

/-!
# Actual flat reflection geometry and Laplacian covariance

Reflection in a coordinate hyperplane is the genuine measure-preserving
linear isometry. The second Fréchet chain rule proves exact Laplacian
covariance, and reflected compact tests give actual odd zero-boundary
functions. These are the primitives for the flat boundary estimate.
-/
noncomputable section
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 1000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapSchauder
variable {n : ℕ}

def flatReflection (j : Fin n) : KernelSpace n ≃ₗᵢ[ℝ] KernelSpace n :=
  LinearIsometryEquiv.piLpCongrRight 2
    (fun k => if k = j then (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ)
      else LinearIsometryEquiv.refl ℝ ℝ)

lemma flatReflection_apply (j k : Fin n) (x : KernelSpace n) :
    flatReflection j x k = if k = j then -x k else x k := by
  classical
  by_cases hk : k = j
  · subst k
    simp [flatReflection, LinearIsometryEquiv.piLpCongrRight_apply]
  · simp [flatReflection, LinearIsometryEquiv.piLpCongrRight_apply, hk]

lemma flatReflection_involutive (j : Fin n) : Function.Involutive (flatReflection j) := by
  intro x
  ext k
  simp only [flatReflection_apply]
  split_ifs <;> simp

lemma flatReflection_fixed (j : Fin n) {x : KernelSpace n} (hx : x j = 0) : flatReflection j x = x := by
  ext k
  rw [flatReflection_apply]
  split_ifs with h
  · subst k; simp [hx]
  · rfl

lemma flatReflection_basis (j i : Fin n) :
    flatReflection j (EuclideanSpace.basisFun (Fin n) ℝ i) =
      if i = j then -(EuclideanSpace.basisFun (Fin n) ℝ i) else EuclideanSpace.basisFun (Fin n) ℝ i := by
  classical
  ext k
  rw [flatReflection_apply]
  by_cases hi : i = j
  · subst i
    by_cases hk : k = j
    · subst k; simp
    · simp [hk, EuclideanSpace.basisFun_apply, EuclideanSpace.single_apply, Ne.symm hk]
  · by_cases hk : k = j
    · subst k; simp [hi, EuclideanSpace.basisFun_apply, EuclideanSpace.single_apply, Ne.symm hi]
    · simp [hi, hk]

/-- The actual Laplacian is unchanged by coordinate reflection. -/
lemma kernelLaplacian_flatReflection {f : KernelSpace n → ℝ}
    (hf : ContDiff ℝ 2 f) (j : Fin n) (x : KernelSpace n) :
    kernelLaplacian (f ∘ flatReflection j) x = kernelLaplacian f (flatReflection j x) := by
  have hc : ContDiff ℝ 2 (f ∘ flatReflection j) := hf.comp (flatReflection j).toContinuousLinearEquiv.contDiff
  simp only [kernelLaplacian, directionalHessian_eq_fderiv_fderiv hc,
    directionalHessian_eq_fderiv_fderiv hf]
  have he := secondFrechet_comp_linear hf (flatReflection j).toContinuousLinearEquiv.toContinuousLinearMap x
  change fderiv ℝ (fderiv ℝ (f ∘ flatReflection j)) x = _ at he
  rw [he]
  simp only [ContinuousLinearMap.bilinearComp_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe]
  apply Finset.sum_congr rfl
  intro i _
  rw [flatReflection_basis]
  split_ifs <;> simp

def oddReflectionTest (j : Fin n) (ψ : KernelSpace n → ℝ) (x : KernelSpace n) : ℝ :=
  ψ x - ψ (flatReflection j x)

lemma contDiff_oddReflectionTest (j : Fin n) {ψ : KernelSpace n → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) : ContDiff ℝ ∞ (oddReflectionTest j ψ) :=
  hψ.sub (hψ.comp (flatReflection j).toContinuousLinearEquiv.contDiff)

lemma hasCompactSupport_oddReflectionTest (j : Fin n) {ψ : KernelSpace n → ℝ}
    (hψ : HasCompactSupport ψ) : HasCompactSupport (oddReflectionTest j ψ) :=
  hψ.sub (hψ.comp_homeomorph (flatReflection j).toHomeomorph)

lemma oddReflectionTest_zero_on_plane (j : Fin n) (ψ : KernelSpace n → ℝ)
    {x : KernelSpace n} (hx : x j = 0) : oddReflectionTest j ψ x = 0 := by
  simp only [oddReflectionTest, flatReflection_fixed j hx, sub_self]

lemma oddReflectionTest_reflect (j : Fin n) (ψ : KernelSpace n → ℝ) (x : KernelSpace n) :
    oddReflectionTest j ψ (flatReflection j x) = -oddReflectionTest j ψ x := by
  rw [oddReflectionTest, flatReflection_involutive, oddReflectionTest]
  ring

lemma tsupport_oddReflectionTest_subset_ball (j : Fin n) {ψ : KernelSpace n → ℝ} {R : ℝ}
    (hψ : tsupport ψ ⊆ Metric.ball (0 : KernelSpace n) R) :
    tsupport (oddReflectionTest j ψ) ⊆ Metric.ball 0 R := by
  have hc : tsupport (ψ ∘ flatReflection j) ⊆ (flatReflection j) ⁻¹' tsupport ψ := by
    apply closure_minimal _ ((isClosed_tsupport ψ).preimage (flatReflection j).continuous)
    intro x hx
    exact subset_tsupport ψ hx
  change tsupport (ψ - ψ ∘ flatReflection j) ⊆ _
  rw [sub_eq_add_neg]
  apply tsupport_add.trans
  apply union_subset hψ
  have hn : tsupport (-ψ ∘ flatReflection j) = tsupport (ψ ∘ flatReflection j) := by
    apply congrArg closure
    ext x
    simp [Function.mem_support]
  rw [hn]
  intro x hx
  have hh := hψ (hc hx)
  simpa only [Metric.mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map] using hh

end GaussianTilt.MomentMapLinearDirichlet
