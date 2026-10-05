import GaussianTilt.MomentMapEllipticFundamentalSolution

/-!
# Actual annular cancellation of the Newtonian Hessian

Orthogonal coordinate reflections and exchanges preserve both Lebesgue
measure and concentric annuli. Their exact change-of-variables identities
supply off-diagonal cancellation and equality of diagonal radial moments.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace GaussianTilt.MomentMapElliptic

abbrev KernelSpace (n : ℕ) := EuclideanSpace ℝ (Fin n)
variable {n : ℕ}

/-- A compact concentric annulus, separated from the origin when `r > 0`. -/
def kernelAnnulus (r R : ℝ) : Set (KernelSpace n) := {x | r ≤ ‖x‖ ∧ ‖x‖ ≤ R}

lemma isClosed_kernelAnnulus (r R : ℝ) : IsClosed (kernelAnnulus (n := n) r R) :=
  (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)

lemma isCompact_kernelAnnulus (r R : ℝ) : IsCompact (kernelAnnulus (n := n) r R) := by
  apply (isCompact_closedBall (0 : KernelSpace n) R).of_isClosed_subset
    (isClosed_kernelAnnulus r R)
  intro x hx
  simpa only [Metric.mem_closedBall, dist_zero_right] using hx.2

lemma kernelAnnulus_ne_zero {r R : ℝ} (hr : 0 < r) {x : KernelSpace n}
    (hx : x ∈ kernelAnnulus r R) : x ≠ 0 := by
  intro he
  have hh := hx.1
  rw [he, norm_zero] at hh
  exact (not_le_of_gt hr) hh

/-- Orthogonal changes of variables preserve the actual annular integral. -/
lemma integral_kernelAnnulus_comp_isometry (T : KernelSpace n ≃ₗᵢ[ℝ] KernelSpace n)
    (f : KernelSpace n → ℝ) (r R : ℝ) :
    (∫ x in kernelAnnulus r R, f (T x)) = ∫ x in kernelAnnulus r R, f x := by
  have he : T ⁻¹' kernelAnnulus r R = kernelAnnulus r R := by
    ext x
    simp only [mem_preimage, kernelAnnulus, mem_setOf_eq, T.norm_map]
  have hp := T.measurePreserving.restrict_preimage (isClosed_kernelAnnulus r R).measurableSet
  rw [he] at hp
  exact hp.integral_comp T.toHomeomorph.measurableEmbedding f

/-- Every off-diagonal radial second moment on an annulus is exactly zero.
The identity itself needs no integrability hypothesis. -/
theorem integral_radial_coordinate_product_offDiagonal (F : ℝ → ℝ)
    (r R : ℝ) (i j : Fin n) (hij : i ≠ j) :
    (∫ x in kernelAnnulus r R, F ‖x‖ * x i * x j) = 0 := by
  classical
  let T : KernelSpace n ≃ₗᵢ[ℝ] KernelSpace n := LinearIsometryEquiv.piLpCongrRight 2
    (fun k => if k = i then (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ)
      else LinearIsometryEquiv.refl ℝ ℝ)
  have hTi (x : KernelSpace n) : T x i = -x i := by
    simp [T, LinearIsometryEquiv.piLpCongrRight_apply]
  have hTj (x : KernelSpace n) : T x j = x j := by
    simp [T, LinearIsometryEquiv.piLpCongrRight_apply, Ne.symm hij]
  have hchange := integral_kernelAnnulus_comp_isometry T
    (fun x => F ‖x‖ * x i * x j) r R
  have he : (fun x : KernelSpace n => F ‖T x‖ * T x i * T x j) =
      (fun x => -(F ‖x‖ * x i * x j)) := by
    funext x
    rw [T.norm_map, hTi, hTj]
    ring
  rw [he, integral_neg] at hchange
  linarith

/-- Exchanging two orthonormal coordinates makes all diagonal radial
second moments equal on a concentric annulus. -/
theorem integral_radial_coordinate_square_eq (F : ℝ → ℝ)
    (r R : ℝ) (i j : Fin n) :
    (∫ x in kernelAnnulus r R, F ‖x‖ * x i * x i) =
      ∫ x in kernelAnnulus r R, F ‖x‖ * x j * x j := by
  classical
  let T : KernelSpace n ≃ₗᵢ[ℝ] KernelSpace n :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j)
  have hTi (x : KernelSpace n) : T x i = x j := by
    change x ((Equiv.swap i j).symm i) = x j
    congr 1
    apply (Equiv.swap i j).injective
    simp only [Equiv.apply_symm_apply]
    exact (Equiv.swap_apply_right i j).symm
  have hh := integral_kernelAnnulus_comp_isometry T (fun x => F ‖x‖ * x i * x i) r R
  have he : (fun x : KernelSpace n => F ‖T x‖ * T x i * T x i) =
      (fun x => F ‖x‖ * x j * x j) := by
    funext x
    rw [T.norm_map, hTi]
  rw [he] at hh
  exact hh.symm

/-- The literal Hessian entry of a radial power in the Euclidean coordinate
basis, including the Kronecker term. -/
lemma directionalHessian_radialPower_basis (β : ℝ) {x : KernelSpace n} (hx : x ≠ 0)
    (i j : Fin n) :
    directionalHessian (radialPower β) x (EuclideanSpace.basisFun (Fin n) ℝ i)
      (EuclideanSpace.basisFun (Fin n) ℝ j) =
      4 * β * (β - 1) * (‖x‖ ^ 2) ^ (β - 2) * x i * x j +
        2 * β * (‖x‖ ^ 2) ^ (β - 1) * (if i = j then 1 else 0) := by
  rw [directionalHessian_radialPower β hx]
  have hb := (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal
  rw [orthonormal_iff_ite] at hb
  rw [hb i j, EuclideanSpace.inner_basisFun_real, EuclideanSpace.inner_basisFun_real]

/-- Literal coordinate Hessian entry of the radial kernel. -/
def radialHessianEntry (β : ℝ) (i j : Fin n) (x : KernelSpace n) : ℝ :=
  directionalHessian (radialPower β) x (EuclideanSpace.basisFun (Fin n) ℝ i)
    (EuclideanSpace.basisFun (Fin n) ℝ j)

lemma integrableOn_radialHessianEntry (β : ℝ) (i j : Fin n)
    {r R : ℝ} (hr : 0 < r) : IntegrableOn (radialHessianEntry β i j) (kernelAnnulus r R) := by
  apply ContinuousOn.integrableOn_compact (isCompact_kernelAnnulus r R)
  exact continuousOn_directionalHessian_radialPower β _ _
    (fun x hx => kernelAnnulus_ne_zero hr hx)

/-- Actual off-diagonal Hessian entries cancel on every compact annulus. -/
theorem integral_radialHessianEntry_offDiagonal (β : ℝ) {r R : ℝ}
    (hr : 0 < r) (i j : Fin n) (hij : i ≠ j) :
    (∫ x in kernelAnnulus r R, radialHessianEntry β i j x) = 0 := by
  classical
  have heq : EqOn (radialHessianEntry β i j)
      (fun x : KernelSpace n => (4 * β * (β - 1) * (‖x‖ ^ 2) ^ (β - 2)) * x i * x j)
      (kernelAnnulus r R) := by
    intro x hx
    simp only [radialHessianEntry, directionalHessian_radialPower_basis β (kernelAnnulus_ne_zero hr hx),
      if_neg hij, mul_zero, add_zero]
  rw [setIntegral_congr_fun (isClosed_kernelAnnulus r R).measurableSet heq]
  exact integral_radial_coordinate_product_offDiagonal
    (fun t => 4 * β * (β - 1) * (t ^ 2) ^ (β - 2)) r R i j hij

/-- The diagonal integrals of the actual Hessian are equal by orthogonal
coordinate exchange. This is proved for the kernel itself. -/
theorem integral_radialHessianEntry_diagonal_eq (β : ℝ) {r R : ℝ}
    (hr : 0 < r) (i j : Fin n) :
    (∫ x in kernelAnnulus r R, radialHessianEntry β i i x) =
      ∫ x in kernelAnnulus r R, radialHessianEntry β j j x := by
  classical
  let T : KernelSpace n ≃ₗᵢ[ℝ] KernelSpace n :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j)
  have hTi (x : KernelSpace n) : T x i = x j := by
    change x ((Equiv.swap i j).symm i) = x j
    rw [Equiv.symm_swap, Equiv.swap_apply_left]
  have hchange := integral_kernelAnnulus_comp_isometry T (radialHessianEntry β i i) r R
  have heq : EqOn (fun x => radialHessianEntry β i i (T x))
      (radialHessianEntry β j j) (kernelAnnulus r R) := by
    intro x hx
    have hx0 := kernelAnnulus_ne_zero hr hx
    have hTx0 : T x ≠ 0 := by intro he; exact hx0 (T.injective (by simpa using he))
    simp only [radialHessianEntry, directionalHessian_radialPower_basis β hTx0,
      directionalHessian_radialPower_basis β hx0, T.norm_map, hTi, if_true]
  have hh := setIntegral_congr_fun (μ := volume) (isClosed_kernelAnnulus r R).measurableSet heq
  exact hchange.symm.trans hh

/-- Full annular cancellation of the actual Newtonian-power Hessian.
The proof uses measured orthogonal changes of variables and the computed
zero trace, including proof of integrability on the compact annulus. -/
theorem integral_newtonian_power_hessianEntry_eq_zero [NeZero n] {r R : ℝ}
    (hr : 0 < r) (i j : Fin n) :
    (∫ x in kernelAnnulus r R, radialHessianEntry ((2 - (n : ℝ)) / 2) i j x) = 0 := by
  by_cases hij : i = j
  · subst j
    let β : ℝ := (2 - (n : ℝ)) / 2
    let J : Fin n → ℝ := fun k => ∫ x in kernelAnnulus r R, radialHessianEntry β k k x
    have hsum : (∑ k, J k) = 0 := by
      calc
        (∑ k, J k) = ∫ x in kernelAnnulus r R, ∑ k, radialHessianEntry β k k x := by
          exact (integral_finset_sum Finset.univ (fun k _ => integrableOn_radialHessianEntry β k k hr)).symm
        _ = 0 := setIntegral_eq_zero_of_forall_eq_zero (fun x hx => by
          simpa only [radialHessianEntry, β, Fintype.card_fin] using
            newtonian_power_trace_zero (EuclideanSpace.basisFun (Fin n) ℝ) (kernelAnnulus_ne_zero hr hx))
    have heq (k : Fin n) : J k = J i := integral_radialHessianEntry_diagonal_eq β hr k i
    simp_rw [heq] at hsum
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
    exact (mul_eq_zero.mp hsum).resolve_left hn
  · exact integral_radialHessianEntry_offDiagonal _ hr i j hij

end GaussianTilt.MomentMapElliptic
