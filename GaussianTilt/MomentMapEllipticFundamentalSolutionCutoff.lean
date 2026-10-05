import GaussianTilt.MomentMapEllipticFundamentalSolutionKernel

/-!
# Genuine radial-cutoff Newtonian Hessian kernels

The logarithmic and power kernels have the same radial tensor form. Actual
orthogonal symmetries and their proved zero trace yield annular cancellation
with every continuous radial weight. Compact radial cutoffs therefore give
integrable tails with exactly zero integral, as required by the singular
integral Hölder estimate.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace GaussianTilt.MomentMapElliptic
variable {n : ℕ}

def newtonianHessianEntry (i j : Fin n) (x : KernelSpace n) : ℝ :=
  directionalHessian (newtonianKernel n) x (EuclideanSpace.basisFun (Fin n) ℝ i)
    (EuclideanSpace.basisFun (Fin n) ℝ j)

lemma newtonianHessianEntry_formula {x : KernelSpace n} (hx : x ≠ 0) (i j : Fin n) :
    newtonianHessianEntry i j x =
      -(2 * (n : ℝ)) * (‖x‖ ^ 2) ^ (-((n : ℝ) + 2) / 2) * x i * x j +
        2 * (‖x‖ ^ 2) ^ (-(n : ℝ) / 2) * (if i = j then 1 else 0) := by
  rw [newtonianHessianEntry, directionalHessian_newtonianKernel hx]
  have hb := (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal
  rw [orthonormal_iff_ite] at hb
  rw [hb i j, EuclideanSpace.inner_basisFun_real, EuclideanSpace.inner_basisFun_real]

lemma trace_newtonianHessianEntry {x : KernelSpace n} (hx : x ≠ 0) :
    (∑ i : Fin n, newtonianHessianEntry i i x) = 0 := by
  have ht : 0 < (0 : ℝ) + ‖x‖ ^ 2 := by simpa using sq_pos_of_pos (norm_pos_iff.mpr hx)
  simpa only [newtonianHessianEntry, newtonianKernel, mul_zero, zero_mul] using
    trace_directionalHessian_regularizedNewtonian ht

lemma measurable_newtonianHessianEntry (i j : Fin n) : Measurable (newtonianHessianEntry i j) := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hm : Measurable (fun L : KernelSpace n →L[ℝ] ℝ => L (b j)) :=
    (show Continuous (fun L : KernelSpace n →L[ℝ] ℝ => L (b j)) from
      continuous_id.clm_apply continuous_const).measurable
  exact hm.comp (measurable_fderiv ℝ (fun x => fderiv ℝ (newtonianKernel n) x (b i)))

lemma continuousOn_newtonianHessianEntry (i j : Fin n) {A : Set (KernelSpace n)}
    (hA : ∀ x ∈ A, x ≠ 0) : ContinuousOn (newtonianHessianEntry i j) A := by
  intro x hx
  exact (hasFDerivAt_newtonian_directionalHessian (hA x hx) _ _).continuousAt.continuousWithinAt

/-- A continuous radial cutoff of an actual Hessian entry. -/
def cutoffNewtonianHessian (χ : ℝ → ℝ) (i j : Fin n) (x : KernelSpace n) : ℝ :=
  χ ‖x‖ * newtonianHessianEntry i j x

lemma measurable_cutoffNewtonianHessian {χ : ℝ → ℝ} (hχ : Continuous χ) (i j : Fin n) :
    Measurable (cutoffNewtonianHessian χ i j) :=
  (hχ.measurable.comp measurable_norm).mul (measurable_newtonianHessianEntry i j)

lemma integrableOn_cutoffNewtonianHessian_annulus {χ : ℝ → ℝ} (hχ : Continuous χ)
    (i j : Fin n) {r R : ℝ} (hr : 0 < r) :
    IntegrableOn (cutoffNewtonianHessian χ i j) (kernelAnnulus r R) := by
  apply ContinuousOn.integrableOn_compact (isCompact_kernelAnnulus r R)
  exact (hχ.comp continuous_norm).continuousOn.mul
    (continuousOn_newtonianHessianEntry i j (fun _ hx => kernelAnnulus_ne_zero hr hx))

lemma integral_cutoffNewtonianHessian_offDiagonal (χ : ℝ → ℝ) {r R : ℝ}
    (hr : 0 < r) (i j : Fin n) (hij : i ≠ j) :
    (∫ x in kernelAnnulus r R, cutoffNewtonianHessian χ i j x) = 0 := by
  have heq : EqOn (cutoffNewtonianHessian χ i j)
      (fun x : KernelSpace n => (χ ‖x‖ * (-(2 * (n : ℝ)) * (‖x‖ ^ 2) ^ (-((n : ℝ) + 2) / 2))) * x i * x j)
      (kernelAnnulus r R) := by
    intro x hx
    rw [cutoffNewtonianHessian, newtonianHessianEntry_formula (kernelAnnulus_ne_zero hr hx), if_neg hij, mul_zero, add_zero]
    ring
  rw [setIntegral_congr_fun (isClosed_kernelAnnulus r R).measurableSet heq]
  exact integral_radial_coordinate_product_offDiagonal
    (fun t => χ t * (-(2 * (n : ℝ)) * (t ^ 2) ^ (-((n : ℝ) + 2) / 2))) r R i j hij

lemma integral_cutoffNewtonianHessian_diagonal_eq (χ : ℝ → ℝ) {r R : ℝ}
    (hr : 0 < r) (i j : Fin n) :
    (∫ x in kernelAnnulus r R, cutoffNewtonianHessian χ i i x) =
      ∫ x in kernelAnnulus r R, cutoffNewtonianHessian χ j j x := by
  classical
  let T : KernelSpace n ≃ₗᵢ[ℝ] KernelSpace n :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j)
  have hTi (x : KernelSpace n) : T x i = x j := by
    change x ((Equiv.swap i j).symm i) = x j
    rw [Equiv.symm_swap, Equiv.swap_apply_left]
  have hchange := integral_kernelAnnulus_comp_isometry T (cutoffNewtonianHessian χ i i) r R
  have heq : EqOn (fun x => cutoffNewtonianHessian χ i i (T x))
      (cutoffNewtonianHessian χ j j) (kernelAnnulus r R) := by
    intro x hx
    have hx0 := kernelAnnulus_ne_zero hr hx
    have hTx0 : T x ≠ 0 := by intro he; exact hx0 (T.injective (by simpa using he))
    simp only [cutoffNewtonianHessian, newtonianHessianEntry_formula hTx0,
      newtonianHessianEntry_formula hx0, T.norm_map, hTi, if_true]
  have hh := setIntegral_congr_fun (μ := volume) (isClosed_kernelAnnulus r R).measurableSet heq
  exact hchange.symm.trans hh

/-- Actual radial-weighted annular cancellation in every positive dimension,
including the logarithmic kernel in dimension two. -/
theorem integral_cutoffNewtonianHessian_annulus_zero [NeZero n]
    {χ : ℝ → ℝ} (hχ : Continuous χ) {r R : ℝ} (hr : 0 < r) (i j : Fin n) :
    (∫ x in kernelAnnulus r R, cutoffNewtonianHessian χ i j x) = 0 := by
  by_cases hij : i = j
  · subst j
    let J : Fin n → ℝ := fun k => ∫ x in kernelAnnulus r R, cutoffNewtonianHessian χ k k x
    have hsum : (∑ k, J k) = 0 := by
      calc
        (∑ k, J k) = ∫ x in kernelAnnulus r R, ∑ k, cutoffNewtonianHessian χ k k x :=
          (integral_finset_sum Finset.univ
            (fun k _ => integrableOn_cutoffNewtonianHessian_annulus hχ k k hr)).symm
        _ = 0 := setIntegral_eq_zero_of_forall_eq_zero (fun x hx => by
          simp only [cutoffNewtonianHessian, ← Finset.mul_sum,
            trace_newtonianHessianEntry (kernelAnnulus_ne_zero hr hx), mul_zero])
    have heq (k : Fin n) : J k = J i := integral_cutoffNewtonianHessian_diagonal_eq χ hr k i
    simp_rw [heq] at hsum
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    exact (mul_eq_zero.mp hsum).resolve_left (Nat.cast_ne_zero.mpr (NeZero.ne n))
  · exact integral_cutoffNewtonianHessian_offDiagonal χ hr i j hij

lemma cutoffNewtonianHessian_tail_indicator {χ : ℝ → ℝ} {R : ℝ}
    (hχR : ∀ t : ℝ, R < t → χ t = 0) (r : ℝ) (i j : Fin n) :
    (Metric.ball (0 : KernelSpace n) r)ᶜ.indicator (cutoffNewtonianHessian χ i j) =
      (kernelAnnulus r R).indicator (cutoffNewtonianHessian χ i j) := by
  classical
  funext x
  by_cases hrx : r ≤ ‖x‖
  · by_cases hxR : ‖x‖ ≤ R
    · simp [kernelAnnulus, Metric.mem_ball, not_lt.mpr hrx, hrx, hxR]
    · have hzero : cutoffNewtonianHessian χ i j x = 0 := by
        rw [cutoffNewtonianHessian, hχR _ (lt_of_not_ge hxR), zero_mul]
      simp [kernelAnnulus, Metric.mem_ball, not_lt.mpr hrx, hrx, hxR, hzero]
  · have hxball : x ∈ Metric.ball (0 : KernelSpace n) r := by simpa using lt_of_not_ge hrx
    have hxA : x ∉ kernelAnnulus r R := fun h => hrx h.1
    simp [hxball, hxA]

/-- Compact radial cutoffs have actual integrable tails with zero total
mass outside every positive radius. -/
theorem cutoffNewtonianHessian_tail_properties [NeZero n] {χ : ℝ → ℝ}
    (hχ : Continuous χ) {R : ℝ} (hχR : ∀ t : ℝ, R < t → χ t = 0)
    {r : ℝ} (hr : 0 < r) (i j : Fin n) :
    IntegrableOn (cutoffNewtonianHessian χ i j) (Metric.ball (0 : KernelSpace n) r)ᶜ ∧
      (∫ x in (Metric.ball (0 : KernelSpace n) r)ᶜ, cutoffNewtonianHessian χ i j x) = 0 := by
  have hA := (isClosed_kernelAnnulus (n := n) r R).measurableSet
  have hB : MeasurableSet (Metric.ball (0 : KernelSpace n) r)ᶜ := Metric.isOpen_ball.measurableSet.compl
  have he := cutoffNewtonianHessian_tail_indicator hχR r i j
  constructor
  · rw [← integrable_indicator_iff hB, he, integrable_indicator_iff hA]
    exact integrableOn_cutoffNewtonianHessian_annulus hχ i j hr
  · rw [← integral_indicator hB, he, integral_indicator hA]
    exact integral_cutoffNewtonianHessian_annulus_zero hχ hr i j

/-- The boundary sphere has zero volume, so cancellation also holds on
the open exterior used by the singular-integral estimates. -/
theorem cutoffNewtonianHessian_closedBall_tail_zero [NeZero n] {χ : ℝ → ℝ}
    (hχ : Continuous χ) {R : ℝ} (hχR : ∀ t : ℝ, R < t → χ t = 0)
    {r : ℝ} (hr : 0 < r) (i j : Fin n) :
    (∫ x in (Metric.closedBall (0 : KernelSpace n) r)ᶜ, cutoffNewtonianHessian χ i j x) = 0 := by
  have hne : ∀ᵐ x : KernelSpace n ∂volume, dist x 0 ≠ r := by
    apply ae_iff.mpr
    simpa only [not_not, ← Metric.mem_sphere, setOf_mem_eq] using volume.addHaar_sphere (0 : KernelSpace n) r
  have he : (Metric.closedBall (0 : KernelSpace n) r)ᶜ =ᵐ[volume]
      (Metric.ball (0 : KernelSpace n) r)ᶜ := by
    filter_upwards [hne] with x hx
    apply propext
    change (¬dist x 0 ≤ r) ↔ (¬dist x 0 < r)
    constructor
    · intro h hh
      exact h hh.le
    · intro h hh
      exact hx (le_antisymm hh (le_of_not_gt h))
  exact (setIntegral_congr_set he).trans (cutoffNewtonianHessian_tail_properties hχ hχR hr i j).2

lemma newtonianHessianEntry_bound {x : KernelSpace n} (hx : x ≠ 0) (i j : Fin n) :
    |newtonianHessianEntry i j x| ≤ (2 * ((n : ℝ) + 1)) * ‖x‖ ^ (-(n : ℝ)) :=
  newtonian_directionalHessian_bound hx
    ((EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.norm_eq_one i).le
    ((EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.norm_eq_one j).le

lemma differentiableAt_newtonianHessianEntry {x : KernelSpace n} (hx : x ≠ 0) (i j : Fin n) :
    DifferentiableAt ℝ (newtonianHessianEntry i j) x :=
  (hasFDerivAt_newtonian_directionalHessian hx _ _).differentiableAt

lemma norm_fderiv_newtonianHessianEntry_le {x : KernelSpace n} (hx : x ≠ 0) (i j : Fin n) :
    ‖fderiv ℝ (newtonianHessianEntry i j) x‖ ≤
      (2 * (n : ℝ) * ((n : ℝ) + 5)) * ‖x‖ ^ (-(n : ℝ) - 1) := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro z hz
  rw [Real.norm_eq_abs]
  exact newtonian_third_derivative_bound hx
    ((EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.norm_eq_one i).le
    ((EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.norm_eq_one j).le hz.le

lemma cutoffNewtonianHessian_support {χ : ℝ → ℝ} {R : ℝ}
    (hχR : ∀ t : ℝ, R < t → χ t = 0) (i j : Fin n) (x : KernelSpace n)
    (hx : R < ‖x‖) : cutoffNewtonianHessian χ i j x = 0 := by
  rw [cutoffNewtonianHessian, hχR _ hx, zero_mul]

lemma cutoffNewtonianHessian_bound {χ : ℝ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hχ : ∀ t : ℝ, 0 ≤ t → |χ t| ≤ A) {x : KernelSpace n} (hx : x ≠ 0) (i j : Fin n) :
    |cutoffNewtonianHessian χ i j x| ≤
      (A * (2 * ((n : ℝ) + 1))) * ‖x‖ ^ (-(n : ℝ)) := by
  rw [cutoffNewtonianHessian, abs_mul]
  exact (mul_le_mul (hχ _ (norm_nonneg x)) (newtonianHessianEntry_bound hx i j)
    (abs_nonneg _) hA).trans_eq (by ring)

lemma differentiableAt_cutoffNewtonianHessian {χ : ℝ → ℝ} (hχ : Differentiable ℝ χ)
    {x : KernelSpace n} (hx : x ≠ 0) (i j : Fin n) :
    DifferentiableAt ℝ (cutoffNewtonianHessian χ i j) x := by
  have hn : DifferentiableAt ℝ (fun y : KernelSpace n => ‖y‖) x := differentiableAt_id.norm ℝ hx
  exact ((hχ ‖x‖).comp x hn).mul (differentiableAt_newtonianHessianEntry hx i j)

/-- Actual derivative decay of a radial-cutoff Hessian kernel, with the
weighted radial derivative of the cutoff made explicit. -/
theorem norm_fderiv_cutoffNewtonianHessian_le [NeZero n] {χ : ℝ → ℝ}
    (hχ : Differentiable ℝ χ) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hχA : ∀ t : ℝ, 0 ≤ t → |χ t| ≤ A)
    (hχB : ∀ t : ℝ, 0 < t → t * |deriv χ t| ≤ B)
    {x : KernelSpace n} (hx : x ≠ 0) (i j : Fin n) :
    ‖fderiv ℝ (cutoffNewtonianHessian χ i j) x‖ ≤
      (A * (2 * (n : ℝ) * ((n : ℝ) + 5)) + B * (2 * ((n : ℝ) + 1))) *
        ‖x‖ ^ (-(n : ℝ) - 1) := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hn : DifferentiableAt ℝ (fun y : KernelSpace n => ‖y‖) x := differentiableAt_id.norm ℝ hx
  have hfirst := (hχ ‖x‖).hasDerivAt.comp_hasFDerivAt x hn.hasFDerivAt
  have hsecond := (differentiableAt_newtonianHessianEntry hx i j).hasFDerivAt
  have hprod := hfirst.mul hsecond
  change ‖fderiv ℝ ((χ ∘ norm) * newtonianHessianEntry i j) x‖ ≤ _
  rw [hprod.fderiv]
  have hnorm : ‖fderiv ℝ (fun y : KernelSpace n => ‖y‖) x‖ = 1 := norm_fderiv_norm hn
  have htriangle := norm_add_le
    (χ ‖x‖ • fderiv ℝ (newtonianHessianEntry i j) x)
    (newtonianHessianEntry i j x • (deriv χ ‖x‖ • fderiv ℝ (fun y : KernelSpace n => ‖y‖) x))
  simp only [norm_smul, Real.norm_eq_abs, hnorm, mul_one] at htriangle
  have hp : ‖x‖ ^ (-(n : ℝ)) = ‖x‖ ^ (-(n : ℝ) - 1) * ‖x‖ := by
    rw [← Real.rpow_add_one hr.ne']
    congr 1
    ring
  calc
    _ ≤ |χ ‖x‖| * ‖fderiv ℝ (newtonianHessianEntry i j) x‖ +
        |newtonianHessianEntry i j x| * |deriv χ ‖x‖| := htriangle
    _ ≤ A * ((2 * (n : ℝ) * ((n : ℝ) + 5)) * ‖x‖ ^ (-(n : ℝ) - 1)) +
        ((2 * ((n : ℝ) + 1)) * ‖x‖ ^ (-(n : ℝ))) * |deriv χ ‖x‖| :=
      add_le_add (mul_le_mul (hχA _ hr.le) (norm_fderiv_newtonianHessianEntry_le hx i j)
        (norm_nonneg _) hA)
        (mul_le_mul_of_nonneg_right (newtonianHessianEntry_bound hx i j) (abs_nonneg _))
    _ = A * ((2 * (n : ℝ) * ((n : ℝ) + 5)) * ‖x‖ ^ (-(n : ℝ) - 1)) +
        ((2 * ((n : ℝ) + 1)) * ‖x‖ ^ (-(n : ℝ) - 1)) * (‖x‖ * |deriv χ ‖x‖|) := by
      rw [hp]
      ring
    _ ≤ A * ((2 * (n : ℝ) * ((n : ℝ) + 5)) * ‖x‖ ^ (-(n : ℝ) - 1)) +
        ((2 * ((n : ℝ) + 1)) * ‖x‖ ^ (-(n : ℝ) - 1)) * B :=
      add_le_add_left (mul_le_mul_of_nonneg_left (hχB _ hr) (by positivity)) _
    _ = _ := by ring

end GaussianTilt.MomentMapElliptic
