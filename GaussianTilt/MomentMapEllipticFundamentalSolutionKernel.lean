import GaussianTilt.MomentMapEllipticFundamentalSolutionLimit

/-!
# The full power/logarithmic Newtonian Hessian kernel

This module covers all positive dimensions with one literal kernel. It
computes the derivative of its Hessian, proves the singular-integral size
bounds, and supplies actual radial-weighted annular cancellation.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma directionalHessian_newtonianKernel {x : KernelSpace n} (hx : x ≠ 0)
    (v w : KernelSpace n) :
    directionalHessian (newtonianKernel n) x v w =
      -(2 * (n : ℝ)) * (‖x‖ ^ 2) ^ (-((n : ℝ) + 2) / 2) * inner ℝ x v * inner ℝ x w +
        2 * (‖x‖ ^ 2) ^ (-(n : ℝ) / 2) * inner ℝ v w := by
  have ht : 0 < (0 : ℝ) + ‖x‖ ^ 2 := by simpa using sq_pos_of_pos (norm_pos_iff.mpr hx)
  simpa only [newtonianKernel, zero_add] using directionalHessian_regularizedNewtonian ht v w

/-- The actual third differential with two directions already fixed. -/
def newtonianThirdCLM (x v w : KernelSpace n) : KernelSpace n →L[ℝ] ℝ :=
  (2 * (n : ℝ) * ((n : ℝ) + 2) * (‖x‖ ^ 2) ^ (-((n : ℝ) + 4) / 2) *
    inner ℝ x v * inner ℝ x w) • innerSL ℝ x +
  (-(2 * (n : ℝ)) * (‖x‖ ^ 2) ^ (-((n : ℝ) + 2) / 2)) •
    (inner ℝ x w • innerSL ℝ v + inner ℝ x v • innerSL ℝ w + inner ℝ v w • innerSL ℝ x)

lemma newtonianThirdCLM_apply (x v w z : KernelSpace n) :
    newtonianThirdCLM x v w z =
      2 * (n : ℝ) * ((n : ℝ) + 2) * (‖x‖ ^ 2) ^ (-((n : ℝ) + 4) / 2) *
        inner ℝ x v * inner ℝ x w * inner ℝ x z -
      2 * (n : ℝ) * (‖x‖ ^ 2) ^ (-((n : ℝ) + 2) / 2) *
        (inner ℝ z v * inner ℝ x w + inner ℝ x v * inner ℝ z w + inner ℝ x z * inner ℝ v w) := by
  simp only [newtonianThirdCLM, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, innerSL_apply, real_inner_comm v z, real_inner_comm w z]
  ring

/-- The Newtonian Hessian is genuinely differentiable away from its
singularity, including the logarithmic case n=2. -/
theorem hasFDerivAt_newtonian_directionalHessian {x : KernelSpace n} (hx : x ≠ 0)
    (v w : KernelSpace n) :
    HasFDerivAt (fun y => directionalHessian (newtonianKernel n) y v w)
      (newtonianThirdCLM x v w) x := by
  have hp := (hasFDerivAt_radialPower (-((n : ℝ) + 2) / 2) hx).const_mul (-(2 * (n : ℝ)))
  have hq := (hasFDerivAt_radialPower (-(n : ℝ) / 2) hx).const_mul 2
  have hv := hasFDerivAt_inner_right v x
  have hw := hasFDerivAt_inner_right w x
  have hh := ((hp.mul hv).mul hw).add (hq.mul_const (inner ℝ v w))
  have heq : (fun y => directionalHessian (newtonianKernel n) y v w) =ᶠ[𝓝 x]
      (fun y => ((-(2 * (n : ℝ)) * radialPower (-((n : ℝ) + 2) / 2) y) * inner ℝ y v) * inner ℝ y w +
        (2 * radialPower (-(n : ℝ) / 2) y) * inner ℝ v w) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hx] with y hy
    exact directionalHessian_newtonianKernel hy v w
  have hactual := hh.congr_of_eventuallyEq heq
  convert hactual using 1
  ext z
  simp only [newtonianThirdCLM, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, Pi.mul_apply, innerSL_apply, radialPower,
    show -((n : ℝ) + 2) / 2 - 1 = -((n : ℝ) + 4) / 2 by ring,
    show -(n : ℝ) / 2 - 1 = -((n : ℝ) + 2) / 2 by ring]
  ring

/-- A radial rank-one-plus-identity tensor has its expected homogeneous
size in every pair of unit-bounded directions. -/
lemma radial_tensor_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b t : ℝ) {x : E} (hx : x ≠ 0) {v w : E} (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    |a * (‖x‖ ^ 2) ^ (t - 1) * inner ℝ x v * inner ℝ x w +
      b * (‖x‖ ^ 2) ^ t * inner ℝ v w| ≤ (|a| + |b|) * ‖x‖ ^ (2 * t) := by
  let S := ‖x‖ ^ 2
  have hS : 0 < S := sq_pos_of_pos (norm_pos_iff.mpr hx)
  have hvx := abs_inner_le_norm_of_norm_le_one (x := x) hv
  have hwx := abs_inner_le_norm_of_norm_le_one (x := x) hw
  have hvw : |inner ℝ v w| ≤ 1 := (abs_inner_le_norm_of_norm_le_one hw).trans hv
  have hprod : |inner ℝ x v| * |inner ℝ x w| ≤ S :=
    (mul_le_mul hvx hwx (abs_nonneg _) (norm_nonneg x)).trans_eq (sq ‖x‖).symm
  have hpow : S ^ (t - 1) * S = S ^ t := by
    rw [← Real.rpow_add_one hS.ne']
    congr 1
    ring
  calc
    _ ≤ |a * S ^ (t - 1) * inner ℝ x v * inner ℝ x w| + |b * S ^ t * inner ℝ v w| := abs_add_le _ _
    _ = |a| * S ^ (t - 1) * (|inner ℝ x v| * |inner ℝ x w|) +
        |b| * S ^ t * |inner ℝ v w| := by
      simp only [abs_mul, abs_of_nonneg (Real.rpow_nonneg hS.le _)]
      ring
    _ ≤ |a| * S ^ (t - 1) * S + |b| * S ^ t * 1 :=
      add_le_add (mul_le_mul_of_nonneg_left hprod (by positivity))
        (mul_le_mul_of_nonneg_left hvw (by positivity))
    _ = (|a| + |b|) * S ^ t := by rw [mul_assoc _ _ S, hpow]; ring
    _ = _ := by rw [show S = ‖x‖ ^ 2 from rfl, squaredNorm_rpow]

/-- A radial third-order tensor has the expected degree one lower. -/
lemma radial_third_tensor_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b t : ℝ) {x : E} (hx : x ≠ 0) {v w z : E}
    (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) (hz : ‖z‖ ≤ 1) :
    |a * (‖x‖ ^ 2) ^ (t - 2) * inner ℝ x v * inner ℝ x w * inner ℝ x z +
      b * (‖x‖ ^ 2) ^ (t - 1) *
        (inner ℝ z v * inner ℝ x w + inner ℝ x v * inner ℝ z w + inner ℝ x z * inner ℝ v w)| ≤
      (|a| + 3 * |b|) * ‖x‖ ^ (2 * t - 1) := by
  let S := ‖x‖ ^ 2
  have hS : 0 < S := sq_pos_of_pos (norm_pos_iff.mpr hx)
  have hvx := abs_inner_le_norm_of_norm_le_one (x := x) hv
  have hwx := abs_inner_le_norm_of_norm_le_one (x := x) hw
  have hzx := abs_inner_le_norm_of_norm_le_one (x := x) hz
  have hzv : |inner ℝ z v| ≤ 1 := (abs_inner_le_norm_of_norm_le_one hv).trans hz
  have hzw : |inner ℝ z w| ≤ 1 := (abs_inner_le_norm_of_norm_le_one hw).trans hz
  have hvw : |inner ℝ v w| ≤ 1 := (abs_inner_le_norm_of_norm_le_one hw).trans hv
  have hprod : |inner ℝ x v| * |inner ℝ x w| * |inner ℝ x z| ≤ S * ‖x‖ := by
    have hpair : |inner ℝ x v| * |inner ℝ x w| ≤ S :=
      (mul_le_mul hvx hwx (abs_nonneg _) (norm_nonneg x)).trans_eq (sq ‖x‖).symm
    exact mul_le_mul hpair hzx (abs_nonneg _) hS.le
  have hsum : |inner ℝ z v * inner ℝ x w + inner ℝ x v * inner ℝ z w +
      inner ℝ x z * inner ℝ v w| ≤ 3 * ‖x‖ := by
    calc
      _ ≤ |inner ℝ z v * inner ℝ x w + inner ℝ x v * inner ℝ z w| +
          |inner ℝ x z * inner ℝ v w| := abs_add_le _ _
      _ ≤ (|inner ℝ z v * inner ℝ x w| + |inner ℝ x v * inner ℝ z w|) +
          |inner ℝ x z * inner ℝ v w| := add_le_add_right (abs_add_le _ _) _
      _ = (|inner ℝ z v| * |inner ℝ x w| + |inner ℝ x v| * |inner ℝ z w|) +
          |inner ℝ x z| * |inner ℝ v w| := by simp only [abs_mul]
      _ ≤ (1 * ‖x‖ + ‖x‖ * 1) + ‖x‖ * 1 := by
        exact add_le_add (add_le_add
          (mul_le_mul hzv hwx (abs_nonneg _) zero_le_one)
          (mul_le_mul hvx hzw (abs_nonneg _) (norm_nonneg x)))
          (mul_le_mul hzx hvw (abs_nonneg _) (norm_nonneg x))
      _ = _ := by ring
  have hpow : S ^ (t - 2) * S = S ^ (t - 1) := by
    rw [← Real.rpow_add_one hS.ne']
    congr 1
    ring
  calc
    _ ≤ |a * S ^ (t - 2) * inner ℝ x v * inner ℝ x w * inner ℝ x z| +
        |b * S ^ (t - 1) * (inner ℝ z v * inner ℝ x w + inner ℝ x v * inner ℝ z w + inner ℝ x z * inner ℝ v w)| := abs_add_le _ _
    _ = |a| * S ^ (t - 2) * (|inner ℝ x v| * |inner ℝ x w| * |inner ℝ x z|) +
        |b| * S ^ (t - 1) * |inner ℝ z v * inner ℝ x w + inner ℝ x v * inner ℝ z w + inner ℝ x z * inner ℝ v w| := by
      simp only [abs_mul, abs_of_nonneg (Real.rpow_nonneg hS.le _)]
      ring
    _ ≤ |a| * S ^ (t - 2) * (S * ‖x‖) + |b| * S ^ (t - 1) * (3 * ‖x‖) :=
      add_le_add (mul_le_mul_of_nonneg_left hprod (by positivity))
        (mul_le_mul_of_nonneg_left hsum (by positivity))
    _ = (|a| * (S ^ (t - 2) * S) + 3 * |b| * S ^ (t - 1)) * ‖x‖ := by ring
    _ = (|a| + 3 * |b|) * (S ^ (t - 1) * ‖x‖) := by rw [hpow]; ring
    _ = _ := by
      rw [show S = ‖x‖ ^ 2 from rfl, squaredNorm_rpow,
        ← Real.rpow_add_one (norm_ne_zero_iff.mpr hx)]
      congr 2
      ring

/-- Actual Newtonian Hessian size, uniform over all unit-bounded directions. -/
theorem newtonian_directionalHessian_bound {x : KernelSpace n} (hx : x ≠ 0)
    {v w : KernelSpace n} (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    |directionalHessian (newtonianKernel n) x v w| ≤
      (2 * ((n : ℝ) + 1)) * ‖x‖ ^ (-(n : ℝ)) := by
  rw [directionalHessian_newtonianKernel hx]
  have hh := radial_tensor_bound (-(2 * (n : ℝ))) 2 (-(n : ℝ) / 2) hx hv hw
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have he : -(n : ℝ) / 2 - 1 = -((n : ℝ) + 2) / 2 := by ring
  simpa only [he, abs_neg, abs_of_nonneg (by positivity : 0 ≤ 2 * (n : ℝ)), abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    show 2 * (-(n : ℝ) / 2) = -(n : ℝ) by ring, show 2 * (n : ℝ) + 2 = 2 * ((n : ℝ) + 1) by ring] using hh

/-- Actual third-derivative size of the Newtonian kernel. -/
theorem newtonian_third_derivative_bound {x : KernelSpace n} (hx : x ≠ 0)
    {v w z : KernelSpace n} (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) (hz : ‖z‖ ≤ 1) :
    |fderiv ℝ (fun y => directionalHessian (newtonianKernel n) y v w) x z| ≤
      (2 * (n : ℝ) * ((n : ℝ) + 5)) * ‖x‖ ^ (-(n : ℝ) - 1) := by
  rw [(hasFDerivAt_newtonian_directionalHessian hx v w).fderiv, newtonianThirdCLM_apply]
  have hh := radial_third_tensor_bound (2 * (n : ℝ) * ((n : ℝ) + 2)) (-(2 * (n : ℝ)))
    (-(n : ℝ) / 2) hx hv hw hz
  have he1 : -(n : ℝ) / 2 - 1 = -((n : ℝ) + 2) / 2 := by ring
  have he2 : -(n : ℝ) / 2 - 2 = -((n : ℝ) + 4) / 2 := by ring
  have he3 : 2 * (-(n : ℝ) / 2) - 1 = -(n : ℝ) - 1 := by ring
  simp only [he1, he2, he3, abs_neg, abs_of_nonneg (by positivity : 0 ≤ 2 * (n : ℝ)),
    abs_of_nonneg (by positivity : 0 ≤ 2 * (n : ℝ) * ((n : ℝ) + 2))] at hh
  convert hh using 1 <;> congr 1 <;> ring

end GaussianTilt.MomentMapElliptic
