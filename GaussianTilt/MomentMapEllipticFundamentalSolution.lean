import Mathlib

/-!
# Actual radial kernels for the constant-coefficient elliptic equation

The derivatives below are the literal Fréchet derivatives of radial power
kernels. They are computed away from the singularity; no fundamental-solution
or singular-integral theorem is assumed. Distributional normalization and
Poisson representation are separate analytic steps.
-/
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace GaussianTilt.MomentMapElliptic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A power of squared Euclidean distance, before dimensional normalization. -/
def radialPower (β : ℝ) (x : E) : ℝ := (‖x‖ ^ 2) ^ β

/-- The literal iterated directional Fréchet derivative. -/
def directionalHessian (f : E → ℝ) (x v w : E) : ℝ :=
  fderiv ℝ (fun y => fderiv ℝ f y v) x w

lemma hasFDerivAt_radialPower (β : ℝ) {x : E} (hx : x ≠ 0) :
    HasFDerivAt (radialPower β)
      ((2 * β * (‖x‖ ^ 2) ^ (β - 1)) • innerSL ℝ x) x := by
  have hs : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  have hh := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.rpow_const (p := β) (Or.inl hs)
  convert hh using 1
  ext v
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

lemma fderiv_radialPower_apply (β : ℝ) {x : E} (hx : x ≠ 0) (v : E) :
    fderiv ℝ (radialPower β) x v =
      2 * β * (‖x‖ ^ 2) ^ (β - 1) * inner ℝ x v := by
  rw [(hasFDerivAt_radialPower β hx).fderiv]
  rfl

lemma hasFDerivAt_inner_right (v : E) (x : E) :
    HasFDerivAt (fun y => inner ℝ y v) (innerSL ℝ v) x := by
  simpa only [real_inner_comm] using (innerSL ℝ v).hasFDerivAt (x := x)

/-- Exact off-origin Hessian formula for every real power of the squared
norm. The result is expressed in arbitrary vectors, independent of a basis. -/
theorem directionalHessian_radialPower (β : ℝ) {x : E} (hx : x ≠ 0) (v w : E) :
    directionalHessian (radialPower β) x v w =
      4 * β * (β - 1) * (‖x‖ ^ 2) ^ (β - 2) * inner ℝ x v * inner ℝ x w +
        2 * β * (‖x‖ ^ 2) ^ (β - 1) * inner ℝ v w := by
  have hp := (hasFDerivAt_radialPower (β - 1) hx).const_mul (2 * β)
  have hi := hasFDerivAt_inner_right v x
  have hh := hp.mul hi
  have heq : (fun y => fderiv ℝ (radialPower β) y v) =ᶠ[𝓝 x]
      (fun y => (2 * β * radialPower (β - 1) y) * inner ℝ y v) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hx] with y hy
    exact fderiv_radialPower_apply β hy v
  have hactual := hh.congr_of_eventuallyEq heq
  unfold directionalHessian
  rw [hactual.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, Pi.mul_apply, innerSL_apply, radialPower, show β - 1 - 1 = β - 2 by ring,
    real_inner_comm v w]
  ring

/-- The actual radial-power Hessian, differentiated in one more direction. -/
theorem fderiv_directionalHessian_radialPower (β : ℝ) {x : E} (hx : x ≠ 0)
    (v w z : E) :
    fderiv ℝ (fun y => directionalHessian (radialPower β) y v w) x z =
      8 * β * (β - 1) * (β - 2) * (‖x‖ ^ 2) ^ (β - 3) *
        inner ℝ x v * inner ℝ x w * inner ℝ x z +
      4 * β * (β - 1) * (‖x‖ ^ 2) ^ (β - 2) *
        (inner ℝ z v * inner ℝ x w + inner ℝ x v * inner ℝ z w +
          inner ℝ x z * inner ℝ v w) := by
  have hp := (hasFDerivAt_radialPower (β - 2) hx).const_mul (4 * β * (β - 1))
  have hq := (hasFDerivAt_radialPower (β - 1) hx).const_mul (2 * β)
  have hv := hasFDerivAt_inner_right v x
  have hw := hasFDerivAt_inner_right w x
  have hh := ((hp.mul hv).mul hw).add (hq.mul_const (inner ℝ v w))
  have heq : (fun y => directionalHessian (radialPower β) y v w) =ᶠ[𝓝 x]
      (fun y => ((4 * β * (β - 1) * radialPower (β - 2) y) * inner ℝ y v) * inner ℝ y w +
        (2 * β * radialPower (β - 1) y) * inner ℝ v w) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hx] with y hy
    exact directionalHessian_radialPower β hy v w
  have hactual := hh.congr_of_eventuallyEq heq
  rw [hactual.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, Pi.mul_apply, innerSL_apply, radialPower,
    show β - 2 - 1 = β - 3 by ring, show β - 1 - 1 = β - 2 by ring,
    real_inner_comm v z, real_inner_comm w z]
  ring

/-- The radial Hessian trace in any orthonormal basis is computed exactly. -/
theorem trace_directionalHessian_radialPower {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (β : ℝ) {x : E} (hx : x ≠ 0) :
    (∑ i, directionalHessian (radialPower β) x (b i) (b i)) =
      2 * β * (2 * β + Fintype.card ι - 2) * (‖x‖ ^ 2) ^ (β - 1) := by
  have hS : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  have hsum : (∑ i, inner ℝ x (b i) * inner ℝ x (b i)) = ‖x‖ ^ 2 := by
    simpa only [real_inner_comm (b _), real_inner_self_eq_norm_sq] using b.sum_inner_mul_inner x x
  have hunit (i : ι) : inner ℝ (b i) (b i) = 1 := by
    rw [real_inner_self_eq_norm_sq, b.orthonormal.norm_eq_one]
    norm_num
  simp_rw [directionalHessian_radialPower β hx, hunit, mul_one]
  rw [Finset.sum_add_distrib]
  have he : (∑ i, 4 * β * (β - 1) * (‖x‖ ^ 2) ^ (β - 2) *
      inner ℝ x (b i) * inner ℝ x (b i)) =
      (4 * β * (β - 1) * (‖x‖ ^ 2) ^ (β - 2)) * ‖x‖ ^ 2 := by
    rw [← hsum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hp : (‖x‖ ^ 2) ^ (β - 2) * ‖x‖ ^ 2 = (‖x‖ ^ 2) ^ (β - 1) := by
    rw [← Real.rpow_add_one hS]
    congr 1
    ring
  calc
    _ = 4 * β * (β - 1) * ((‖x‖ ^ 2) ^ (β - 2) * ‖x‖ ^ 2) +
        Fintype.card ι * (2 * β * (‖x‖ ^ 2) ^ (β - 1)) := by ring
    _ = _ := by rw [hp]; ring

/-- The Newtonian homogeneity exponent makes the actual off-origin
Hessian trace vanish in every dimension. In dimension two this power is
constant; the logarithmic kernel must be treated separately. -/
theorem newtonian_power_trace_zero {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) {x : E} (hx : x ≠ 0) :
    (∑ i, directionalHessian (radialPower ((2 - Fintype.card ι) / 2)) x (b i) (b i)) = 0 := by
  rw [trace_directionalHessian_radialPower b _ hx]
  have he : 2 * ((2 - (Fintype.card ι : ℝ)) / 2) + Fintype.card ι - 2 = 0 := by ring
  rw [he]
  ring

lemma abs_inner_le_norm_of_norm_le_one {x v : E} (hv : ‖v‖ ≤ 1) :
    |inner ℝ x v| ≤ ‖x‖ := by
  exact (abs_real_inner_le_norm x v).trans
    (by simpa using mul_le_mul_of_nonneg_left hv (norm_nonneg x))

/-- Sharp homogeneity of the Hessian with an explicit (non-optimal)
coefficient, valid in every pair of unit-bounded directions. -/
theorem directionalHessian_radialPower_bound (β : ℝ) {x : E} (hx : x ≠ 0)
    {v w : E} (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    |directionalHessian (radialPower β) x v w| ≤
      (|4 * β * (β - 1)| + |2 * β|) * (‖x‖ ^ 2) ^ (β - 1) := by
  let S := ‖x‖ ^ 2
  have hS : 0 < S := sq_pos_of_pos (norm_pos_iff.mpr hx)
  have hvx := abs_inner_le_norm_of_norm_le_one (x := x) hv
  have hwx := abs_inner_le_norm_of_norm_le_one (x := x) hw
  have hvw : |inner ℝ v w| ≤ 1 := (abs_inner_le_norm_of_norm_le_one hw).trans hv
  have hprod : |inner ℝ x v| * |inner ℝ x w| ≤ S := by
    exact (mul_le_mul hvx hwx (abs_nonneg _) (norm_nonneg x)).trans_eq (sq ‖x‖).symm
  have hpow : S ^ (β - 2) * S = S ^ (β - 1) := by
    rw [← Real.rpow_add_one hS.ne']
    congr 1
    ring
  rw [directionalHessian_radialPower β hx]
  calc
    _ ≤ |4 * β * (β - 1) * S ^ (β - 2) * inner ℝ x v * inner ℝ x w| +
        |2 * β * S ^ (β - 1) * inner ℝ v w| := abs_add_le _ _
    _ = |4 * β * (β - 1)| * S ^ (β - 2) * (|inner ℝ x v| * |inner ℝ x w|) +
        |2 * β| * S ^ (β - 1) * |inner ℝ v w| := by
      simp only [abs_mul, abs_of_nonneg (Real.rpow_nonneg hS.le _)]
      ring
    _ ≤ |4 * β * (β - 1)| * S ^ (β - 2) * S + |2 * β| * S ^ (β - 1) * 1 := by
      exact add_le_add (mul_le_mul_of_nonneg_left hprod (by positivity))
        (mul_le_mul_of_nonneg_left hvw (by positivity))
    _ = _ := by dsimp [S] at hpow ⊢; rw [mul_assoc _ _ S, hpow]; ring

/-- The degree of the third derivative is one below the Hessian degree.
All derivatives are literal, and the decay constant is explicit. -/
theorem fderiv_directionalHessian_radialPower_bound (β : ℝ) {x : E} (hx : x ≠ 0)
    {v w z : E} (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) (hz : ‖z‖ ≤ 1) :
    |fderiv ℝ (fun y => directionalHessian (radialPower β) y v w) x z| ≤
      (|8 * β * (β - 1) * (β - 2)| + 3 * |4 * β * (β - 1)|) *
        (‖x‖ ^ 2) ^ (β - 2) * ‖x‖ := by
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
  have hpow : S ^ (β - 3) * S = S ^ (β - 2) := by
    rw [← Real.rpow_add_one hS.ne']
    congr 1
    ring
  rw [fderiv_directionalHessian_radialPower β hx]
  calc
    _ ≤ |8 * β * (β - 1) * (β - 2) * S ^ (β - 3) *
        inner ℝ x v * inner ℝ x w * inner ℝ x z| +
        |4 * β * (β - 1) * S ^ (β - 2) *
          (inner ℝ z v * inner ℝ x w + inner ℝ x v * inner ℝ z w + inner ℝ x z * inner ℝ v w)| :=
      abs_add_le _ _
    _ = |8 * β * (β - 1) * (β - 2)| * S ^ (β - 3) *
        (|inner ℝ x v| * |inner ℝ x w| * |inner ℝ x z|) +
        |4 * β * (β - 1)| * S ^ (β - 2) *
          |inner ℝ z v * inner ℝ x w + inner ℝ x v * inner ℝ z w + inner ℝ x z * inner ℝ v w| := by
      simp only [abs_mul, abs_of_nonneg (Real.rpow_nonneg hS.le _)]
      ring
    _ ≤ |8 * β * (β - 1) * (β - 2)| * S ^ (β - 3) * (S * ‖x‖) +
        |4 * β * (β - 1)| * S ^ (β - 2) * (3 * ‖x‖) :=
      add_le_add (mul_le_mul_of_nonneg_left hprod (by positivity))
        (mul_le_mul_of_nonneg_left hsum (by positivity))
    _ = (|8 * β * (β - 1) * (β - 2)| * (S ^ (β - 3) * S) +
        3 * |4 * β * (β - 1)| * S ^ (β - 2)) * ‖x‖ := by ring
    _ = _ := by rw [hpow]; dsimp [S]; ring

/-- The Hessian kernel is continuous on every set avoiding its singularity. -/
lemma continuousOn_directionalHessian_radialPower (β : ℝ) (v w : E)
    {s : Set E} (hs : ∀ x ∈ s, x ≠ 0) :
    ContinuousOn (fun x => directionalHessian (radialPower β) x v w) s := by
  have hp (t : ℝ) : ContinuousOn (fun x : E => (‖x‖ ^ 2) ^ t) s :=
    (continuous_norm.pow 2).continuousOn.rpow_const
      (fun x hx => Or.inl (pow_ne_zero 2 (norm_ne_zero_iff.mpr (hs x hx))))
  have hv : ContinuousOn (fun x : E => inner ℝ x v) s :=
    (continuous_id.inner continuous_const).continuousOn
  have hw : ContinuousOn (fun x : E => inner ℝ x w) s :=
    (continuous_id.inner continuous_const).continuousOn
  have hh : ContinuousOn (fun x : E =>
      4 * β * (β - 1) * (‖x‖ ^ 2) ^ (β - 2) * inner ℝ x v * inner ℝ x w +
        2 * β * (‖x‖ ^ 2) ^ (β - 1) * inner ℝ v w) s :=
    (((continuousOn_const.mul (hp (β - 2))).mul hv).mul hw).add
      ((continuousOn_const.mul (hp (β - 1))).mul continuousOn_const)
  apply hh.congr
  intro x hx
  exact directionalHessian_radialPower β (hs x hx) v w

lemma squaredNorm_rpow (x : E) (t : ℝ) : (‖x‖ ^ 2) ^ t = ‖x‖ ^ (2 * t) := by
  rw [← Real.rpow_natCast ‖x‖ 2, ← Real.rpow_mul (norm_nonneg x)]
  norm_num

/-- Standard norm-power form of the Hessian decay estimate. -/
theorem directionalHessian_radialPower_decay (β : ℝ) {x : E} (hx : x ≠ 0)
    {v w : E} (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    |directionalHessian (radialPower β) x v w| ≤
      (|4 * β * (β - 1)| + |2 * β|) * ‖x‖ ^ (2 * β - 2) := by
  have hh := directionalHessian_radialPower_bound β hx hv hw
  rw [squaredNorm_rpow, show 2 * (β - 1) = 2 * β - 2 by ring] at hh
  exact hh

/-- Standard norm-power form of the third-derivative decay estimate. -/
theorem fderiv_directionalHessian_radialPower_decay (β : ℝ) {x : E} (hx : x ≠ 0)
    {v w z : E} (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) (hz : ‖z‖ ≤ 1) :
    |fderiv ℝ (fun y => directionalHessian (radialPower β) y v w) x z| ≤
      (|8 * β * (β - 1) * (β - 2)| + 3 * |4 * β * (β - 1)|) * ‖x‖ ^ (2 * β - 3) := by
  have hh := fderiv_directionalHessian_radialPower_bound β hx hv hw hz
  rw [squaredNorm_rpow, mul_assoc, ← Real.rpow_add_one (norm_ne_zero_iff.mpr hx)] at hh
  convert hh using 1
  congr 2
  ring

end GaussianTilt.MomentMapElliptic
