import GaussianTilt.MomentMapEllipticFundamentalSolutionCancellation

/-!
# Smooth regularizations of the actual fundamental kernel

A single radial profile covers the power kernels and the logarithmic
kernel in dimension two. Its literal Hessian trace is a positive,
integrable rescaled Japanese-bracket kernel. No distributional delta
identity is assumed in these calculations.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace GaussianTilt.MomentMapElliptic
variable {n : ℕ}

/-- A profile with derivative `t^(-n/2)` on the positive half-line. The
logarithm supplies the exceptional two-dimensional case. -/
def newtonianProfile (n : ℕ) (t : ℝ) : ℝ :=
  if n = 2 then Real.log t else t ^ ((2 - (n : ℝ)) / 2) / ((2 - (n : ℝ)) / 2)

lemma hasDerivAt_newtonianProfile (n : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (newtonianProfile n) (t ^ (-(n : ℝ) / 2)) t := by
  by_cases hn : n = 2
  · subst n
    simpa [newtonianProfile, Real.rpow_neg_one] using Real.hasDerivAt_log ht.ne'
  · have hb : (2 - (n : ℝ)) / 2 ≠ 0 := by
      intro he
      have hnreal : (n : ℝ) = 2 := by linarith
      exact hn (by exact_mod_cast hnreal)
    have hh := (Real.hasDerivAt_rpow_const (p := (2 - (n : ℝ)) / 2) (Or.inl ht.ne')).div_const ((2 - (n : ℝ)) / 2)
    have hexp : (2 - (n : ℝ)) / 2 - 1 = -(n : ℝ) / 2 := by ring
    convert hh using 1
    · funext s
      simp [newtonianProfile, hn]
    · rw [hexp]
      field_simp [show (2 - (n : ℝ)) ≠ 0 from fun hz => hb (by rw [hz, zero_div])]

/-- Squared-radius regularization, globally smooth when `a > 0`. -/
def regularizedNewtonian (n : ℕ) (a : ℝ) (x : KernelSpace n) : ℝ :=
  newtonianProfile n (a + ‖x‖ ^ 2)

lemma hasFDerivAt_regularizedNewtonian {a : ℝ} {x : KernelSpace n}
    (ht : 0 < a + ‖x‖ ^ 2) :
    HasFDerivAt (regularizedNewtonian n a)
      ((2 * (a + ‖x‖ ^ 2) ^ (-(n : ℝ) / 2)) • innerSL ℝ x) x := by
  have hh := (hasDerivAt_newtonianProfile n ht).comp_hasFDerivAt x
    ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_add a)
  convert hh using 1
  ext v
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

lemma fderiv_regularizedNewtonian_apply {a : ℝ} {x : KernelSpace n}
    (ht : 0 < a + ‖x‖ ^ 2) (v : KernelSpace n) :
    fderiv ℝ (regularizedNewtonian n a) x v =
      2 * (a + ‖x‖ ^ 2) ^ (-(n : ℝ) / 2) * inner ℝ x v := by
  rw [(hasFDerivAt_regularizedNewtonian ht).fderiv]
  rfl

/-- The actual regularized Hessian formula includes dimension two without
a separate power-kernel convention. -/
theorem directionalHessian_regularizedNewtonian {a : ℝ} {x : KernelSpace n}
    (ht : 0 < a + ‖x‖ ^ 2) (v w : KernelSpace n) :
    directionalHessian (regularizedNewtonian n a) x v w =
      -(2 * (n : ℝ)) * (a + ‖x‖ ^ 2) ^ (-((n : ℝ) + 2) / 2) * inner ℝ x v * inner ℝ x w +
        2 * (a + ‖x‖ ^ 2) ^ (-(n : ℝ) / 2) * inner ℝ v w := by
  have hp := (((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_add a).rpow_const
    (p := -(n : ℝ) / 2) (Or.inl ht.ne')).const_mul 2
  have hi := hasFDerivAt_inner_right v x
  have hh := hp.mul hi
  have heq : (fun y => fderiv ℝ (regularizedNewtonian n a) y v) =ᶠ[𝓝 x]
      (fun y => (2 * (a + ‖y‖ ^ 2) ^ (-(n : ℝ) / 2)) * inner ℝ y v) := by
    have hop : IsOpen {y : KernelSpace n | 0 < a + ‖y‖ ^ 2} :=
      isOpen_lt continuous_const (continuous_const.add (continuous_norm.pow 2))
    filter_upwards [hop.mem_nhds ht] with y hy
    exact fderiv_regularizedNewtonian_apply hy v
  have hactual := hh.congr_of_eventuallyEq heq
  unfold directionalHessian
  rw [hactual.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, innerSL_apply, show -(n : ℝ) / 2 - 1 = -((n : ℝ) + 2) / 2 by ring]
  ring

/-- The computed Laplacian is exactly a positive approximate-identity
kernel. This identity uses the literal second Fréchet derivatives. -/
theorem trace_directionalHessian_regularizedNewtonian {a : ℝ} {x : KernelSpace n}
    (ht : 0 < a + ‖x‖ ^ 2) :
    (∑ i : Fin n, directionalHessian (regularizedNewtonian n a) x
      (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ i)) =
      2 * (n : ℝ) * a * (a + ‖x‖ ^ 2) ^ (-((n : ℝ) + 2) / 2) := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hsum : (∑ i : Fin n, inner ℝ x (b i) * inner ℝ x (b i)) = ‖x‖ ^ 2 := by
    simpa only [real_inner_comm (b _), real_inner_self_eq_norm_sq] using b.sum_inner_mul_inner x x
  have hunit (i : Fin n) : inner ℝ (b i) (b i) = 1 := by
    rw [real_inner_self_eq_norm_sq, b.orthonormal.norm_eq_one]
    norm_num
  change (∑ i, directionalHessian (regularizedNewtonian n a) x (b i) (b i)) = _
  simp_rw [directionalHessian_regularizedNewtonian ht, hunit, mul_one]
  rw [Finset.sum_add_distrib]
  have he : (∑ i, -(2 * (n : ℝ)) * (a + ‖x‖ ^ 2) ^ (-((n : ℝ) + 2) / 2) *
      inner ℝ x (b i) * inner ℝ x (b i)) =
      (-(2 * (n : ℝ)) * (a + ‖x‖ ^ 2) ^ (-((n : ℝ) + 2) / 2)) * ‖x‖ ^ 2 := by
    rw [← hsum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hp : (a + ‖x‖ ^ 2) ^ (-(n : ℝ) / 2) =
      (a + ‖x‖ ^ 2) ^ (-((n : ℝ) + 2) / 2) * (a + ‖x‖ ^ 2) := by
    rw [← Real.rpow_add_one ht.ne']
    congr 1
    ring
  rw [hp]
  ring

/-- The strictly positive integrable base density arising from the
computed Laplacian of the regularized fundamental kernel. -/
def fundamentalApproxBase (n : ℕ) (x : KernelSpace n) : ℝ :=
  (1 + ‖x‖ ^ 2) ^ (-((n : ℝ) + 2) / 2)

lemma fundamentalApproxBase_pos (x : KernelSpace n) : 0 < fundamentalApproxBase n x := by
  unfold fundamentalApproxBase
  positivity

lemma integrable_fundamentalApproxBase (n : ℕ) : Integrable (fundamentalApproxBase n) := by
  apply integrable_rpow_neg_one_add_norm_sq
  simp [KernelSpace]

/-- The normalization is the actual convergent integral, not an assumed
sphere-area or Gamma-function identity. -/
def fundamentalApproxMass (n : ℕ) : ℝ := ∫ x, fundamentalApproxBase n x

lemma fundamentalApproxMass_pos (n : ℕ) : 0 < fundamentalApproxMass n := by
  apply (integral_pos_iff_support_of_nonneg (fun x => (fundamentalApproxBase_pos x).le)
    (integrable_fundamentalApproxBase n)).mpr
  have he : Function.support (fundamentalApproxBase n) = univ := by
    ext x
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (fundamentalApproxBase_pos x).ne'
  rw [he]
  exact (Metric.isOpen_ball.measure_pos volume
    ⟨0, Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1)⟩).trans_le (measure_mono (subset_univ _))

/-- A genuine probability kernel, in every positive dimension and also in
the harmless zero-dimensional case. -/
def fundamentalApproxDensity (n : ℕ) (x : KernelSpace n) : ℝ :=
  fundamentalApproxBase n x / fundamentalApproxMass n

lemma fundamentalApproxDensity_pos (x : KernelSpace n) : 0 < fundamentalApproxDensity n x :=
  div_pos (fundamentalApproxBase_pos x) (fundamentalApproxMass_pos n)

lemma integral_fundamentalApproxDensity (n : ℕ) :
    (∫ x, fundamentalApproxDensity n x) = 1 := by
  change (∫ x, fundamentalApproxBase n x / fundamentalApproxMass n) = 1
  rw [integral_div]
  exact div_self (fundamentalApproxMass_pos n).ne'

/-- Positive squared-radius regularization is genuinely C∞, including
at its center and in the logarithmic two-dimensional case. -/
theorem contDiff_regularizedNewtonian {a : ℝ} (ha : 0 < a) {k : WithTop ℕ∞} :
    ContDiff ℝ k (regularizedNewtonian n a) := by
  have hh : ContDiff ℝ k (fun x : KernelSpace n => a + ‖x‖ ^ 2) :=
    contDiff_const.add (contDiff_id.norm_sq ℝ)
  have hnz : ∀ x : KernelSpace n, a + ‖x‖ ^ 2 ≠ 0 := fun x => (by positivity : 0 < a + ‖x‖ ^ 2).ne'
  change ContDiff ℝ k (fun x : KernelSpace n => newtonianProfile n (a + ‖x‖ ^ 2))
  by_cases hn : n = 2
  · simp only [newtonianProfile, if_pos hn]
    exact hh.log hnz
  · simp only [newtonianProfile, if_neg hn]
    exact (hh.rpow_const_of_ne hnz).div_const ((2 - (n : ℝ)) / 2)

/-- The base density has the quantitative tail needed by the genuine
approximation-of-identity theorem. -/
lemma fundamentalApproxBase_weighted_bound (x : KernelSpace n) :
    ‖x‖ ^ n * fundamentalApproxBase n x ≤ (1 + ‖x‖ ^ 2)⁻¹ := by
  have hpow : ‖x‖ ^ n ≤ (1 + ‖x‖ ^ 2) ^ ((n : ℝ) / 2) := by
    have he : ‖x‖ ^ n = (‖x‖ ^ 2) ^ ((n : ℝ) / 2) := by
      rw [squaredNorm_rpow, ← Real.rpow_natCast]
      congr 1
      ring
    rw [he]
    exact Real.rpow_le_rpow (sq_nonneg _) (by linarith) (by positivity)
  unfold fundamentalApproxBase
  calc
    ‖x‖ ^ n * (1 + ‖x‖ ^ 2) ^ (-((n : ℝ) + 2) / 2) ≤
        (1 + ‖x‖ ^ 2) ^ ((n : ℝ) / 2) * (1 + ‖x‖ ^ 2) ^ (-((n : ℝ) + 2) / 2) :=
      mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg (by positivity) _)
    _ = (1 + ‖x‖ ^ 2) ^ (-1 : ℝ) := by
      rw [← Real.rpow_add (by positivity)]
      congr 1
      ring
    _ = _ := Real.rpow_neg_one _

lemma fundamentalApproxDensity_weighted_tendsto (n : ℕ) :
    Tendsto (fun x : KernelSpace n => ‖x‖ ^ n * fundamentalApproxDensity n x)
      (Bornology.cobounded (KernelSpace n)) (𝓝 0) := by
  have hgrow : Tendsto (fun x : KernelSpace n => 1 + ‖x‖ ^ 2)
      (Bornology.cobounded (KernelSpace n)) atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [tendsto_norm_cobounded_atTop.eventually (eventually_ge_atTop (max 1 b))] with x hx
    have h1 : 1 ≤ ‖x‖ := (le_max_left _ _).trans hx
    have hb : b ≤ ‖x‖ := (le_max_right _ _).trans hx
    nlinarith
  have hbase : Tendsto (fun x : KernelSpace n => ‖x‖ ^ n * fundamentalApproxBase n x)
      (Bornology.cobounded (KernelSpace n)) (𝓝 0) := by
    exact squeeze_zero (fun x => mul_nonneg (pow_nonneg (norm_nonneg x) n)
      (fundamentalApproxBase_pos x).le) fundamentalApproxBase_weighted_bound
      (tendsto_inv_atTop_zero.comp hgrow)
  simpa only [fundamentalApproxDensity, mul_div_assoc, zero_div] using
    hbase.div_const (fundamentalApproxMass n)

/-- The computed, normalized Laplacian kernel is an actual approximation
of the identity under concentration. This statement is proved from its
positive finite integral and its verified decay. -/
theorem fundamentalApproxDensity_approximate_identity {g : KernelSpace n → ℝ}
    (hg : Integrable g) {x₀ : KernelSpace n} (hgc : ContinuousAt g x₀) :
    Tendsto (fun c : ℝ => ∫ x, (c ^ n * fundamentalApproxDensity n (c • (x₀ - x))) * g x)
      atTop (𝓝 (g x₀)) := by
  have hh := tendsto_integral_comp_smul_smul_of_integrable'
    (fun x : KernelSpace n => (fundamentalApproxDensity_pos x).le)
    (integral_fundamentalApproxDensity n)
    (by simpa only [KernelSpace, finrank_euclideanSpace_fin] using fundamentalApproxDensity_weighted_tendsto n)
    hg hgc
  simpa only [KernelSpace, finrank_euclideanSpace_fin, smul_eq_mul] using hh

end GaussianTilt.MomentMapElliptic
