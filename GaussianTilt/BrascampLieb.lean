import Mathlib

/-!
# One-dimensional Brascamp–Lieb covariance estimates

The smooth finite-interval theorem is proved from the fundamental theorem of
calculus and monotonicity of the derivative of a convex function. Inward Steklov
averaging then proves the nonsmooth continuous-potential version, preserving
the exact strong-convexity constant.  In
particular, a covariance estimate or a Poincaré estimate is not a hypothesis.

The extension to arbitrary-dimensional nonsmooth strongly logconcave densities
requires a separate marginalization theorem; it is not asserted here.
-/

noncomputable section
open MeasureTheory Set
open Filter
open scoped Interval Topology

namespace GaussianTilt.BrascampLieb

/-- The unnormalized density of a finite real potential. -/
def weight (W : ℝ → ℝ) (x : ℝ) : ℝ := Real.exp (-W x)

/-- Normalizing mass on a finite interval. -/
def mass (W : ℝ → ℝ) (a b : ℝ) : ℝ := ∫ x in a..b, weight W x

/-- The mean of the normalized finite-interval density. -/
def mean (W : ℝ → ℝ) (a b : ℝ) : ℝ :=
  (∫ x in a..b, x * weight W x) / mass W a b

/-- Its centered second moment. -/
def variance (W : ℝ → ℝ) (a b : ℝ) : ℝ :=
  (∫ x in a..b, (x - mean W a b) ^ 2 * weight W x) / mass W a b

lemma continuous_weight {W : ℝ → ℝ} (hW : Continuous W) : Continuous (weight W) :=
  Real.continuous_exp.comp hW.neg

lemma weight_pos (W : ℝ → ℝ) (x : ℝ) : 0 < weight W x := Real.exp_pos _

lemma mass_pos {W : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hW : Continuous W) :
    0 < mass W a b := by
  apply intervalIntegral.integral_pos hab (continuous_weight hW).continuousOn
  · intro x _
    exact (weight_pos W x).le
  · exact ⟨a, ⟨le_rfl, hab.le⟩, weight_pos W a⟩

lemma mean_mem_Icc {W : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hW : Continuous W) :
    mean W a b ∈ Icc a b := by
  have hp := continuous_weight hW
  have hZ := mass_pos hab hW
  constructor
  · apply (le_div_iff₀ hZ).2
    have h := intervalIntegral.integral_mono_on (μ := volume) hab.le
      ((continuous_const.mul hp).intervalIntegrable a b) (((show Continuous (fun x : ℝ ↦ x) from continuous_id).mul hp).intervalIntegrable a b)
      (fun x hx ↦ mul_le_mul_of_nonneg_right hx.1 (weight_pos W x).le)
    simpa only [intervalIntegral.integral_const_mul, mass] using h
  · apply (div_le_iff₀ hZ).2
    have h := intervalIntegral.integral_mono_on (μ := volume) hab.le
      (((show Continuous (fun x : ℝ ↦ x) from continuous_id).mul hp).intervalIntegrable a b) ((continuous_const.mul hp).intervalIntegrable a b)
      (fun x hx ↦ mul_le_mul_of_nonneg_right hx.2 (weight_pos W x).le)
    simpa only [intervalIntegral.integral_const_mul, mass] using h

lemma centered_first_moment {W : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hW : Continuous W) :
    (∫ x in a..b, (x - mean W a b) * weight W x) = 0 := by
  have hp := continuous_weight hW
  have hZ : mass W a b ≠ 0 := (mass_pos hab hW).ne'
  simp_rw [sub_mul]
  rw [intervalIntegral.integral_sub (((show Continuous (fun x : ℝ ↦ x) from continuous_id).mul hp).intervalIntegrable a b)
    ((continuous_const.mul hp).intervalIntegrable a b), intervalIntegral.integral_const_mul]
  change _ - ((_ / mass W a b) * mass W a b) = 0
  rw [div_mul_cancel₀ _ hZ, sub_self]

/-- Strong monotonicity of a scalar score gives its pointwise coercivity
about every point of the interval. -/
lemma score_coercivity {s : ℝ → ℝ} {a b κ x m : ℝ}
    (hs : MonotoneOn (fun z ↦ s z - κ * z) (Icc a b))
    (hx : x ∈ Icc a b) (hm : m ∈ Icc a b) :
    κ * (x - m) ^ 2 ≤ (x - m) * (s x - s m) := by
  rcases le_total m x with hmx | hxm
  · have h := hs hm hx hmx
    have hp := mul_nonneg (sub_nonneg.mpr hmx) (sub_nonneg.mpr h)
    nlinarith
  · have h := hs hx hm hxm
    have hp := mul_nonneg (sub_nonneg.mpr hxm) (sub_nonneg.mpr h)
    nlinarith

/-- Integration by parts for the centered coordinate and the exponential
weight.  The boundary term is retained, so this also applies to hard cutoffs. -/
lemma score_integral_eq {W s : ℝ → ℝ} {a b : ℝ}
    (hW : Continuous W) (hs : Continuous s)
    (hd : ∀ x, HasDerivAt W (s x) x) (m : ℝ) :
    (∫ x in a..b, (x - m) * s x * weight W x) =
      mass W a b - ((b - m) * weight W b - (a - m) * weight W a) := by
  have hp := continuous_weight hW
  have hder : ∀ x, HasDerivAt (weight W) (-s x * weight W x) x := by
    intro x
    simpa only [weight, mul_comm] using (hd x).neg.exp
  have h := intervalIntegral.integral_deriv_mul_eq_sub
    (fun x _ ↦ (hasDerivAt_id x).sub_const m) (fun x _ ↦ hder x)
    (continuous_const.intervalIntegrable a b : IntervalIntegrable (fun _ : ℝ ↦ (1 : ℝ)) volume a b)
    ((hs.neg.mul hp).intervalIntegrable a b)
  simp only [id_eq] at h
  have he : (fun x ↦ 1 * weight W x + (x - m) * (-s x * weight W x)) =
      (fun x ↦ weight W x - (x - m) * s x * weight W x) := by
    funext x
    ring
  rw [he, intervalIntegral.integral_sub (hp.intervalIntegrable a b)
    (((((show Continuous (fun x : ℝ ↦ x) from continuous_id).sub continuous_const).mul hs).mul hp).intervalIntegrable a b)] at h
  change mass W a b - _ = _ at h
  linarith

/-- The centered coordinate has score covariance at most one.  This is a
proved integration-by-parts inequality, including the boundary signs. -/
lemma score_integral_le_mass {W s : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hW : Continuous W) (hs : Continuous s)
    (hd : ∀ x, HasDerivAt W (s x) x) :
    (∫ x in a..b, (x - mean W a b) * s x * weight W x) ≤ mass W a b := by
  rw [score_integral_eq hW hs hd]
  obtain ⟨hma, hmb⟩ := mean_mem_Icc hab hW
  have hb := mul_nonneg (sub_nonneg.mpr hmb) (weight_pos W b).le
  have ha := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hma) (weight_pos W a).le
  linarith

/-- One-dimensional covariance bound from a strongly increasing score.
All integral identities are derived from differentiation; there is no
assumed variance or Poincaré bound. -/
theorem variance_le_inv_of_score {W s : ℝ → ℝ} {a b κ : ℝ}
    (hab : a < b) (hκ : 0 < κ) (hW : Continuous W) (hs : Continuous s)
    (hd : ∀ x, HasDerivAt W (s x) x)
    (hmono : MonotoneOn (fun x ↦ s x - κ * x) (Icc a b)) :
    variance W a b ≤ κ⁻¹ := by
  have hp := continuous_weight hW
  let m := mean W a b
  have hm : m ∈ Icc a b := mean_mem_Icc hab hW
  have hi := intervalIntegral.integral_mono_on (μ := volume) hab.le
    (((continuous_const.mul (((show Continuous (fun x : ℝ ↦ x) from continuous_id).sub continuous_const).pow 2)).mul hp).intervalIntegrable a b)
    (((((show Continuous (fun x : ℝ ↦ x) from continuous_id).sub continuous_const).mul (hs.sub continuous_const)).mul hp).intervalIntegrable a b)
    (fun x hx ↦ mul_le_mul_of_nonneg_right (score_coercivity hmono hx hm)
      (weight_pos W x).le)
  have he : (∫ x in a..b, (x - m) * (s x - s m) * weight W x) =
      ∫ x in a..b, (x - m) * s x * weight W x := by
    have hf : (fun x ↦ (x - m) * (s x - s m) * weight W x) =
        (fun x ↦ (x - m) * s x * weight W x - s m * ((x - m) * weight W x)) := by
      funext x
      ring
    rw [hf, intervalIntegral.integral_sub
      (((((show Continuous (fun x : ℝ ↦ x) from continuous_id).sub continuous_const).mul hs).mul hp).intervalIntegrable a b)
      ((continuous_const.mul (((show Continuous (fun x : ℝ ↦ x) from continuous_id).sub continuous_const).mul hp)).intervalIntegrable a b),
      intervalIntegral.integral_const_mul, centered_first_moment hab hW, mul_zero, sub_zero]
  rw [he] at hi
  have hf : (fun x ↦ κ * (x - m) ^ 2 * weight W x) =
      (fun x ↦ κ * ((x - m) ^ 2 * weight W x)) := by
    funext x
    ring
  rw [hf, intervalIntegral.integral_const_mul] at hi
  have hb := hi.trans (score_integral_le_mass hab hW hs hd)
  have hZ := mass_pos hab hW
  dsimp [variance]
  apply (div_le_iff₀ hZ).2
  apply (mul_le_mul_left hκ).mp
  calc
    κ * (∫ x in a..b, (x - mean W a b) ^ 2 * weight W x) ≤ mass W a b := hb
    _ = κ * (κ⁻¹ * mass W a b) := by rw [← mul_assoc, mul_inv_cancel₀ hκ.ne', one_mul]

/-- A differentiable strongly convex potential has a strongly monotone score. -/
lemma score_monotone_of_convex {W s : ℝ → ℝ} {a b κ : ℝ}
    (hd : ∀ x, HasDerivAt W (s x) x)
    (hc : ConvexOn ℝ (Icc a b) (fun x ↦ W x - κ / 2 * x ^ 2)) :
    MonotoneOn (fun x ↦ s x - κ * x) (Icc a b) := by
  have hder : ∀ x, HasDerivAt (fun z ↦ W z - κ / 2 * z ^ 2) (s x - κ * x) x := by
    intro x
    convert (hd x).sub (((hasDerivAt_id x).pow 2).const_mul (κ / 2)) using 1 <;> simp only [id_eq, Nat.cast_ofNat, pow_one] <;> ring
  have h := hc.monotoneOn_deriv (fun x _ ↦ (hder x).differentiableAt)
  intro x hx y hy hxy
  simpa only [(hder x).deriv, (hder y).deriv] using h hx hy hxy

/-- The genuine finite-interval Brascamp–Lieb covariance bound for a C¹
strongly convex potential.  A finite endpoint density is allowed. -/
theorem variance_le_inv {W s : ℝ → ℝ} {a b κ : ℝ}
    (hab : a < b) (hκ : 0 < κ) (hW : Continuous W) (hs : Continuous s)
    (hd : ∀ x, HasDerivAt W (s x) x)
    (hc : ConvexOn ℝ (Icc a b) (fun x ↦ W x - κ / 2 * x ^ 2)) :
    variance W a b ≤ κ⁻¹ :=
  variance_le_inv_of_score hab hκ hW hs hd (score_monotone_of_convex hd hc)

lemma continuous_intervalIntegral {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] [LocallyCompactSpace X]
    {f : X → ℝ → ℝ} (hf : Continuous f.uncurry) {a b : ℝ} (hab : a ≤ b) :
    Continuous (fun z ↦ ∫ x in a..b, f z x) := by
  have h := continuous_parametric_integral_of_continuous (μ := volume) hf (isCompact_Icc (a := a) (b := b))
  simpa only [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc] using h

/-- Averaging a continuous potential over a unit parameter interval. -/
def boxAverage (V : ℝ → ℝ) (δ x : ℝ) : ℝ := ∫ u in (0 : ℝ)..1, V (x + δ * u)

lemma continuous_boxAverage {V : ℝ → ℝ} (hV : Continuous V) :
    Continuous (fun p : ℝ × ℝ ↦ boxAverage V p.1 p.2) := by
  apply continuous_intervalIntegral (a := 0) (b := 1) (hab := by norm_num)
  exact hV.comp (by fun_prop)

@[simp] lemma boxAverage_zero (V : ℝ → ℝ) (x : ℝ) : boxAverage V 0 x = V x := by
  simp [boxAverage]

lemma boxAverage_eq_primitive {V : ℝ → ℝ} (hV : Continuous V) {δ : ℝ} (hδ : δ ≠ 0)
    (x : ℝ) : boxAverage V δ x =
      δ⁻¹ * ((∫ z in (0 : ℝ)..x + δ, V z) - ∫ z in (0 : ℝ)..x, V z) := by
  rw [boxAverage, intervalIntegral.integral_comp_add_mul V hδ x]
  simp only [mul_zero, add_zero, mul_one, smul_eq_mul]
  congr 1
  have h := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hV.intervalIntegrable 0 x) (hV.intervalIntegrable x (x + δ))
  linarith

lemma hasDerivAt_boxAverage {V : ℝ → ℝ} (hV : Continuous V) {δ : ℝ} (hδ : δ ≠ 0)
    (x : ℝ) : HasDerivAt (boxAverage V δ) ((V (x + δ) - V x) / δ) x := by
  have h₁ := ((hV.integral_hasStrictDerivAt 0 (x + δ)).hasDerivAt.comp x
    ((hasDerivAt_id x).add_const δ))
  have h₂ := (hV.integral_hasStrictDerivAt 0 x).hasDerivAt
  convert (h₁.sub h₂).const_mul δ⁻¹ using 1
  · funext z
    exact boxAverage_eq_primitive hV hδ z
  · simp only [mul_one]
    ring

/-- Inward averaging keeps all sampled points in the original interval. -/
def inwardAverage (V : ℝ → ℝ) (a b ε x : ℝ) : ℝ :=
  boxAverage V (ε * (b - a)) ((1 - ε) * x + ε * a)

lemma continuous_inwardAverage {V : ℝ → ℝ} (hV : Continuous V) (a b : ℝ) :
    Continuous (fun p : ℝ × ℝ ↦ inwardAverage V a b p.1 p.2) := by
  change Continuous (fun p : ℝ × ℝ ↦ boxAverage V (p.1 * (b - a)) ((1 - p.1) * p.2 + p.1 * a))
  exact (continuous_boxAverage hV).comp (by fun_prop : Continuous (fun p : ℝ × ℝ ↦ (p.1 * (b - a), (1 - p.1) * p.2 + p.1 * a)))

@[simp] lemma inwardAverage_zero (V : ℝ → ℝ) (a b x : ℝ) :
    inwardAverage V a b 0 x = V x := by simp [inwardAverage]

lemma hasDerivAt_inwardAverage {V : ℝ → ℝ} (hV : Continuous V) {a b ε : ℝ}
    (hab : a < b) (hε : ε ≠ 0) (x : ℝ) :
    HasDerivAt (inwardAverage V a b ε)
      (((V ((1 - ε) * x + ε * a + ε * (b - a)) -
          V ((1 - ε) * x + ε * a)) / (ε * (b - a))) * (1 - ε)) x := by
  have hδ : ε * (b - a) ≠ 0 := mul_ne_zero hε (sub_pos.mpr hab).ne'
  simpa only [id_eq, mul_one] using (hasDerivAt_boxAverage hV hδ _).comp x
    (((hasDerivAt_id x).const_mul (1 - ε)).add_const (ε * a))

lemma inward_point_mem {a b ε x u : ℝ} (hab : a ≤ b) (hε : ε ∈ Icc (0 : ℝ) 1)
    (hx : x ∈ Icc a b) (hu : u ∈ Icc (0 : ℝ) 1) :
    (1 - ε) * x + ε * a + ε * (b - a) * u ∈ Icc a b := by
  have hu' : a + (b - a) * u ∈ Icc a b := by constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hab) hu.1, mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hu.2)]
  have h := (convex_Icc a b) hx hu' (sub_nonneg.mpr hε.2) hε.1 (by ring : (1 - ε) + ε = 1)
  convert h using 1 <;> simp only [smul_eq_mul] <;> ring

lemma convexOn_inwardAverage {V : ℝ → ℝ} (hV : Continuous V) {a b ε : ℝ}
    (hab : a ≤ b) (hε : ε ∈ Icc (0 : ℝ) 1) (hc : ConvexOn ℝ (Icc a b) V) :
    ConvexOn ℝ (Icc a b) (inwardAverage V a b ε) := by
  refine ⟨convex_Icc a b, ?_⟩
  intro x hx y hy α β hα hβ hαβ
  simp only [inwardAverage, boxAverage, smul_eq_mul]
  have h₁ : Continuous (fun u ↦ V ((1 - ε) * x + ε * a + ε * (b - a) * u)) := hV.comp (by fun_prop)
  have h₂ : Continuous (fun u ↦ V ((1 - ε) * y + ε * a + ε * (b - a) * u)) := hV.comp (by fun_prop)
  have h₃ : Continuous (fun u ↦ V ((1 - ε) * (α * x + β * y) + ε * a + ε * (b - a) * u)) := hV.comp (by fun_prop)
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add ((continuous_const.mul h₁).intervalIntegrable 0 1)
      ((continuous_const.mul h₂).intervalIntegrable 0 1)]
  apply intervalIntegral.integral_mono_on (by norm_num) (h₃.intervalIntegrable 0 1)
    (((continuous_const.mul h₁).add (continuous_const.mul h₂)).intervalIntegrable 0 1)
  intro u hu
  have h := hc.2 (inward_point_mem hab hε hx hu) (inward_point_mem hab hε hy hu) hα hβ hαβ
  simp only [smul_eq_mul] at h
  convert h using 1
  congr 1
  linear_combination -(ε * a + ε * (b - a) * u) * hαβ


/-- Smoothing only the convex residual preserves the strong-convexity constant. -/
def regularizedPotential (W : ℝ → ℝ) (κ a b ε x : ℝ) : ℝ :=
  inwardAverage (fun z ↦ W z - κ / 2 * z ^ 2) a b ε x + κ / 2 * x ^ 2

@[simp] lemma regularizedPotential_zero (W : ℝ → ℝ) (κ a b : ℝ) :
    regularizedPotential W κ a b 0 = W := by
  funext x
  simp [regularizedPotential]

lemma continuous_regularizedPotential {W : ℝ → ℝ} (hW : Continuous W) (κ a b : ℝ) :
    Continuous (fun p : ℝ × ℝ ↦ regularizedPotential W κ a b p.1 p.2) := by
  exact (continuous_inwardAverage (hW.sub (by fun_prop)) a b).add (by fun_prop)

lemma convexOn_regularizedPotential {W : ℝ → ℝ} (hW : Continuous W) {κ a b ε : ℝ}
    (hab : a ≤ b) (hε : ε ∈ Icc (0 : ℝ) 1)
    (hc : ConvexOn ℝ (Icc a b) (fun x ↦ W x - κ / 2 * x ^ 2)) :
    ConvexOn ℝ (Icc a b) (fun x ↦ regularizedPotential W κ a b ε x - κ / 2 * x ^ 2) := by
  simpa only [regularizedPotential, add_sub_cancel_right] using
    convexOn_inwardAverage (hW.sub (by fun_prop)) hab hε hc

lemma regularizedPotential_has_continuous_score {W : ℝ → ℝ} (hW : Continuous W)
    {κ a b ε : ℝ} (hab : a < b) (hε : ε ≠ 0) :
    ∃ s : ℝ → ℝ, Continuous s ∧ ∀ x, HasDerivAt (regularizedPotential W κ a b ε) (s x) x := by
  let V : ℝ → ℝ := fun z ↦ W z - κ / 2 * z ^ 2
  have hV : Continuous V := hW.sub (by fun_prop)
  let s : ℝ → ℝ := fun x ↦
    ((V ((1 - ε) * x + ε * a + ε * (b - a)) - V ((1 - ε) * x + ε * a)) /
      (ε * (b - a))) * (1 - ε) + κ * x
  refine ⟨s, ?_, ?_⟩
  · dsimp [s]
    fun_prop
  · intro x
    have hd := (hasDerivAt_inwardAverage hV hab hε x).add
      (((hasDerivAt_id x).pow 2).const_mul (κ / 2))
    convert hd using 1 <;> simp only [regularizedPotential, s, V, id_eq, Nat.cast_ofNat, pow_one] <;> ring

/-- Normalized variance is continuous under a jointly continuous family of
finite potentials on a fixed finite interval. -/
lemma continuous_variance {W : ℝ → ℝ → ℝ} (hW : Continuous W.uncurry)
    {a b : ℝ} (hab : a < b) : Continuous (fun ε ↦ variance (W ε) a b) := by
  have hp : Continuous (fun p : ℝ × ℝ ↦ weight (W p.1) p.2) := Real.continuous_exp.comp hW.neg
  have hZ : Continuous (fun ε ↦ mass (W ε) a b) := continuous_intervalIntegral hp hab.le
  have hW' : ∀ ε, Continuous (W ε) := fun ε ↦ hW.comp (by fun_prop : Continuous (fun x : ℝ ↦ (ε, x)))
  have hm : Continuous (fun ε ↦ mean (W ε) a b) := by
    apply Continuous.div (continuous_intervalIntegral (continuous_snd.mul hp) hab.le) hZ
    intro ε
    exact (mass_pos hab (hW' ε)).ne'
  apply Continuous.div ?_ hZ (fun ε ↦ (mass_pos hab (hW' ε)).ne')
  apply continuous_intervalIntegral (hab := hab.le)
  exact ((continuous_snd.sub (hm.comp continuous_fst)).pow 2).mul hp

/-- Finite-interval Brascamp–Lieb for a continuous, possibly nonsmooth,
strongly convex potential. Inward Steklov averaging supplies the C¹
approximants, and their actual normalized moments converge by continuity. -/
theorem variance_le_inv_of_continuous {W : ℝ → ℝ} {a b κ : ℝ}
    (hab : a < b) (hκ : 0 < κ) (hW : Continuous W)
    (hc : ConvexOn ℝ (Icc a b) (fun x ↦ W x - κ / 2 * x ^ 2)) :
    variance W a b ≤ κ⁻¹ := by
  have hcont : Continuous (fun ε ↦ variance (regularizedPotential W κ a b ε) a b) :=
    continuous_variance (W := regularizedPotential W κ a b) (continuous_regularizedPotential hW κ a b) hab
  have hlim := hcont.continuousAt.tendsto.comp tendsto_one_div_add_atTop_nhds_zero_nat
  simp only [regularizedPotential_zero] at hlim
  apply le_of_tendsto hlim
  filter_upwards [] with n
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hε : (1 / ((n : ℝ) + 1)) ∈ Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · apply (div_le_one hn).2
      linarith [Nat.cast_nonneg (α := ℝ) n]
  obtain ⟨s, hs, hd⟩ := regularizedPotential_has_continuous_score (κ := κ) hW hab
    (one_div_ne_zero hn.ne')
  apply variance_le_inv hab hκ ?_ hs hd (convexOn_regularizedPotential hW hab.le hε hc)
  exact (continuous_regularizedPotential hW κ a b).comp
    (by fun_prop : Continuous (fun x : ℝ ↦ (1 / ((n : ℝ) + 1), x)))


lemma variance_congr {W V : ℝ → ℝ} {a b : ℝ} (h : EqOn W V (uIcc a b)) :
    variance W a b = variance V a b := by
  have hZ : mass W a b = mass V a b := by
    apply intervalIntegral.integral_congr
    intro x hx
    simp only [weight, h hx]
  have hm : mean W a b = mean V a b := by
    unfold mean
    rw [hZ]
    congr 1
    apply intervalIntegral.integral_congr
    intro x hx
    simp only [weight, h hx]
  unfold variance
  rw [hZ, hm]
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  simp only [weight, h hx]

/-- The potential need only be continuous on the actual interval of integration. -/
theorem variance_le_inv_of_continuousOn {W : ℝ → ℝ} {a b κ : ℝ}
    (hab : a < b) (hκ : 0 < κ) (hW : ContinuousOn W (Icc a b))
    (hc : ConvexOn ℝ (Icc a b) (fun x ↦ W x - κ / 2 * x ^ 2)) :
    variance W a b ≤ κ⁻¹ := by
  let V : ℝ → ℝ := fun x ↦ W (max a (min b x))
  have hV : Continuous V := hW.comp_continuous (by fun_prop)
    (fun x ↦ ⟨le_max_left _ _, max_le hab.le (min_le_left _ _)⟩)
  have he : EqOn W V (Icc a b) := by
    intro x hx
    simp [V, min_eq_right hx.2, max_eq_right hx.1]
  have hcV : ConvexOn ℝ (Icc a b) (fun x ↦ V x - κ / 2 * x ^ 2) :=
    hc.congr (fun x hx ↦ by rw [he hx])
  rw [variance_congr (by simpa only [uIcc_of_le hab.le] using he)]
  exact variance_le_inv_of_continuous hab hκ hV hcV

lemma variance_eq_moments {W : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hW : Continuous W) :
    variance W a b = (∫ x in a..b, x ^ 2 * weight W x) / mass W a b - (mean W a b) ^ 2 := by
  have hp := continuous_weight hW
  have hi₀ := hp.intervalIntegrable a b (μ := volume)
  have hi₁ := ((show Continuous (fun x : ℝ ↦ x) from continuous_id).mul hp).intervalIntegrable a b (μ := volume)
  have hi₂ := ((show Continuous (fun x : ℝ ↦ x ^ 2) by fun_prop).mul hp).intervalIntegrable a b (μ := volume)
  have hf : (fun x ↦ (x - mean W a b) ^ 2 * weight W x) =
      (fun x ↦ x ^ 2 * weight W x - (2 * mean W a b) * (x * weight W x) + (mean W a b) ^ 2 * weight W x) := by
    funext x
    ring
  unfold variance
  rw [hf, intervalIntegral.integral_add (hi₂.sub (hi₁.const_mul _)) (hi₀.const_mul _),
    intervalIntegral.integral_sub hi₂ (hi₁.const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  have hZ := (mass_pos hab hW).ne'
  unfold mean mass
  dsimp [mass] at hZ
  field_simp [hZ]
  <;> ring

/-- An explicit supporting affine function for an everywhere finite convex
potential, using one-sided derivatives rather than differentiability. -/
lemma convex_affine_lower {V : ℝ → ℝ} (hc : ConvexOn ℝ univ V) :
    ∃ m : ℝ, ∀ x, V 0 + m * x ≤ V x := by
  let m := derivWithin V (Iio 0) 0
  refine ⟨m, ?_⟩
  intro x
  have h0 : (0 : ℝ) ∈ interior (univ : Set ℝ) := by simp
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have h := hc.slope_le_leftDeriv_of_mem_interior (mem_univ x) h0 hx
    simp only [slope_def_field, zero_sub] at h
    have hh := (div_le_iff₀ (neg_pos.mpr hx)).mp h
    dsimp [m]
    nlinarith
  · simp
  · have h := (hc.leftDeriv_le_rightDeriv_of_mem_interior h0).trans
      (hc.rightDeriv_le_slope_of_mem_interior h0 (mem_univ x) hx)
    simp only [slope_def_field, sub_zero] at h
    have hh := (le_div_iff₀ hx).mp h
    dsimp [m]
    linarith

lemma continuous_of_stronglyConvex {W : ℝ → ℝ} {κ : ℝ}
    (hc : ConvexOn ℝ univ (fun x ↦ W x - κ / 2 * x ^ 2)) : Continuous W := by
  have hV := continuousOn_univ.mp (ConvexOn.continuousOn isOpen_univ hc)
  convert hV.add (show Continuous (fun x : ℝ ↦ κ / 2 * x ^ 2) by fun_prop) using 1
  funext x
  ring

lemma weight_gaussian_bound {W : ℝ → ℝ} {κ : ℝ} (hκ : 0 < κ)
    (hc : ConvexOn ℝ univ (fun x ↦ W x - κ / 2 * x ^ 2)) :
    ∃ C : ℝ, ∀ x, weight W x ≤ Real.exp C * Real.exp (-(κ / 4) * x ^ 2) := by
  obtain ⟨m, hm⟩ := convex_affine_lower hc
  refine ⟨m ^ 2 / κ - W 0, ?_⟩
  intro x
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := hm x
  simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero] at h
  have hsq := sq_nonneg (κ * x + 2 * m)
  have hdiv : m ^ 2 / κ * κ = m ^ 2 := div_mul_cancel₀ _ hκ.ne'
  have hm0 : 0 ≤ κ / 4 * x ^ 2 + m * x + m ^ 2 / κ := by
    apply (mul_nonneg_iff_of_pos_left hκ).mp
    nlinarith
  nlinarith

lemma integrable_pow_mul_weight {W : ℝ → ℝ} {κ : ℝ} (hκ : 0 < κ)
    (hc : ConvexOn ℝ univ (fun x ↦ W x - κ / 2 * x ^ 2)) (k : ℕ) :
    Integrable (fun x ↦ x ^ k * weight W x) := by
  have hW := continuous_of_stronglyConvex hc
  obtain ⟨C, hC⟩ := weight_gaussian_bound hκ hc
  have hg : Integrable (fun x : ℝ ↦ x ^ k * Real.exp (-(κ / 4) * x ^ 2)) := by
    simpa only [Real.rpow_natCast] using
      (integrable_rpow_mul_exp_neg_mul_sq (by linarith : 0 < κ / 4)
        (s := (k : ℝ)) (by linarith [Nat.cast_nonneg (α := ℝ) k]))
  apply (hg.norm.const_mul (Real.exp C)).mono' (by unfold weight; fun_prop)
  filter_upwards [] with x
  rw [norm_mul, Real.norm_of_nonneg (weight_pos W x).le, norm_mul,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  have h := mul_le_mul_of_nonneg_left (hC x) (norm_nonneg (x ^ k))
  nlinarith

/-- The full-line normalized second central moment. -/
def fullVariance (W : ℝ → ℝ) : ℝ :=
  (∫ x, x ^ 2 * weight W x) / (∫ x, weight W x) -
    ((∫ x, x * weight W x) / (∫ x, weight W x)) ^ 2

/-- Full-line, nonsmooth Brascamp–Lieb in one dimension for finite potentials.
Moment existence is derived from strong convexity, rather than assumed. -/
theorem fullVariance_le_inv {W : ℝ → ℝ} {κ : ℝ} (hκ : 0 < κ)
    (hc : ConvexOn ℝ univ (fun x ↦ W x - κ / 2 * x ^ 2)) :
    fullVariance W ≤ κ⁻¹ := by
  have hW := continuous_of_stronglyConvex hc
  have hi₀ : Integrable (weight W) := by simpa using integrable_pow_mul_weight hκ hc 0
  have hi₁ : Integrable (fun x ↦ x * weight W x) := by simpa using integrable_pow_mul_weight hκ hc 1
  have hi₂ := integrable_pow_mul_weight hκ hc 2
  have hZ : (∫ x, weight W x) ≠ 0 := by
    have hpos := integral_exp_pos (f := fun x ↦ - W x) hi₀
    exact hpos.ne'
  have hb : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have ha : Tendsto (fun n : ℕ ↦ -((n : ℝ) + 1)) atTop atBot := tendsto_neg_atTop_atBot.comp hb
  have h₀ := intervalIntegral_tendsto_integral hi₀ ha hb
  have h₁ := intervalIntegral_tendsto_integral hi₁ ha hb
  have h₂ := intervalIntegral_tendsto_integral hi₂ ha hb
  have hlim := (h₂.div h₀ hZ).sub ((h₁.div h₀ hZ).pow 2)
  apply le_of_tendsto hlim
  filter_upwards [] with n
  have hab : -((n : ℝ) + 1) < (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  change (∫ x in -((n : ℝ) + 1)..(n : ℝ) + 1, x ^ 2 * weight W x) /
    mass W (-((n : ℝ) + 1)) ((n : ℝ) + 1) - (mean W (-((n : ℝ) + 1)) ((n : ℝ) + 1)) ^ 2 ≤ κ⁻¹
  rw [← variance_eq_moments hab hW]
  exact variance_le_inv_of_continuous hab hκ hW (hc.subset (subset_univ _) (convex_Icc _ _))


end GaussianTilt.BrascampLieb
