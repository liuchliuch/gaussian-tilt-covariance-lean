import GaussianTilt.BrascampLieb

/-!
# One-dimensional Prékopa–Leindler by monotone transport

The transport below is constructed from the actual primitives of the two
densities. Its derivative is derived by the inverse function theorem. No
functional inequality or marginalization statement is assumed.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Interval Topology
namespace GaussianTilt.Prekopa

lemma primitive_strictMono {f : ℝ → ℝ} (hf : Continuous f) (hp : ∀ x, 0 < f x) (a : ℝ) :
    StrictMono (fun x ↦ ∫ z in a..x, f z) := by
  intro x y hxy
  have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hf.intervalIntegrable a x) (hf.intervalIntegrable x y)
  have hi : 0 < ∫ z in x..y, f z := intervalIntegral.integral_pos hxy hf.continuousOn
    (fun z _ ↦ (hp z).le) ⟨x, ⟨le_rfl, hxy.le⟩, hp x⟩
  linarith

/-- The arithmetic-geometric mean inequality is the entire pointwise
Jacobian estimate in the one-dimensional transport proof. -/
lemma transport_jacobian_bound {f g α β : ℝ} (hf : 0 < f) (hg : 0 < g)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + β = 1) :
    f ≤ (f ^ α * g ^ β) * (α + β * (f / g)) := by
  have h := Real.geom_mean_le_arith_mean2_weighted hα hβ (by norm_num : (0 : ℝ) ≤ 1)
    (div_nonneg hf.le hg.le) hαβ
  simp only [Real.one_rpow, one_mul, mul_one] at h
  have he : (f ^ α * g ^ β) * (f / g) ^ β = f := by
    rw [Real.div_rpow hf.le hg.le]
    have hg' : g ^ β ≠ 0 := (Real.rpow_pos_of_pos hg β).ne'
    calc
      (f ^ α * g ^ β) * (f ^ β / g ^ β) = f ^ α * f ^ β := by field_simp
      _ = f := by rw [← Real.rpow_add hf, hαβ, Real.rpow_one]
  calc
    f = (f ^ α * g ^ β) * (f / g) ^ β := he.symm
    _ ≤ (f ^ α * g ^ β) * (α + β * (f / g)) :=
      mul_le_mul_of_nonneg_left h (by positivity)

/-- Prékopa–Leindler on two finite intervals, for positive continuous
unit-mass densities. The increasing transport is constructed internally. -/
theorem integral_ge_one_of_normalized {f g h : ℝ → ℝ} {a b c d α β : ℝ}
    (hab : a < b) (hcd : c < d) (hf : Continuous f) (hg : Continuous g) (hh : Continuous h)
    (hfp : ∀ x, 0 < f x) (hgp : ∀ x, 0 < g x)
    (hf1 : (∫ x in a..b, f x) = 1) (hg1 : (∫ y in c..d, g y) = 1)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + β = 1)
    (hmajor : ∀ x ∈ Icc a b, ∀ y ∈ Icc c d,
      f x ^ α * g y ^ β ≤ h (α * x + β * y)) :
    1 ≤ ∫ z in α * a + β * c..α * b + β * d, h z := by
  let F : ℝ → ℝ := fun x ↦ ∫ z in a..x, f z
  let G : ℝ → ℝ := fun y ↦ ∫ z in c..y, g z
  have hFm : StrictMono F := primitive_strictMono hf hfp a
  have hGm : StrictMono G := primitive_strictMono hg hgp c
  have hFd : ∀ x, HasStrictDerivAt F (f x) x := hf.integral_hasStrictDerivAt a
  have hGd : ∀ y, HasStrictDerivAt G (g y) y := hg.integral_hasStrictDerivAt c
  have hGc : Continuous G := intervalIntegral.continuous_primitive (hg.intervalIntegrable) c
  have hFa : F a = 0 := by simp [F]
  have hFb : F b = 1 := hf1
  have hGc0 : G c = 0 := by simp [G]
  have hGd1 : G d = 1 := hg1
  have hGimage : G '' Icc c d = Icc 0 1 := by
    rw [ContinuousOn.image_Icc_of_monotoneOn hcd.le hGc.continuousOn (hGm.monotone.monotoneOn (Icc c d)), hGc0, hGd1]
  let T : ℝ → ℝ := fun x ↦ Function.invFun G (F x)
  have hGT : ∀ x ∈ Icc a b, G (T x) = F x := by
    intro x hx
    have hFx : F x ∈ Icc (0 : ℝ) 1 := by
      rw [← hFa, ← hFb]
      exact ⟨hFm.monotone hx.1, hFm.monotone hx.2⟩
    rw [← hGimage] at hFx
    rcases hFx with ⟨y, hy, he⟩
    exact Function.invFun_eq ⟨y, he⟩
  have hTmem : ∀ x ∈ Icc a b, T x ∈ Icc c d := by
    intro x hx
    constructor
    · apply hGm.le_iff_le.mp
      rw [hGT x hx, hGc0, ← hFa]
      exact hFm.monotone hx.1
    · apply hGm.le_iff_le.mp
      rw [hGT x hx, hGd1, ← hFb]
      exact hFm.monotone hx.2
  have hTa : T a = c := by
    apply hGm.injective
    rw [hGT a ⟨le_rfl, hab.le⟩, hFa, hGc0]
  have hTb : T b = d := by
    apply hGm.injective
    rw [hGT b ⟨hab.le, le_rfl⟩, hFb, hGd1]
  have hTd : ∀ x ∈ Icc a b, HasDerivAt T (f x / g (T x)) x := by
    intro x hx
    have hinv := (hGd (T x)).to_local_left_inverse (hgp (T x)).ne'
      (Filter.Eventually.of_forall (Function.leftInverse_invFun hGm.injective))
    rw [hGT x hx] at hinv
    convert hinv.hasDerivAt.comp x (hFd x).hasDerivAt using 1 <;> simp [T, div_eq_mul_inv, mul_comm]
  have hTc : ContinuousOn T (Icc a b) := fun x hx ↦ (hTd x hx).continuousAt.continuousWithinAt
  let S : ℝ → ℝ := fun x ↦ α * x + β * T x
  let J : ℝ → ℝ := fun x ↦ α + β * (f x / g (T x))
  have hSd : ∀ x ∈ Icc a b, HasDerivAt S (J x) x := by
    intro x hx
    simpa only [S, J, id_eq, mul_one] using
      ((hasDerivAt_id x).const_mul α).add ((hTd x hx).const_mul β)
  have hJc : ContinuousOn J (Icc a b) := by
    apply continuousOn_const.add
    apply continuousOn_const.mul
    exact hf.continuousOn.div (hg.continuousOn.comp hTc (mapsTo_univ _ _)) (fun x _ ↦ (hgp (T x)).ne')
  have hSc : ContinuousOn S (Icc a b) := fun x hx ↦ (hSd x hx).continuousAt.continuousWithinAt
  have he := intervalIntegral.integral_comp_mul_deriv (a := a) (b := b)
    (f := S) (f' := J) (g := h)
    (by simpa only [uIcc_of_le hab.le] using hSd)
    (by simpa only [uIcc_of_le hab.le] using hJc) hh
  have hib : IntervalIntegrable (fun x ↦ h (S x) * J x) volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hab.le] using (hh.continuousOn.comp hSc (mapsTo_univ _ _)).mul hJc
  have hbound : (∫ x in a..b, f x) ≤ ∫ x in a..b, h (S x) * J x := by
    apply intervalIntegral.integral_mono_on hab.le (hf.intervalIntegrable a b) hib
    intro x hx
    have hJ : 0 ≤ J x := add_nonneg hα (mul_nonneg hβ (div_nonneg (hfp x).le (hgp (T x)).le))
    exact (transport_jacobian_bound (hfp x) (hgp (T x)) hα hβ hαβ).trans
      (mul_le_mul_of_nonneg_right (hmajor x hx (T x) (hTmem x hx)) hJ)
  simp only [Function.comp_apply] at he
  rw [hf1, he] at hbound
  simpa only [S, hTa, hTb] using hbound


/-- Finite-interval Prékopa–Leindler with arbitrary positive masses. -/
theorem integral_rpow_mul_le {f g h : ℝ → ℝ} {a b c d α β : ℝ}
    (hab : a < b) (hcd : c < d) (hf : Continuous f) (hg : Continuous g) (hh : Continuous h)
    (hfp : ∀ x, 0 < f x) (hgp : ∀ x, 0 < g x)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + β = 1)
    (hmajor : ∀ x ∈ Icc a b, ∀ y ∈ Icc c d,
      f x ^ α * g y ^ β ≤ h (α * x + β * y)) :
    (∫ x in a..b, f x) ^ α * (∫ y in c..d, g y) ^ β ≤
      ∫ z in α * a + β * c..α * b + β * d, h z := by
  let A : ℝ := ∫ x in a..b, f x
  let B : ℝ := ∫ y in c..d, g y
  have hA : 0 < A := intervalIntegral.integral_pos hab hf.continuousOn
    (fun x _ ↦ (hfp x).le) ⟨a, ⟨le_rfl, hab.le⟩, hfp a⟩
  have hB : 0 < B := intervalIntegral.integral_pos hcd hg.continuousOn
    (fun y _ ↦ (hgp y).le) ⟨c, ⟨le_rfl, hcd.le⟩, hgp c⟩
  have hC : 0 < A ^ α * B ^ β := mul_pos (Real.rpow_pos_of_pos hA _) (Real.rpow_pos_of_pos hB _)
  have hn := integral_ge_one_of_normalized (f := fun x ↦ f x / A) (g := fun y ↦ g y / B)
    (h := fun z ↦ h z / (A ^ α * B ^ β)) hab hcd (hf.div_const A) (hg.div_const B)
    (hh.div_const _) (fun x ↦ div_pos (hfp x) hA) (fun y ↦ div_pos (hgp y) hB)
    (by rw [intervalIntegral.integral_div]; exact div_self hA.ne')
    (by rw [intervalIntegral.integral_div]; exact div_self hB.ne') hα hβ hαβ ?_
  · rw [intervalIntegral.integral_div, le_div_iff₀ hC, one_mul] at hn
    exact hn
  · intro x hx y hy
    rw [Real.div_rpow (hfp x).le hA.le, Real.div_rpow (hgp y).le hB.le, div_mul_div_comm]
    exact div_le_div_of_nonneg_right (hmajor x hx y hy) hC.le

/-- Full-line Prékopa–Leindler for positive continuous integrable densities.
It follows by exhaustion by finite intervals, using actual integral limits. -/
theorem integral_rpow_mul_le_integral {f g h : ℝ → ℝ} {α β : ℝ}
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h)
    (hfp : ∀ x, 0 < f x) (hgp : ∀ x, 0 < g x)
    (hfi : Integrable f) (hgi : Integrable g) (hhi : Integrable h)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + β = 1)
    (hmajor : ∀ x y, f x ^ α * g y ^ β ≤ h (α * x + β * y)) :
    (∫ x, f x) ^ α * (∫ y, g y) ^ β ≤ ∫ z, h z := by
  have hb : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have ha := tendsto_neg_atTop_atBot.comp hb
  have hfLim := (intervalIntegral_tendsto_integral hfi ha hb).rpow_const (Or.inr hα)
  have hgLim := (intervalIntegral_tendsto_integral hgi ha hb).rpow_const (Or.inr hβ)
  have hhLim := intervalIntegral_tendsto_integral hhi ha hb
  apply le_of_tendsto_of_tendsto (hfLim.mul hgLim) hhLim
  filter_upwards [] with n
  have hn : -((n : ℝ) + 1) < (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have h := integral_rpow_mul_le hn hn hf hg hh hfp hgp hα hβ hαβ
    (fun x _ y _ ↦ hmajor x y)
  have he₁ : α * -((n : ℝ) + 1) + β * -((n : ℝ) + 1) = -((n : ℝ) + 1) := by
    rw [← add_mul, hαβ, one_mul]
  have he₂ : α * ((n : ℝ) + 1) + β * ((n : ℝ) + 1) = (n : ℝ) + 1 := by
    rw [← add_mul, hαβ, one_mul]
  simpa only [he₁, he₂] using h

/-- Integrating out one coordinate over a finite interval preserves
logconcavity for positive continuous functions. This is a proved marginal
result, with Prékopa–Leindler supplied by the transport construction above. -/
theorem finite_marginal_logconcave {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E × ℝ → ℝ} {a b : ℝ} (hab : a < b) (hf : Continuous f)
    (hfp : ∀ p, 0 < f p)
    (hlc : ∀ x y : E, ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, ∀ α β : ℝ,
      0 ≤ α → 0 ≤ β → α + β = 1 →
      f (x, u) ^ α * f (y, v) ^ β ≤ f (α • x + β • y, α * u + β * v)) :
    ∀ x y : E, ∀ α β : ℝ, 0 ≤ α → 0 ≤ β → α + β = 1 →
      (∫ u in a..b, f (x, u)) ^ α * (∫ v in a..b, f (y, v)) ^ β ≤
        ∫ z in a..b, f (α • x + β • y, z) := by
  intro x y α β hα hβ hαβ
  have h := integral_rpow_mul_le hab hab
    (hf.comp (continuous_const.prodMk continuous_id))
    (hf.comp (continuous_const.prodMk continuous_id))
    (hf.comp (continuous_const.prodMk continuous_id))
    (fun u ↦ hfp (x, u)) (fun v ↦ hfp (y, v)) hα hβ hαβ
    (fun u hu v hv ↦ hlc x y u hu v hv α β hα hβ hαβ)
  simpa only [← add_mul, hαβ, one_mul] using h

/-- The full one-coordinate Prékopa marginal theorem for continuous positive
functions with integrable slices. -/
theorem marginal_logconcave {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E × ℝ → ℝ} (hf : Continuous f) (hfp : ∀ p, 0 < f p)
    (hfi : ∀ x, Integrable (fun u ↦ f (x, u)))
    (hlc : ∀ x y : E, ∀ u v α β : ℝ, 0 ≤ α → 0 ≤ β → α + β = 1 →
      f (x, u) ^ α * f (y, v) ^ β ≤ f (α • x + β • y, α * u + β * v)) :
    ∀ x y : E, ∀ α β : ℝ, 0 ≤ α → 0 ≤ β → α + β = 1 →
      (∫ u, f (x, u)) ^ α * (∫ v, f (y, v)) ^ β ≤
        ∫ z, f (α • x + β • y, z) := by
  intro x y α β hα hβ hαβ
  exact integral_rpow_mul_le_integral
    (hf.comp (continuous_const.prodMk continuous_id))
    (hf.comp (continuous_const.prodMk continuous_id))
    (hf.comp (continuous_const.prodMk continuous_id))
    (fun u ↦ hfp (x, u)) (fun v ↦ hfp (y, v))
    (hfi x) (hfi y) (hfi (α • x + β • y)) hα hβ hαβ
    (fun u v ↦ hlc x y u v α β hα hβ hαβ)


/-- Finite-interval Prékopa–Leindler for continuous nonnegative densities.
Zeros are removed by a positive perturbation; the explicit error tends to
zero, so no strict positivity remains in the statement. -/
theorem integral_rpow_mul_le_of_nonneg {f g h : ℝ → ℝ} {a b c d α β : ℝ}
    (hab : a < b) (hcd : c < d) (hf : Continuous f) (hg : Continuous g) (hh : Continuous h)
    (hfp : ∀ x, 0 ≤ f x) (hgp : ∀ x, 0 ≤ g x)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + β = 1)
    (hmajor : ∀ x ∈ Icc a b, ∀ y ∈ Icc c d,
      f x ^ α * g y ^ β ≤ h (α * x + β * y)) :
    (∫ x in a..b, f x) ^ α * (∫ y in c..d, g y) ^ β ≤
      ∫ z in α * a + β * c..α * b + β * d, h z := by
  by_cases hα0 : α = 0
  · have hβ1 : β = 1 := by linarith
    simp only [hα0, hβ1, Real.rpow_zero, Real.rpow_one, zero_mul, one_mul, zero_add] at *
    exact intervalIntegral.integral_mono_on hcd.le (hg.intervalIntegrable c d)
      (hh.intervalIntegrable c d) (fun y hy ↦ hmajor a ⟨le_rfl, hab.le⟩ y hy)
  by_cases hβ0 : β = 0
  · have hα1 : α = 1 := by linarith
    simp only [hβ0, hα1, Real.rpow_zero, Real.rpow_one, zero_mul, one_mul, mul_one, add_zero] at *
    exact intervalIntegral.integral_mono_on hab.le (hf.intervalIntegrable a b)
      (hh.intervalIntegrable a b) (fun x hx ↦ hmajor x hx c ⟨le_rfl, hcd.le⟩)
  have hαp : 0 < α := lt_of_le_of_ne hα (Ne.symm hα0)
  have hβp : 0 < β := lt_of_le_of_ne hβ (Ne.symm hβ0)
  obtain ⟨A, hA⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    ((hf.rpow_const (fun _ ↦ Or.inr hα)).continuousOn)
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := c) (b := d)).exists_bound_of_continuousOn
    ((hg.rpow_const (fun _ ↦ Or.inr hβ)).continuousOn)
  have hA' : ∀ x ∈ Icc a b, f x ^ α ≤ A := fun x hx ↦ (le_abs_self _).trans (hA x hx)
  have hB' : ∀ y ∈ Icc c d, g y ^ β ≤ B := fun y hy ↦ (le_abs_self _).trans (hB y hy)
  let δ : ℝ → ℝ := fun ε ↦ A * ε ^ β + B * ε ^ α + ε
  have hδc : Continuous δ := by
    exact ((continuous_const.mul (Real.continuous_rpow_const hβ)).add
      (continuous_const.mul (Real.continuous_rpow_const hα))).add continuous_id
  have hδ0 : δ 0 = 0 := by simp [δ, Real.zero_rpow hα0, Real.zero_rpow hβ0]
  have hbound : ∀ ε, 0 < ε →
      (∫ x in a..b, f x + ε) ^ α * (∫ y in c..d, g y + ε) ^ β ≤
        ∫ z in α * a + β * c..α * b + β * d, h z + δ ε := by
    intro ε hε
    apply integral_rpow_mul_le hab hcd (hf.add continuous_const) (hg.add continuous_const)
      (hh.add continuous_const) (fun x ↦ add_pos_of_nonneg_of_pos (hfp x) hε)
      (fun y ↦ add_pos_of_nonneg_of_pos (hgp y) hε) hα hβ hαβ
    intro x hx y hy
    have hfε := Real.rpow_add_le_add_rpow (hfp x) hε.le hα (by linarith : α ≤ 1)
    have hgε := Real.rpow_add_le_add_rpow (hgp y) hε.le hβ (by linarith : β ≤ 1)
    have hhε := mul_le_mul hfε hgε (Real.rpow_nonneg (by linarith [hgp y]) β)
      (add_nonneg (Real.rpow_nonneg (hfp x) α) (Real.rpow_nonneg hε.le α))
    have hAε := mul_le_mul_of_nonneg_right (hA' x hx) (Real.rpow_nonneg hε.le β)
    have hBε := mul_le_mul_of_nonneg_right (hB' y hy) (Real.rpow_nonneg hε.le α)
    have hεpow : ε ^ α * ε ^ β = ε := by rw [← Real.rpow_add hε, hαβ, Real.rpow_one]
    have hm := hmajor x hx y hy
    dsimp [δ]
    nlinarith
  have hab' : α * a + β * c ≤ α * b + β * d :=
    add_le_add (mul_le_mul_of_nonneg_left hab.le hα) (mul_le_mul_of_nonneg_left hcd.le hβ)
  have hfc : Continuous (fun ε ↦ ∫ x in a..b, f x + ε) :=
    BrascampLieb.continuous_intervalIntegral (hf.comp continuous_snd |>.add continuous_fst) hab.le
  have hgc : Continuous (fun ε ↦ ∫ y in c..d, g y + ε) :=
    BrascampLieb.continuous_intervalIntegral (hg.comp continuous_snd |>.add continuous_fst) hcd.le
  have hhc : Continuous (fun ε ↦ ∫ z in α * a + β * c..α * b + β * d, h z + δ ε) :=
    BrascampLieb.continuous_intervalIntegral ((hh.comp continuous_snd).add (hδc.comp continuous_fst)) hab'
  have hL := ((hfc.rpow_const (fun _ ↦ Or.inr hα)).mul
    (hgc.rpow_const (fun _ ↦ Or.inr hβ))).continuousAt.tendsto.comp tendsto_one_div_add_atTop_nhds_zero_nat
  have hR := hhc.continuousAt.tendsto.comp tendsto_one_div_add_atTop_nhds_zero_nat
  simp only [hδ0, add_zero] at hL hR
  apply le_of_tendsto_of_tendsto hL hR
  filter_upwards [] with n
  exact hbound _ (by positivity)


/-- Extension from a closed interval by clamping the argument. -/
def clampExtension (f : ℝ → ℝ) (a b x : ℝ) : ℝ := f (max a (min b x))

lemma clamp_mem {a b : ℝ} (hab : a ≤ b) (x : ℝ) : max a (min b x) ∈ Icc a b :=
  ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩

lemma clampExtension_eq {f : ℝ → ℝ} {a b x : ℝ} (hx : x ∈ Icc a b) :
    clampExtension f a b x = f x := by simp [clampExtension, min_eq_right hx.2, max_eq_right hx.1]

lemma continuous_clampExtension {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) : Continuous (clampExtension f a b) :=
  hf.comp_continuous (by fun_prop) (clamp_mem hab)

lemma integral_clampExtension (f : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) :
    (∫ x in a..b, clampExtension f a b x) = ∫ x in a..b, f x := by
  apply intervalIntegral.integral_congr
  intro x hx
  exact clampExtension_eq (by simpa only [uIcc_of_le hab] using hx)

/-- The finite-interval Prékopa–Leindler theorem requires continuity and
positivity only on the intervals actually used. Endpoint behavior elsewhere
is completely irrelevant. -/
theorem integral_rpow_mul_le_continuousOn {f g h : ℝ → ℝ} {a b c d α β : ℝ}
    (hab : a < b) (hcd : c < d) (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc c d))
    (hh : ContinuousOn h (Icc (α * a + β * c) (α * b + β * d)))
    (hfp : ∀ x ∈ Icc a b, 0 < f x) (hgp : ∀ x ∈ Icc c d, 0 < g x)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + β = 1)
    (hmajor : ∀ x ∈ Icc a b, ∀ y ∈ Icc c d,
      f x ^ α * g y ^ β ≤ h (α * x + β * y)) :
    (∫ x in a..b, f x) ^ α * (∫ y in c..d, g y) ^ β ≤
      ∫ z in α * a + β * c..α * b + β * d, h z := by
  have hhord : α * a + β * c ≤ α * b + β * d :=
    add_le_add (mul_le_mul_of_nonneg_left hab.le hα) (mul_le_mul_of_nonneg_left hcd.le hβ)
  have h := integral_rpow_mul_le hab hcd (continuous_clampExtension hab.le hf)
    (continuous_clampExtension hcd.le hg) (continuous_clampExtension hhord hh)
    (fun x ↦ hfp _ (clamp_mem hab.le x)) (fun y ↦ hgp _ (clamp_mem hcd.le y)) hα hβ hαβ ?_
  · simpa only [integral_clampExtension _ hab.le, integral_clampExtension _ hcd.le,
      integral_clampExtension _ hhord] using h
  · intro x hx y hy
    have hz : α * x + β * y ∈ Icc (α * a + β * c) (α * b + β * d) := by
      constructor
      · exact add_le_add (mul_le_mul_of_nonneg_left hx.1 hα) (mul_le_mul_of_nonneg_left hy.1 hβ)
      · exact add_le_add (mul_le_mul_of_nonneg_left hx.2 hα) (mul_le_mul_of_nonneg_left hy.2 hβ)
    simpa only [clampExtension_eq hx, clampExtension_eq hy, clampExtension_eq hz] using hmajor x hx y hy

/-- Full-line Prékopa–Leindler also allows zeros in continuous densities. -/
theorem integral_rpow_mul_le_integral_of_nonneg {f g h : ℝ → ℝ} {α β : ℝ}
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h)
    (hfp : ∀ x, 0 ≤ f x) (hgp : ∀ x, 0 ≤ g x)
    (hfi : Integrable f) (hgi : Integrable g) (hhi : Integrable h)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + β = 1)
    (hmajor : ∀ x y, f x ^ α * g y ^ β ≤ h (α * x + β * y)) :
    (∫ x, f x) ^ α * (∫ y, g y) ^ β ≤ ∫ z, h z := by
  have hb : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have ha := tendsto_neg_atTop_atBot.comp hb
  have hfLim := (intervalIntegral_tendsto_integral hfi ha hb).rpow_const (Or.inr hα)
  have hgLim := (intervalIntegral_tendsto_integral hgi ha hb).rpow_const (Or.inr hβ)
  have hhLim := intervalIntegral_tendsto_integral hhi ha hb
  apply le_of_tendsto_of_tendsto (hfLim.mul hgLim) hhLim
  filter_upwards [] with n
  have hn : -((n : ℝ) + 1) < (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have h := integral_rpow_mul_le_of_nonneg hn hn hf hg hh hfp hgp hα hβ hαβ
    (fun x _ y _ ↦ hmajor x y)
  have he₁ : α * -((n : ℝ) + 1) + β * -((n : ℝ) + 1) = -((n : ℝ) + 1) := by
    rw [← add_mul, hαβ, one_mul]
  have he₂ : α * ((n : ℝ) + 1) + β * ((n : ℝ) + 1) = (n : ℝ) + 1 := by
    rw [← add_mul, hαβ, one_mul]
  simpa only [he₁, he₂] using h

end GaussianTilt.Prekopa
