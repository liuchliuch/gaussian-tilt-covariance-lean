import GaussianTilt.CramerFinite
import GaussianTilt.CramerIID

/-! # Uniform Cramér--Petrov limit from the proved finite relative-error theorem -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace GaussianTilt.CramerUniform
open CramerAnalytic CramerFinite GaussianLaplace SmoothComparison

lemma scaled_power_identity {x : ℝ} (hx : 0 < x) (u a b : ℝ) (k : ℕ) :
    u ^ k / x ^ a = (u / x ^ b) ^ k * x ^ (b * k - a) := by
  rw [div_pow, ← Real.rpow_mul_natCast hx.le, Real.rpow_sub hx]
  field_simp

lemma scaled_product_identity {x : ℝ} (hx : 0 < x) (u a b : ℝ) :
    u * x ^ a = (u / x ^ b) * x ^ (b + a) := by
  rw [Real.rpow_add hx]
  field_simp

/-- All four powers controlling the finite relative error vanish uniformly
at the original o(n^(1/6)) scale. -/
theorem cramer_scale_limits {u : ℕ → ℝ}
    (hu : Asymptotics.IsLittleO atTop u (fun n ↦ (n : ℝ) ^ (1 / 6 : ℝ))) :
    Tendsto (fun n ↦ u n / Real.sqrt n) atTop (𝓝 0) ∧
    Tendsto (fun n ↦ u n ^ 3 / Real.sqrt n) atTop (𝓝 0) ∧
    Tendsto (fun n ↦ (1 + u n) * (u n ^ 2 / Real.sqrt n + (n : ℝ) ^ (-(1 / 5 : ℝ)))) atTop (𝓝 0) := by
  let q : ℕ → ℝ := fun n ↦ u n / (n : ℝ) ^ (1 / 6 : ℝ)
  have hq : Tendsto q atTop (𝓝 0) := hu.tendsto_div_nhds_zero
  have hcast : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hneg (a : ℝ) (ha : 0 < a) : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (-a)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop ha).comp hcast
  have hδ : Tendsto (fun n ↦ u n / Real.sqrt n) atTop (𝓝 0) := by
    have h := hq.mul (hneg (1 / 3) (by norm_num))
    simp only [zero_mul] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnp : (0 : ℝ) < n := by exact_mod_cast hn
    have hh := scaled_power_identity hnp (u n) (1 / 2) (1 / 6) 1
    simpa only [pow_one, Nat.cast_one, mul_one, show (1 / 6 : ℝ) - 1 / 2 = -(1 / 3 : ℝ) by norm_num,
      ← Real.sqrt_eq_rpow, q] using hh.symm
  have h2 : Tendsto (fun n ↦ u n ^ 2 / Real.sqrt n) atTop (𝓝 0) := by
    have h := (hq.pow 2).mul (hneg (1 / 6) (by norm_num))
    simp only [zero_pow (by decide : 2 ≠ 0), zero_mul] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnp : (0 : ℝ) < n := by exact_mod_cast hn
    have hh := scaled_power_identity hnp (u n) (1 / 2) (1 / 6) 2
    norm_num only [Nat.cast_ofNat, show (1 / 6 : ℝ) * 2 - 1 / 2 = -(1 / 6 : ℝ) by norm_num] at hh
    simpa only [← Real.sqrt_eq_rpow, q] using hh.symm
  have h3 : Tendsto (fun n ↦ u n ^ 3 / Real.sqrt n) atTop (𝓝 0) := by
    have h := hq.pow 3
    simp only [zero_pow (by decide : 3 ≠ 0)] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnp : (0 : ℝ) < n := by exact_mod_cast hn
    have hh := scaled_power_identity hnp (u n) (1 / 2) (1 / 6) 3
    norm_num only [Nat.cast_ofNat, show (1 / 6 : ℝ) * 3 - 1 / 2 = (0 : ℝ) by norm_num,
      Real.rpow_zero, mul_one] at hh
    simpa only [← Real.sqrt_eq_rpow, q] using hh.symm
  have hu5 : Tendsto (fun n ↦ u n * (n : ℝ) ^ (-(1 / 5 : ℝ))) atTop (𝓝 0) := by
    have h := hq.mul (hneg (1 / 30) (by norm_num))
    simp only [zero_mul] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnp : (0 : ℝ) < n := by exact_mod_cast hn
    have hh := scaled_product_identity hnp (u n) (-(1 / 5)) (1 / 6)
    norm_num only [show (1 / 6 : ℝ) + -(1 / 5 : ℝ) = -(1 / 30 : ℝ) by norm_num] at hh
    exact hh.symm
  refine ⟨hδ, h3, ?_⟩
  have h := ((h2.add h3).add (hneg (1 / 5) (by norm_num))).add hu5
  convert h using 1 <;> ring

/-- Explicit finite relative-error majorant. -/
def errorBound (A : ℝ) (n : ℕ) (z : ℝ) : ℝ :=
  Real.exp (A * z ^ 3 / Real.sqrt n) *
    (1 + A * (1 + z) * (z ^ 2 / Real.sqrt n + (n : ℝ) ^ (-(1 / 5 : ℝ)))) - 1

lemma errorBound_tendsto {u : ℕ → ℝ}
    (hu : Asymptotics.IsLittleO atTop u (fun n ↦ (n : ℝ) ^ (1 / 6 : ℝ))) (A : ℝ) :
    Tendsto (fun n ↦ errorBound A n (u n)) atTop (𝓝 0) := by
  obtain ⟨hδ, h3, hrest⟩ := cramer_scale_limits hu
  have h3' : Tendsto (fun n ↦ A * (u n ^ 3 / Real.sqrt n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using h3.const_mul A
  have hr' : Tendsto (fun n ↦ 1 + A * ((1 + u n) *
      (u n ^ 2 / Real.sqrt n + (n : ℝ) ^ (-(1 / 5 : ℝ))))) atTop (𝓝 1) := by
    simpa only [mul_zero, add_zero] using (hrest.const_mul A).const_add 1
  have h := (((Real.continuous_exp.tendsto 0).comp h3').mul hr').sub_const 1
  simp only [Real.exp_zero, one_mul, sub_self] at h
  convert h using 1
  funext n
  dsimp [errorBound]
  congr 2 <;> ring

lemma errorBound_mono {A z u : ℝ} {n : ℕ} (hA : 0 ≤ A) (hz : 0 ≤ z) (hzu : z ≤ u) :
    errorBound A n z ≤ errorBound A n u := by
  have hu : 0 ≤ u := hz.trans hzu
  have hs : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have h2 := div_le_div_of_nonneg_right (pow_le_pow_left₀ hz hzu 2) hs
  have h3 := div_le_div_of_nonneg_right (pow_le_pow_left₀ hz hzu 3) hs
  have hex : Real.exp (A * z ^ 3 / Real.sqrt n) ≤ Real.exp (A * u ^ 3 / Real.sqrt n) := by
    apply Real.exp_le_exp.mpr
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left h3 hA
  have hrest : 1 + A * (1 + z) * (z ^ 2 / Real.sqrt n + (n : ℝ) ^ (-(1 / 5 : ℝ))) ≤
      1 + A * (1 + u) * (u ^ 2 / Real.sqrt n + (n : ℝ) ^ (-(1 / 5 : ℝ))) := by
    apply add_le_add_left
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left (by linarith : 1 + z ≤ 1 + u) hA
    · exact add_le_add_right h2 _
    · positivity
    · positivity
  exact sub_le_sub_right (mul_le_mul hex hrest (by positivity) (Real.exp_nonneg _)) 1

/-- The actual set of nonnegative relative-tail errors on the requested window. -/
def relativeErrorSet (μ : Measure ℝ) (n : ℕ) (u : ℝ) : Set ℝ :=
  {e | ∃ z ∈ Icc (0 : ℝ) u,
    e = |(sumLaw μ n).real {x | Real.sqrt n * z ≤ x} / normalTail z - 1|}

/-- The normalized original Cramér--Petrov uniform relative-tail conclusion.
Nonemptiness and upper boundedness of each eventual supremum are derived from
the actual finite probability theorem. -/
theorem normalized_uniform_relative_tail {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : StandardCramer μ) {u : ℕ → ℝ} (hu0 : ∀ n, 0 ≤ u n)
    (hu : Asymptotics.IsLittleO atTop u (fun n ↦ (n : ℝ) ^ (1 / 6 : ℝ))) :
    Tendsto (fun n ↦ sSup (relativeErrorSet μ n (u n))) atTop (𝓝 0) := by
  obtain ⟨A, κ, hA, hκ, hfinite⟩ := cramer_finite_relative_bound hμ
  have hδ := (cramer_scale_limits hu).1
  have hev : ∀ᶠ n : ℕ in atTop,
      0 ≤ sSup (relativeErrorSet μ n (u n)) ∧
      sSup (relativeErrorSet μ n (u n)) ≤ errorBound A n (u n) := by
    filter_upwards [hδ.eventually (gt_mem_nhds hκ), eventually_gt_atTop 0] with n hnκ hn
    have hbound (e : ℝ) (he : e ∈ relativeErrorSet μ n (u n)) : e ≤ errorBound A n (u n) := by
      obtain ⟨z, hz, rfl⟩ := he
      have hzκ : z / Real.sqrt n ≤ κ :=
        (div_le_div_of_nonneg_right hz.2 (Real.sqrt_nonneg _)).trans hnκ.le
      exact (hfinite n z hn hz.1 hzκ).trans (errorBound_mono hA.le hz.1 hz.2)
    have hb : BddAbove (relativeErrorSet μ n (u n)) := ⟨errorBound A n (u n), hbound⟩
    have hmem : |(sumLaw μ n).real {x | Real.sqrt n * 0 ≤ x} / normalTail 0 - 1| ∈
        relativeErrorSet μ n (u n) := ⟨0, ⟨le_rfl, hu0 n⟩, rfl⟩
    exact ⟨(abs_nonneg _).trans (le_csSup hb hmem), csSup_le ⟨_, hmem⟩ hbound⟩
  exact squeeze_zero' (hev.mono fun _ h ↦ h.1) (hev.mono fun _ h ↦ h.2) (errorBound_tendsto hu A)

/-- Original Theorem4.3 for an arbitrary probability space and actual iid
sequence, at its original variance, left-tail orientation and supremum window.
Every finite estimate and probability-law transport is proved upstream. -/
theorem original4_3 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → ℝ) (hY : ∀ i, Measurable (Y i))
    (hInd : ProbabilityTheory.iIndepFun Y μ)
    (hIdent : ∀ i, ProbabilityTheory.IdentDistrib (Y i) (Y 0) μ μ)
    (hmean : ∫ ω, Y 0 ω ∂μ = 0) {σ : ℝ} (hσ : 0 < σ)
    (hvar : ProbabilityTheory.variance (Y 0) μ = σ ^ 2)
    (hC : 0 ∈ interior (ProbabilityTheory.integrableExpSet (Y 0) μ))
    {u : ℕ → ℝ} (hu0 : ∀ n, 0 ≤ u n)
    (hu : Asymptotics.IsLittleO atTop u (fun n ↦ (n : ℝ) ^ (1 / 6 : ℝ))) :
    Tendsto (fun n ↦ sSup {e : ℝ | ∃ z ∈ Icc (0 : ℝ) (u n),
      e = |μ.real {ω | (∑ i ∈ Finset.range n, Y i ω) ≤ -σ * Real.sqrt n * z} /
        normalTail z - 1|}) atTop (𝓝 0) := by
  letI := CramerIID.normalized_probability (μ := μ) (hY 0) σ
  simp_rw [CramerIID.iid_left_tail_eq Y hY hInd hIdent hC hσ]
  exact normalized_uniform_relative_tail
    (CramerIID.normalized_standard (hY 0) hmean hσ hvar hC) hu0 hu

end GaussianTilt.CramerUniform
