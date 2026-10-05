import GaussianTilt.LetwinDiffusion

/-!
# Construction of the moment-potential cutoffs

The cutoffs are the actual functions `smoothTransition (2 - W/R)`. Their
compact support is obtained from compact sublevel sets of the potential.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators ContDiff

namespace GaussianTilt.Letwin

/-- A fixed smooth, decreasing transition from one to zero on [1,2]. -/
def cutoffProfile (t : ℝ) : ℝ := Real.smoothTransition (2 - t)

lemma cutoffProfile_contDiff : ContDiff ℝ ∞ cutoffProfile := by
  unfold cutoffProfile
  fun_prop

lemma cutoffProfile_nonneg (t : ℝ) : 0 ≤ cutoffProfile t := Real.smoothTransition.nonneg _
lemma cutoffProfile_le_one (t : ℝ) : cutoffProfile t ≤ 1 := Real.smoothTransition.le_one _
lemma cutoffProfile_one {t : ℝ} (ht : t ≤ 1) : cutoffProfile t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)
lemma cutoffProfile_zero {t : ℝ} (ht : 2 ≤ t) : cutoffProfile t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)
lemma cutoffProfile_antitone : Antitone cutoffProfile := by
  intro s t hst
  exact Real.smoothTransition.monotone (by linarith)

lemma deriv_cutoffProfile_zero_of_not_mem {t : ℝ} (ht : t ∉ Icc (1 : ℝ) 2) :
    deriv cutoffProfile t = 0 := by
  simp only [mem_Icc, not_and_or, not_le] at ht
  rcases ht with ht | ht
  · apply HasDerivAt.deriv
    apply (hasDerivAt_const t (1 : ℝ)).congr_of_eventuallyEq
    filter_upwards [gt_mem_nhds ht] with s hs
    exact cutoffProfile_one hs.le
  · apply HasDerivAt.deriv
    apply (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds ht] with s hs
    exact cutoffProfile_zero hs.le

lemma tsupport_deriv_cutoffProfile_subset : tsupport (deriv cutoffProfile) ⊆ Icc (1 : ℝ) 2 := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  by_contra h
  exact ht (deriv_cutoffProfile_zero_of_not_mem h)

lemma hasCompactSupport_deriv_cutoffProfile : HasCompactSupport (deriv cutoffProfile) :=
  isCompact_Icc.of_isClosed_subset isClosed_closure tsupport_deriv_cutoffProfile_subset

lemma hasCompactSupport_second_deriv_cutoffProfile : HasCompactSupport (deriv (deriv cutoffProfile)) :=
  hasCompactSupport_deriv_cutoffProfile.deriv

lemma tsupport_second_deriv_cutoffProfile_subset :
    tsupport (deriv (deriv cutoffProfile)) ⊆ Icc (1 : ℝ) 2 :=
  (closure_minimal support_deriv_subset isClosed_closure).trans tsupport_deriv_cutoffProfile_subset

/-- The cutoff associated with a potential and a scale. -/
def potentialCutoff {n : ℕ} (W : CoordinateSpace n → ℝ) (R : ℝ) (x : CoordinateSpace n) : ℝ :=
  cutoffProfile (W x / R)

lemma potentialCutoff_nonneg {n : ℕ} (W : CoordinateSpace n → ℝ) (R : ℝ) (x : CoordinateSpace n) :
    0 ≤ potentialCutoff W R x := cutoffProfile_nonneg _
lemma potentialCutoff_le_one {n : ℕ} (W : CoordinateSpace n → ℝ) (R : ℝ) (x : CoordinateSpace n) :
    potentialCutoff W R x ≤ 1 := cutoffProfile_le_one _

lemma potentialCutoff_contDiff {n : ℕ} {W : CoordinateSpace n → ℝ}
    (hW : ContDiff ℝ ∞ W) (R : ℝ) : ContDiff ℝ ∞ (potentialCutoff W R) := by
  exact cutoffProfile_contDiff.comp (hW.div_const R)

lemma potentialCutoff_eq_one {n : ℕ} {W : CoordinateSpace n → ℝ} {R : ℝ} (hR : 0 < R)
    {x : CoordinateSpace n} (hx : W x ≤ R) : potentialCutoff W R x = 1 :=
  cutoffProfile_one ((div_le_one hR).mpr hx)

lemma potentialCutoff_eq_zero {n : ℕ} {W : CoordinateSpace n → ℝ} {R : ℝ} (hR : 0 < R)
    {x : CoordinateSpace n} (hx : 2 * R ≤ W x) : potentialCutoff W R x = 0 :=
  cutoffProfile_zero ((le_div_iff₀ hR).mpr hx)

lemma potentialCutoff_hasCompactSupport {n : ℕ} {W : CoordinateSpace n → ℝ}
    (hproper : ∀ a : ℝ, IsCompact {x | W x ≤ a}) {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (potentialCutoff W R) := by
  apply (hproper (2 * R)).of_isClosed_subset isClosed_closure
  apply closure_minimal _ (hproper (2 * R)).isClosed
  intro x hx
  by_contra h
  exact hx (potentialCutoff_eq_zero hR (le_of_lt (lt_of_not_ge h)))

lemma potentialCutoff_monotone {n : ℕ} {W : CoordinateSpace n → ℝ}
    (hW0 : ∀ x, 0 ≤ W x) (x : CoordinateSpace n) :
    Monotone (fun k : ℕ => potentialCutoff W ((k : ℝ) + 1) x) := by
  intro j k hjk
  apply cutoffProfile_antitone
  apply div_le_div_of_nonneg_left (hW0 x) (by positivity)
  exact_mod_cast Nat.add_le_add_right hjk 1

lemma potentialCutoff_tendsto {n : ℕ} (W : CoordinateSpace n → ℝ) (x : CoordinateSpace n) :
    Tendsto (fun k : ℕ => potentialCutoff W ((k : ℝ) + 1) x) atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  obtain ⟨N, hN⟩ := exists_nat_gt (W x)
  filter_upwards [eventually_ge_atTop N] with k hk
  symm
  apply potentialCutoff_eq_one (by positivity)
  have : (N : ℝ) ≤ k := by exact_mod_cast hk
  linarith

/-- A smooth compactly supported majorant of the second derivative of the
fixed cutoff profile, constructed explicitly from smooth transitions. -/
theorem exists_cutoff_second_derivative_majorant :
    ∃ w : ℝ → ℝ, ContDiff ℝ ∞ w ∧ HasCompactSupport w ∧
      (∀ t, 0 ≤ w t) ∧ (∀ t, |deriv (deriv cutoffProfile) t| ≤ w t) ∧
      (∀ t, 3 ≤ t → w t = 0) := by
  have hd : ContDiff ℝ ∞ (deriv cutoffProfile) := cutoffProfile_contDiff.deriv'
  have hdd : ContDiff ℝ ∞ (deriv (deriv cutoffProfile)) := hd.deriv'
  obtain ⟨C, hC⟩ := hasCompactSupport_second_deriv_cutoffProfile.exists_bound_of_continuous hdd.continuous
  let b := fun t : ℝ => Real.smoothTransition t * Real.smoothTransition (3 - t)
  have hb : ContDiff ℝ ∞ b := by dsimp [b]; fun_prop
  have hb0 (t : ℝ) : 0 ≤ b t :=
    mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  have hbz (t : ℝ) (ht : 3 ≤ t) : b t = 0 := by
    dsimp [b]
    rw [Real.smoothTransition.zero_of_nonpos (x := 3 - t) (by linarith), mul_zero]
  have hbc : HasCompactSupport b := by
    apply (isCompact_Icc : IsCompact (Icc (0 : ℝ) 3)).of_isClosed_subset isClosed_closure
    apply closure_minimal _ isClosed_Icc
    intro t ht
    by_contra hn
    simp only [mem_Icc, not_and_or, not_le] at hn
    rcases hn with hn | hn
    · exact ht (by simp [b, Real.smoothTransition.zero_of_nonpos hn.le])
    · exact ht (hbz t hn.le)
  refine ⟨fun t => max C 0 * b t, contDiff_const.mul hb, hbc.mul_left,
    (fun t => mul_nonneg (le_max_right _ _) (hb0 t)), ?_, ?_⟩
  · intro t
    change |deriv (deriv cutoffProfile) t| ≤ max C 0 * b t
    by_cases ht : t ∈ Icc (1 : ℝ) 2
    · have hb1 : b t = 1 := by
        dsimp [b]
        rw [Real.smoothTransition.one_of_one_le ht.1,
          Real.smoothTransition.one_of_one_le (by linarith [ht.2]), mul_one]
      rw [hb1, mul_one]
      exact (show |deriv (deriv cutoffProfile) t| ≤ C by simpa only [Real.norm_eq_abs] using hC t).trans (le_max_left _ _)
    · have hz : deriv (deriv cutoffProfile) t = 0 := by
        apply Function.notMem_support.mp
        intro hs
        exact ht (tsupport_second_deriv_cutoffProfile_subset (subset_closure hs))
      rw [hz, abs_zero]
      exact mul_nonneg (le_max_right _ _) (hb0 t)
  · intro t ht
    change max C 0 * b t = 0
    rw [hbz t ht, mul_zero]

/-- Uniform bound for the first derivative of the fixed profile. -/
theorem exists_cutoff_first_derivative_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, |deriv cutoffProfile t| ≤ C := by
  obtain ⟨C, hC⟩ := hasCompactSupport_deriv_cutoffProfile.exists_bound_of_continuous
    (cutoffProfile_contDiff.continuous_deriv (by simp))
  exact ⟨max C 0, le_max_right _ _, fun t =>
    (show |deriv cutoffProfile t| ≤ C by simpa only [Real.norm_eq_abs] using hC t).trans (le_max_left _ _)⟩

/-- An antiderivative vanishing beyond the support of the majorant. -/
def cutoffTail (w : ℝ → ℝ) (t : ℝ) : ℝ := ∫ s in t..3, w s

lemma hasDerivAt_cutoffTail {w : ℝ → ℝ} (hw : Continuous w) (t : ℝ) :
    HasDerivAt (cutoffTail w) (-w t) t := by
  exact intervalIntegral.integral_hasDerivAt_left (hw.intervalIntegrable _ _)
    hw.stronglyMeasurable.stronglyMeasurableAtFilter hw.continuousAt

lemma cutoffTail_contDiff {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (cutoffTail w) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun t => (hasDerivAt_cutoffTail hw.continuous t).differentiableAt, ?_⟩
  have he : deriv (cutoffTail w) = fun t => -w t := funext fun t => (hasDerivAt_cutoffTail hw.continuous t).deriv
  rw [he]
  exact hw.neg

lemma cutoffTail_zero {w : ℝ → ℝ} (hwz : ∀ t, 3 ≤ t → w t = 0) {t : ℝ} (ht : 3 ≤ t) :
    cutoffTail w t = 0 := by
  unfold cutoffTail
  rw [intervalIntegral.integral_symm]
  suffices (∫ s in (3 : ℝ)..t, w s) = 0 by rw [this, neg_zero]
  calc
    (∫ s in (3 : ℝ)..t, w s) = ∫ s in (3 : ℝ)..t, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro s hs
      exact hwz s ((by simpa only [Set.uIcc_of_le ht, Set.mem_Icc] using hs : 3 ≤ s ∧ s ≤ t).1)
    _ = 0 := by simp

lemma cutoffTail_nonneg {w : ℝ → ℝ} (hw0 : ∀ t, 0 ≤ w t)
    (hwz : ∀ t, 3 ≤ t → w t = 0) (t : ℝ) : 0 ≤ cutoffTail w t := by
  rcases le_total t 3 with ht | ht
  · exact intervalIntegral.integral_nonneg_of_forall ht hw0
  · rw [cutoffTail_zero hwz ht]

lemma norm_cutoffTail_le {w : ℝ → ℝ} (hw : Integrable w) (t : ℝ) :
    ‖cutoffTail w t‖ ≤ ∫ s, ‖w s‖ := by
  exact intervalIntegral.norm_integral_le_integral_norm_uIoc.trans
    (setIntegral_le_integral hw.norm (Filter.Eventually.of_forall fun s => norm_nonneg (w s)))

/-- The scaled energy test from A4. -/
def cutoffEnergyTest (w : ℝ → ℝ) (R : ℝ) (t : ℝ) : ℝ := cutoffTail w (t / R) / R

lemma hasDerivAt_cutoffEnergyTest {w : ℝ → ℝ} (hw : Continuous w) (R t : ℝ) :
    HasDerivAt (cutoffEnergyTest w R) (-w (t / R) / R ^ 2) t := by
  convert ((hasDerivAt_cutoffTail hw (t / R)).comp t ((hasDerivAt_id t).div_const R)).div_const R using 1
  simp only [div_eq_mul_inv]
  ring

lemma cutoffEnergyTest_contDiff {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (R : ℝ) :
    ContDiff ℝ ∞ (cutoffEnergyTest w R) :=
  ((cutoffTail_contDiff hw).comp (contDiff_id.div_const R)).div_const R

lemma cutoffEnergyTest_nonneg {w : ℝ → ℝ} (hw0 : ∀ t, 0 ≤ w t)
    (hwz : ∀ t, 3 ≤ t → w t = 0) {R : ℝ} (hR : 0 < R) (t : ℝ) :
    0 ≤ cutoffEnergyTest w R t := div_nonneg (cutoffTail_nonneg hw0 hwz _) hR.le

lemma norm_cutoffEnergyTest_le {w : ℝ → ℝ} (hw : Integrable w) {R : ℝ} (hR : 0 < R) (t : ℝ) :
    ‖cutoffEnergyTest w R t‖ ≤ (∫ s, ‖w s‖) / R := by
  change ‖cutoffTail w (t / R) / R‖ ≤ _
  rw [norm_div, Real.norm_of_nonneg hR.le]
  exact div_le_div_of_nonneg_right (norm_cutoffTail_le hw _) hR.le

lemma cutoffEnergyTest_hasCompactSupport {n : ℕ} {W : CoordinateSpace n → ℝ}
    (hproper : ∀ a : ℝ, IsCompact {x | W x ≤ a})
    {w : ℝ → ℝ} (hwz : ∀ t, 3 ≤ t → w t = 0) {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (cutoffEnergyTest w R ∘ W) := by
  apply (hproper (3 * R)).of_isClosed_subset isClosed_closure
  apply closure_minimal _ (hproper (3 * R)).isClosed
  intro x hx
  by_contra hn
  have hx' : 3 ≤ W x / R := (le_div_iff₀ hR).mpr (le_of_lt (lt_of_not_ge hn))
  exact hx (by simp [cutoffEnergyTest, cutoffTail_zero hwz hx'])

/-- The energy identity of A4, now obtained by applying the proved Green
formula to the explicitly constructed compactly supported energy test. -/
theorem cutoff_energy_identity {n : ℕ} {φ W : CoordinateSpace n → ℝ}
    [IsFiniteMeasure (potentialMeasure φ)]
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {w : ℝ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hA : ∀ i j, ContDiff ℝ 1 (fun x => A x i j))
    (hW : ContDiff ℝ 2 W) (hproper : ∀ a : ℝ, IsCompact {x | W x ≤ a})
    (hw : ContDiff ℝ ∞ w) (hwz : ∀ t, 3 ≤ t → w t = 0) {R : ℝ} (hR : 0 < R) :
    (∫ x, w (W x / R) / R ^ 2 * diffusionGamma A W W x ∂potentialMeasure φ) =
      ∫ x, cutoffEnergyTest w R (W x) * divergenceDiffusion φ A W x ∂potentialMeasure φ := by
  have h := integral_diffusion_energy_test hφ hA hW
    ((cutoffEnergyTest_contDiff hw R).of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞))
    (cutoffEnergyTest_hasCompactSupport hproper hwz hR)
  simp_rw [(hasDerivAt_cutoffEnergyTest hw.continuous R _).deriv] at h
  have heq : (fun x => -w (W x / R) / R ^ 2 * diffusionGamma A W W x) =
      (fun x => -(w (W x / R) / R ^ 2 * diffusionGamma A W W x)) := by
    funext x
    ring
  rw [heq, integral_neg, neg_neg] at h
  exact h.symm

lemma cutoff_majorant_hasCompactSupport {n : ℕ} {W : CoordinateSpace n → ℝ}
    (hproper : ∀ a : ℝ, IsCompact {x | W x ≤ a})
    {w : ℝ → ℝ} (hwz : ∀ t, 3 ≤ t → w t = 0) {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (fun x => w (W x / R)) := by
  apply (hproper (3 * R)).of_isClosed_subset isClosed_closure
  apply closure_minimal _ (hproper (3 * R)).isClosed
  intro x hx
  by_contra hn
  exact hx (hwz _ ((le_div_iff₀ hR).mpr (le_of_lt (lt_of_not_ge hn))))

lemma integrable_cutoff_energy {n : ℕ} {φ W : CoordinateSpace n → ℝ}
    [IsFiniteMeasure (potentialMeasure φ)]
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {w : ℝ → ℝ}
    (hA : ∀ i j, ContDiff ℝ 1 (fun x => A x i j)) (hW : ContDiff ℝ 2 W)
    (hproper : ∀ a : ℝ, IsCompact {x | W x ≤ a})
    (hw : Continuous w) (hwz : ∀ t, 3 ≤ t → w t = 0) {R : ℝ} (hR : 0 < R) :
    Integrable (fun x => w (W x / R) / R ^ 2 * diffusionGamma A W W x) (potentialMeasure φ) := by
  apply (((hw.comp (hW.continuous.div_const R)).div_const (R ^ 2)).mul
    (continuous_diffusionGamma hA hW (hW.of_le (by norm_num)))).integrable_of_hasCompactSupport
  exact ((cutoff_majorant_hasCompactSupport hproper hwz hR).mul_right).mul_right

/-- A4's crucial energy bound has no assumed integration identity. -/
theorem cutoff_energy_le {n : ℕ} {φ W : CoordinateSpace n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {w : ℝ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hA : ∀ i j, ContDiff ℝ 1 (fun x => A x i j))
    (hW : ContDiff ℝ 2 W) (hproper : ∀ a : ℝ, IsCompact {x | W x ≤ a})
    (hw : ContDiff ℝ ∞ w) (hwc : HasCompactSupport w)
    (hwz : ∀ t, 3 ≤ t → w t = 0) (D : ℝ)
    (hD : ∀ x, |divergenceDiffusion φ A W x| ≤ D) {R : ℝ} (hR : 0 < R) :
    (∫ x, w (W x / R) / R ^ 2 * diffusionGamma A W W x ∂potentialMeasure φ) ≤
      D * (∫ s, ‖w s‖) / R := by
  rw [cutoff_energy_identity hφ hA hW hproper hw hwz hR]
  have hwi : Integrable w := hw.continuous.integrable_of_hasCompactSupport hwc
  have hqC : Continuous (fun x => cutoffEnergyTest w R (W x)) :=
    (cutoffEnergyTest_contDiff hw R).continuous.comp hW.continuous
  have hqc := cutoffEnergyTest_hasCompactSupport hproper hwz hR
  have hint : Integrable
      (fun x => cutoffEnergyTest w R (W x) * divergenceDiffusion φ A W x) (potentialMeasure φ) :=
    (hqC.mul (continuous_divergenceDiffusion hφ hA hW)).integrable_of_hasCompactSupport hqc.mul_right
  calc
    _ ≤ ∫ _ : CoordinateSpace n, D * (∫ s, ‖w s‖) / R ∂potentialMeasure φ := by
      apply integral_mono hint (integrable_const _)
      intro x
      calc
        _ ≤ ‖cutoffEnergyTest w R (W x) * divergenceDiffusion φ A W x‖ := le_abs_self _
        _ = ‖cutoffEnergyTest w R (W x)‖ * ‖divergenceDiffusion φ A W x‖ := norm_mul _ _
        _ ≤ ((∫ s, ‖w s‖) / R) * D :=
          mul_le_mul (norm_cutoffEnergyTest_le hwi hR _) (hD x)
            (norm_nonneg _) (div_nonneg (integral_nonneg fun s => norm_nonneg _) hR.le)
        _ = _ := by ring
    _ = _ := by simp

lemma deriv_scaled_cutoffProfile (R t : ℝ) :
    deriv (fun s => cutoffProfile (s / R)) t = deriv cutoffProfile (t / R) / R := by
  have hd := ((cutoffProfile_contDiff.differentiable (by simp)) (t / R)).hasDerivAt.comp t
    ((hasDerivAt_id t).div_const R)
  simpa only [div_eq_mul_inv, one_mul] using hd.deriv

lemma second_deriv_scaled_cutoffProfile (R t : ℝ) :
    deriv (deriv (fun s => cutoffProfile (s / R))) t = deriv (deriv cutoffProfile) (t / R) / R ^ 2 := by
  have heq : deriv (fun s => cutoffProfile (s / R)) = fun s => deriv cutoffProfile (s / R) / R :=
    funext (deriv_scaled_cutoffProfile R)
  rw [heq]
  have hd : Differentiable ℝ (deriv cutoffProfile) :=
    (cutoffProfile_contDiff.of_le (by exact WithTop.coe_le_coe.mpr le_top : (2 : WithTop ℕ∞) ≤ ∞)).differentiable_deriv_two
  convert (((hd (t / R)).hasDerivAt.comp t ((hasDerivAt_id t).div_const R)).div_const R).deriv using 1
  simp only [div_eq_mul_inv]
  ring

/-- The actual generator applied to the constructed cutoff, by the chain rule. -/
theorem divergenceDiffusion_potentialCutoff {n : ℕ} (φ : CoordinateSpace n → ℝ)
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {W : CoordinateSpace n → ℝ}
    (hA : ∀ i j, ContDiff ℝ 1 (fun x => A x i j)) (hW : ContDiff ℝ 2 W)
    (R : ℝ) (x : CoordinateSpace n) :
    divergenceDiffusion φ A (potentialCutoff W R) x =
      deriv cutoffProfile (W x / R) / R * divergenceDiffusion φ A W x +
      deriv (deriv cutoffProfile) (W x / R) / R ^ 2 * diffusionGamma A W W x := by
  have hη : ContDiff ℝ 2 (fun s => cutoffProfile (s / R)) :=
    (cutoffProfile_contDiff.of_le (by exact WithTop.coe_le_coe.mpr le_top : (2 : WithTop ℕ∞) ≤ ∞)).comp (contDiff_id.div_const R)
  exact (divergenceDiffusion_comp φ hA hη hW x).trans (by
    rw [deriv_scaled_cutoffProfile, second_deriv_scaled_cutoffProfile])

/-- Pointwise bound used in A4. Positivity of the energy is derived from
positive semidefiniteness of the actual diffusion matrix. -/
lemma norm_divergenceDiffusion_potentialCutoff_le {n : ℕ} (φ : CoordinateSpace n → ℝ)
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {W : CoordinateSpace n → ℝ}
    (hA : ∀ i j, ContDiff ℝ 1 (fun x => A x i j)) (hW : ContDiff ℝ 2 W)
    (hApos : ∀ x, (A x).PosSemidef) {w : ℝ → ℝ} {C D : ℝ}
    (hC : 0 ≤ C) (hη : ∀ t, |deriv cutoffProfile t| ≤ C)
    (hw : ∀ t, |deriv (deriv cutoffProfile) t| ≤ w t)
    (hD : ∀ x, |divergenceDiffusion φ A W x| ≤ D) {R : ℝ} (hR : 0 < R)
    (x : CoordinateSpace n) :
    ‖divergenceDiffusion φ A (potentialCutoff W R) x‖ ≤
      C / R * D + w (W x / R) / R ^ 2 * diffusionGamma A W W x := by
  rw [divergenceDiffusion_potentialCutoff φ hA hW, Real.norm_eq_abs]
  apply (abs_add_le _ _).trans
  apply add_le_add
  · rw [abs_mul, abs_div, abs_of_pos hR]
    exact mul_le_mul (div_le_div_of_nonneg_right (hη _) hR.le) (hD x)
      (abs_nonneg _) (div_nonneg hC hR.le)
  · rw [abs_mul, abs_div, abs_of_nonneg (sq_nonneg R),
      abs_of_nonneg (diffusionGamma_nonneg W x (hApos x))]
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hw _) (sq_nonneg R))
      (diffusionGamma_nonneg W x (hApos x))

/-- The quantitative O(1/R) estimate in A4, with the cutoff and its energy
test both constructed and all integration identities proved. -/
theorem integral_norm_divergenceDiffusion_potentialCutoff_le {n : ℕ}
    {φ W : CoordinateSpace n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {w : ℝ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hA : ∀ i j, ContDiff ℝ 1 (fun x => A x i j))
    (hW : ContDiff ℝ 2 W) (hproper : ∀ a : ℝ, IsCompact {x | W x ≤ a})
    (hApos : ∀ x, (A x).PosSemidef) (hw : ContDiff ℝ ∞ w) (hwc : HasCompactSupport w)
    (hwz : ∀ t, 3 ≤ t → w t = 0) (hwdom : ∀ t, |deriv (deriv cutoffProfile) t| ≤ w t)
    {C : ℝ} (hC : 0 ≤ C) (hη : ∀ t, |deriv cutoffProfile t| ≤ C)
    (D : ℝ) (hD : ∀ x, |divergenceDiffusion φ A W x| ≤ D) {R : ℝ} (hR : 0 < R) :
    (∫ x, ‖divergenceDiffusion φ A (potentialCutoff W R) x‖ ∂potentialMeasure φ) ≤
      D * (C + ∫ s, ‖w s‖) / R := by
  have hχ : ContDiff ℝ 2 (potentialCutoff W R) :=
    (cutoffProfile_contDiff.of_le (by exact WithTop.coe_le_coe.mpr le_top : (2 : WithTop ℕ∞) ≤ ∞)).comp (hW.div_const R)
  have hχc := potentialCutoff_hasCompactSupport hproper hR
  have hLi : Integrable (divergenceDiffusion φ A (potentialCutoff W R)) (potentialMeasure φ) :=
    (continuous_divergenceDiffusion hφ hA hχ).integrable_of_hasCompactSupport
      (divergenceDiffusion_hasCompactSupport φ A hχc)
  have hJi := integrable_cutoff_energy (φ := φ) hA hW hproper hw.continuous hwz hR
  calc
    _ ≤ ∫ x, C / R * D + w (W x / R) / R ^ 2 * diffusionGamma A W W x ∂potentialMeasure φ := by
      exact integral_mono hLi.norm ((integrable_const _).add hJi)
        (norm_divergenceDiffusion_potentialCutoff_le φ hA hW hApos hC hη hwdom hD hR)
    _ = C / R * D + ∫ x, w (W x / R) / R ^ 2 * diffusionGamma A W W x ∂potentialMeasure φ := by
      rw [integral_add (integrable_const _) hJi]
      simp
    _ ≤ C / R * D + D * (∫ s, ‖w s‖) / R :=
      add_le_add_left (cutoff_energy_le hφ hA hW hproper hw hwc hwz D hD hR) _
    _ = _ := by ring

/-- A4 for a proper nonnegative smooth potential and the actual divergence
operator, with an explicit 1/(k+1) bound. No cutoff existence, Green identity,
or decay estimate is assumed. -/
theorem exists_diffusion_cutoffs {n : ℕ} {φ W : CoordinateSpace n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hφ : ContDiff ℝ 1 φ) (hA : ∀ i j, ContDiff ℝ 1 (fun x => A x i j))
    (hW : ContDiff ℝ ∞ W) (hproper : ∀ a : ℝ, IsCompact {x | W x ≤ a})
    (hW0 : ∀ x, 0 ≤ W x) (hApos : ∀ x, (A x).PosSemidef)
    (D : ℝ) (hD : ∀ x, |divergenceDiffusion φ A W x| ≤ D) :
    ∃ χ : ℕ → CoordinateSpace n → ℝ, ∃ C : ℝ, 0 ≤ C ∧
      (∀ k, ContDiff ℝ ∞ (χ k) ∧ HasCompactSupport (χ k)) ∧
      (∀ k x, 0 ≤ χ k x ∧ χ k x ≤ 1) ∧
      (∀ x, Monotone (fun k => χ k x)) ∧
      (∀ x, Tendsto (fun k => χ k x) atTop (𝓝 1)) ∧
      (∀ k, (∫ x, ‖divergenceDiffusion φ A (χ k) x‖ ∂potentialMeasure φ) ≤ C / ((k : ℝ) + 1)) := by
  obtain ⟨w, hw, hwc, hw0, hwdom, hwz⟩ := exists_cutoff_second_derivative_majorant
  obtain ⟨C, hC, hη⟩ := exists_cutoff_first_derivative_bound
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0)
  refine ⟨fun k => potentialCutoff W ((k : ℝ) + 1), D * (C + ∫ s, ‖w s‖),
    mul_nonneg hD0 (add_nonneg hC (integral_nonneg fun s => norm_nonneg _)), ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    exact ⟨potentialCutoff_contDiff hW _, potentialCutoff_hasCompactSupport hproper (by positivity)⟩
  · intro k x
    exact ⟨potentialCutoff_nonneg W _ x, potentialCutoff_le_one W _ x⟩
  · exact potentialCutoff_monotone hW0
  · exact potentialCutoff_tendsto W
  · intro k
    exact integral_norm_divergenceDiffusion_potentialCutoff_le hφ hA (hW.of_le (by exact WithTop.coe_le_coe.mpr le_top))
      hproper hApos hw hwc hwz hwdom hC hη D hD (by positivity)

end GaussianTilt.Letwin
