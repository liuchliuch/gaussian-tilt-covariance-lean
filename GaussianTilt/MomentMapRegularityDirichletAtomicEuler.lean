import GaussianTilt.MomentMapRegularityDirichletAtomicDerivative

/-! # The actual cell-volume Euler equation for atomic Dirichlet data -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators ENNReal NNReal Gradient
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}
variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

lemma norm_heightPerturb_le (h : ι → ℝ) (i : ι) (t : ℝ) : ‖heightPerturb h i t‖ ≤ ‖h‖ + |t| := by
  calc
    _ ≤ ‖h‖ + ‖t • (Pi.single i (1 : ℝ) : ι → ℝ)‖ := norm_add_le _ _
    _ = _ := by simp [norm_smul, Pi.norm_single]

lemma atomicCell_empty_of_height_nonpos {S : Set (E n)} (hS : IsCompact S)
    {X : ι → E n} {r : ℝ} (hr : 0 < r) (hb : ∀ j, Metric.closedBall (X j) r ⊆ S)
    {h : ι → ℝ} {i : ι} (hi : h i ≤ 0) : atomicCell S X h i = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hgap := boundarySupport_ge_inner_add_norm hS hr (hb i) p
  have hpos := hp.1
  nlinarith [norm_nonneg p]

/-- Dominated differentiation of the actual finite slope integral. The
uniform compact support and unit coordinate Lipschitz constant are proved. -/
theorem integral_atomicExcess_hasDerivAt [NeZero n] {S : Set (E n)} (hS : IsCompact S)
    {X : ι → E n} (hX : Function.Injective X) {r : ℝ} (hr : 0 < r)
    (hb : ∀ j, Metric.closedBall (X j) r ⊆ S) (h : ι → ℝ) (i : ι) :
    HasDerivAt (fun t => ∫ p, atomicExcess S X (heightPerturb h i t) p)
      (volume (atomicCell S X h i)).toReal 0 := by
  let B := Metric.closedBall (0 : E n) ((‖h‖ + 1) / r)
  have hBm : MeasurableSet B := Metric.isClosed_closedBall.measurableSet
  have hBfin : volume B ≠ ⊤ := (isCompact_closedBall _ _).measure_ne_top
  have hSn : S.Nonempty := ⟨X (Classical.arbitrary ι), hb _ (Metric.mem_closedBall_self hr.le)⟩
  have hCm := atomicCell_measurable hS hSn X h i
  have hFmeas (t : ℝ) : AEStronglyMeasurable (atomicExcess S X (heightPerturb h i t)) volume :=
    (atomicExcess_continuous hS hSn X _).aestronglyMeasurable
  have hzero {p : E n} (hp : p ∉ B) {t : ℝ} (ht : t ∈ Metric.ball 0 1) :
      atomicExcess S X (heightPerturb h i t) p = 0 := by
    apply atomicExcess_eq_zero_outside hS hr hb
    have hpn : (‖h‖ + 1) / r < ‖p‖ := by simpa [B, Metric.mem_closedBall, dist_zero_right] using hp
    have htn : |t| < 1 := by simpa [Metric.mem_ball, Real.dist_eq] using ht
    apply lt_of_le_of_lt _ hpn
    apply div_le_div_of_nonneg_right _ hr.le
    exact (norm_heightPerturb_le h i t).trans (by linarith)
  have hLip : ∀ᵐ p ∂volume, LipschitzOnWith (Real.nnabs (B.indicator (fun _ => (1 : ℝ)) p))
      (fun t => atomicExcess S X (heightPerturb h i t) p) (Metric.ball 0 1) := by
    apply ae_of_all
    intro p
    by_cases hp : p ∈ B
    · rw [indicator_of_mem hp]
      simpa using (atomicExcess_lipschitz_coordinate S X h i p).lipschitzOnWith
    · rw [indicator_of_notMem hp]
      rw [show Real.nnabs (0 : ℝ) = (0 : ℝ≥0) by ext; simp]
      rw [← Real.toNNReal_zero]
      apply LipschitzOnWith.of_dist_le'
      intro s hs t ht
      rw [hzero hp hs, hzero hp ht]
      simp
  have hbound : Integrable (B.indicator (fun _ => (1 : ℝ))) volume :=
    (integrable_indicator_iff hBm).mpr (integrableOn_const hBfin)
  have hD := hasDerivAt_integral_of_dominated_loc_of_lip
    (μ := volume) (𝕜 := ℝ) (x₀ := (0 : ℝ)) (ε := 1)
    (F := fun t p => atomicExcess S X (heightPerturb h i t) p)
    (F' := (atomicCell S X h i).indicator (fun _ => (1 : ℝ)))
    (bound := B.indicator (fun _ => (1 : ℝ))) (by norm_num)
    (Eventually.of_forall hFmeas) (atomicExcess_integrable hS hr hb _)
    (measurable_const.indicator hCm).aestronglyMeasurable hLip hbound
    (atomicExcess_ae_hasDerivAt_coordinate hS hX hr hb h i)
  simpa only [integral_indicator_const _ hCm, smul_eq_mul, mul_one, measureReal_def] using hD.2

lemma atomicDirichletEnergy_hasDerivAt [NeZero n] {S : Set (E n)} (hS : IsCompact S)
    {X : ι → E n} (hX : Function.Injective X) {r : ℝ} (hr : 0 < r)
    (hb : ∀ j, Metric.closedBall (X j) r ⊆ S) (mass h : ι → ℝ) (i : ι) :
    HasDerivAt (fun t => atomicDirichletEnergy S X mass (heightPerturb h i t))
      ((volume (atomicCell S X h i)).toReal - mass i) 0 := by
  have he (t : ℝ) : (∑ j, mass j * heightPerturb h i t j) = (∑ j, mass j * h j) + t * mass i := by
    simp only [heightPerturb, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
    congr 1
    simp [Pi.single_apply, mul_comm, eq_comm]
  have hlin : HasDerivAt (fun t : ℝ => (∑ j, mass j * h j) + t * mass i) (mass i) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (mass i)).const_add (∑ j, mass j * h j)
  have hd := (integral_atomicExcess_hasDerivAt hS hX hr hb h i).sub hlin
  convert hd using 1
  funext t
  rw [atomicDirichletEnergy, he]
  rfl

lemma derivative_nonneg_of_right_min {f : ℝ → ℝ} {d : ℝ} (hd : HasDerivAt f d 0)
    (hmin : ∀ t, 0 ≤ t → f 0 ≤ f t) : 0 ≤ d := by
  have hl := (hasDerivAt_iff_tendsto_slope.mp hd).mono_left (nhdsGT_le_nhdsNE (0 : ℝ))
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hl
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : 0 < t := ht
  simp only [slope_def_field, sub_zero]
  exact div_nonneg (sub_nonneg.mpr (hmin t ht'.le)) ht'.le

/-- Every minimizing height is strictly positive, and each literal atomic
cell has exactly its prescribed real volume. -/
theorem atomic_minimizer_cells [NeZero n] {S : Set (E n)} (hS : IsCompact S)
    {X : ι → E n} (hX : Function.Injective X) {r : ℝ} (hr : 0 < r)
    (hb : ∀ j, Metric.closedBall (X j) r ⊆ S) {mass h : ι → ℝ}
    (hmass : ∀ i, 0 < mass i) (hh : ∀ i, 0 ≤ h i)
    (hmin : ∀ k : ι → ℝ, (∀ i, 0 ≤ k i) → atomicDirichletEnergy S X mass h ≤ atomicDirichletEnergy S X mass k) :
    (∀ i, 0 < h i) ∧ ∀ i, (volume (atomicCell S X h i)).toReal = mass i := by
  have hd (i : ι) := atomicDirichletEnergy_hasDerivAt hS hX hr hb mass h i
  have hright (i : ι) : 0 ≤ (volume (atomicCell S X h i)).toReal - mass i := by
    apply derivative_nonneg_of_right_min (hd i)
    intro t ht
    have hk : ∀ j, 0 ≤ heightPerturb h i t j := by
      intro j
      by_cases hji : j = i
      · subst j
        simp only [heightPerturb, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
        exact add_nonneg (hh i) ht
      · simpa [heightPerturb, Pi.single_apply, hji] using hh j
    simpa [heightPerturb] using hmin (heightPerturb h i t) hk
  have hpos (i : ι) : 0 < h i := by
    by_contra! hi
    have hempty := atomicCell_empty_of_height_nonpos hS hr hb hi
    have hnonneg := hright i
    rw [hempty, measure_empty, ENNReal.toReal_zero, zero_sub] at hnonneg
    linarith [hmass i]
  refine ⟨hpos, fun i => ?_⟩
  have hlocal : IsLocalMin (fun t => atomicDirichletEnergy S X mass (heightPerturb h i t)) 0 := by
    filter_upwards [eventually_gt_nhds (show -h i < (0 : ℝ) by linarith [hpos i])] with t ht
    have hk : ∀ j, 0 ≤ heightPerturb h i t j := by
      intro j
      by_cases hji : j = i
      · subst j
        simp only [heightPerturb, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
        linarith
      · simpa [heightPerturb, Pi.single_apply, hji] using hh j
    simpa [heightPerturb] using hmin (heightPerturb h i t) hk
  have he : (volume (atomicCell S X h i)).toReal - mass i = 0 := by
    rw [← (hd i).deriv, hlocal.deriv_eq_zero]
  linarith

lemma atomicCell_measure_ne_top {S : Set (E n)} (hS : IsCompact S)
    {X : ι → E n} {r : ℝ} (hr : 0 < r) (hb : ∀ j, Metric.closedBall (X j) r ⊆ S)
    (h : ι → ℝ) (i : ι) : volume (atomicCell S X h i) ≠ ⊤ := by
  apply ne_top_of_le_ne_top ((isCompact_closedBall (0 : E n) (‖h‖ / r)).measure_ne_top (μ := volume))
  apply measure_mono
  intro p hp
  have hgap := boundarySupport_ge_inner_add_norm hS hr (hb i) p
  have hh := (le_abs_self (h i)).trans (by simpa using norm_le_pi_norm h i)
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (le_div_iff₀ hr).mpr
  have hc := hp.1
  nlinarith

/-- Every finite positive interior atomic datum has genuinely constructed
positive cell heights with exactly the prescribed Lebesgue cell volumes. -/
theorem exists_atomic_cell_heights [NeZero n] {S : Set (E n)} (hS : IsCompact S)
    (X : ι → E n) (hX : Function.Injective X) (hXi : ∀ i, X i ∈ interior S)
    (mass : ι → ℝ) (hmass : ∀ i, 0 < mass i) :
    ∃ h : ι → ℝ, (∀ i, 0 < h i) ∧ ∀ i, volume (atomicCell S X h i) = ENNReal.ofReal (mass i) := by
  have hXC : IsCompact (Set.range X) := (Set.finite_range X).isCompact
  have hXI : Set.range X ⊆ interior S := by rintro _ ⟨i, rfl⟩; exact hXi i
  obtain ⟨r, hr, hthick⟩ := hXC.exists_cthickening_subset_open isOpen_interior hXI
  have hb : ∀ i, Metric.closedBall (X i) r ⊆ S := fun i =>
    ((Metric.closedBall_subset_cthickening (Set.mem_range_self i) r).trans hthick).trans interior_subset
  obtain ⟨R, hR⟩ := hS.exists_bound_of_continuousOn (continuous_id.continuousOn)
  have hR' : ∀ x ∈ S, ‖x‖ ≤ max R 0 := fun x hx => (hR x hx).trans (le_max_left _ _)
  obtain ⟨h, hh, hmin⟩ := exists_atomicDirichletEnergy_minimizer hS hr (le_max_right R 0)
    hb hR' mass (fun i => (hmass i).le)
  obtain ⟨hpos, hvol⟩ := atomic_minimizer_cells hS hX hr hb hmass hh hmin
  refine ⟨h, hpos, fun i => ?_⟩
  have he := congrArg ENNReal.ofReal (hvol i)
  rwa [ENNReal.ofReal_toReal (atomicCell_measure_ne_top hS hr hb h i)] at he

end GaussianTilt.MomentMapRegularity
