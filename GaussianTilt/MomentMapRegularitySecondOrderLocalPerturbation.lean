import GaussianTilt.MomentMapRegularitySecondOrderBarriers
import GaussianTilt.MomentMapRegularityDirichletComparison

/-!
# Perturbation estimates on the actual bounded section

The comparison solution need only have supporting planes relative to the
bounded domain. No finite convex extension outside the Dirichlet domain is
assumed. The identities are required only on interior compact subsets.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators Gradient NNReal ENNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

lemma finite_density_mass_on_compact {f : E n → ℝ} (hf : Continuous f)
    {S : Set (E n)} (hS : IsCompact S) :
    (volume.withDensity (fun y => ENNReal.ofReal (f y))) S ≠ ⊤ := by
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn hf.continuousOn
  have hb : (volume.withDensity (fun y => ENNReal.ofReal (f y))) S ≤
      ENNReal.ofReal M * volume S := by
    apply withDensity_le_const_mul_of_ae hS.measurableSet
    filter_upwards [ae_restrict_mem hS.measurableSet] with y hy
    apply ENNReal.ofReal_le_ofReal
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hM y hy)
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hS.measure_ne_top) hb

lemma alexandrovOn_identity_scaled_constant {v : E n → ℝ} {d : ℝ} {S : Set (E n)}
    (hvid : ∀ A : Set (E n), IsCompact A → A ⊆ interior S →
      volume (subgradientImageOn S v A) = ENNReal.ofReal d * volume A)
    {t : ℝ} (ht : 0 < t) (b : ℝ) {A : Set (E n)} (hA : IsCompact A) (hAS : A ⊆ interior S) :
    volume (subgradientImageOn S (fun y => t * v y + b) A) =
      (volume.withDensity (fun _ => ENNReal.ofReal (t ^ n * d))) A := by
  rw [volume_subgradientImageOn_pos_mul_add_const S v ht b A, hvid A hA hAS,
    withDensity_apply _ hA.measurableSet, setLIntegral_const,
    ENNReal.ofReal_mul (pow_nonneg ht.le _), mul_assoc]

/-- Constant-density stability on the actual bounded domain. Convexity
outside that domain is not a premise. -/
theorem alexandrovOn_constant_density_sandwich [NeZero n] {u v f : E n → ℝ}
    (huc : Continuous u) (hvc : Continuous v) (hfc : Continuous f)
    {S : Set (E n)} (hS : IsCompact S)
    (hbu : ∀ y ∈ frontier S, u y = 0) (hbv : ∀ y ∈ frontier S, v y = 0)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hf : ∀ y ∈ interior S, (1 - δ) ^ n ≤ f y ∧ f y ≤ (1 + δ) ^ n)
    (huid : ∀ A : Set (E n), IsCompact A → A ⊆ interior S →
      volume (subgradientImageOn S u A) = (volume.withDensity (fun y => ENNReal.ofReal (f y))) A)
    (hvid : ∀ A : Set (E n), IsCompact A → A ⊆ interior S →
      volume (subgradientImageOn S v A) = volume A) :
    ∀ x ∈ S, (1 + δ) * v x ≤ u x ∧ u x ≤ (1 - δ) * v x := by
  have hminus : 0 < 1 - δ := sub_pos.mpr hδ1
  have hplus : 0 < 1 + δ := by linarith
  have hfp : ∀ y ∈ interior S, 0 < f y :=
    fun y hy => (pow_pos hminus _).trans_le (hf y hy).1
  have hvid' : ∀ A : Set (E n), IsCompact A → A ⊆ interior S →
      volume (subgradientImageOn S v A) = ENNReal.ofReal 1 * volume A := by simpa using hvid
  have hscale (t : ℝ) (ht : 0 < t) : ∀ A : Set (E n), IsCompact A → A ⊆ interior S →
      volume (subgradientImageOn S (fun y => t * v y) A) =
        (volume.withDensity (fun _ => ENNReal.ofReal (t ^ n))) A := by
    intro A hA hAS
    simpa using alexandrovOn_identity_scaled_constant hvid' ht 0 hA hAS
  have hlo := alexandrovOn_comparison_of_density_le huc (continuous_const.mul hvc) hS
    (fun y hy => by simp [hbu y hy, hbv y hy]) measurable_const
    (fun y hy => (hfp y hy).le) (fun _ _ => pow_pos hplus n)
    (fun y hy => (hf y hy).2) (finite_density_mass_on_compact hfc hS) huid (hscale _ hplus)
  have hhi := alexandrovOn_comparison_of_density_le
    (continuous_const.mul hvc) huc hS
    (fun y hy => by simp [hbu y hy, hbv y hy]) hfc.measurable
    (fun _ _ => (pow_pos hminus n).le) hfp (fun y hy => (hf y hy).1)
    (finite_density_mass_on_compact continuous_const hS) (hscale _ hminus) huid
  exact fun x hx => ⟨hlo x hx, hhi x hx⟩

theorem alexandrovOn_constant_density_perturbation [NeZero n] {u v f : E n → ℝ}
    (huc : Continuous u) (hvc : Continuous v) (hfc : Continuous f)
    {S : Set (E n)} (hS : IsCompact S)
    (hbu : ∀ y ∈ frontier S, u y = 0) (hbv : ∀ y ∈ frontier S, v y = 0)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hf : ∀ y ∈ interior S, |f y - 1| ≤ δ)
    (huid : ∀ A : Set (E n), IsCompact A → A ⊆ interior S →
      volume (subgradientImageOn S u A) = (volume.withDensity (fun y => ENNReal.ofReal (f y))) A)
    (hvid : ∀ A : Set (E n), IsCompact A → A ⊆ interior S →
      volume (subgradientImageOn S v A) = volume A) :
    ∀ x ∈ S, |u x - v x| ≤ δ * |v x| := by
  have hpminus : (1 - δ) ^ n ≤ 1 - δ :=
    pow_le_of_le_one (sub_pos.mpr hδ1).le (by linarith) (NeZero.ne n)
  have hpplus : 1 + δ ≤ (1 + δ) ^ n :=
    le_self_pow₀ (by linarith : (1 : ℝ) ≤ 1 + δ) (NeZero.ne n)
  have hs := alexandrovOn_constant_density_sandwich huc hvc hfc hS hbu hbv hδ hδ1
    (fun y hy => ⟨hpminus.trans (by linarith [(abs_le.mp (hf y hy)).1]),
      (by linarith [(abs_le.mp (hf y hy)).2, hpplus])⟩) huid hvid
  intro x hx
  obtain ⟨hlo, hhi⟩ := hs x hx
  apply abs_le.mpr
  constructor <;> nlinarith [le_abs_self (v x), neg_abs_le (v x)]

/-- The actual bounded-domain supporting image of the unit paraboloid is
the source set on interior subsets of the domain. -/
lemma subgradientImageOn_unit_paraboloid {S A : Set (E n)} (hA : A ⊆ interior S) (c : ℝ) :
    subgradientImageOn S (fun y => ‖y‖ ^ 2 / 2 + c) A = A := by
  rw [subgradientImageOn_eq_global (convexOn_unit_paraboloid c) hA,
    subgradientImage_unit_paraboloid]

lemma volume_subgradientImageOn_constant [NeZero n] {S A : Set (E n)}
    (hA : A ⊆ interior S) (c : ℝ) :
    volume (subgradientImageOn S (fun _ => c) A) = 0 := by
  rw [subgradientImageOn_eq_global (convexOn_const c convex_univ) hA,
    volume_subgradientImage_constant]

/-- Explicit barriers for an actual bounded-domain unit-density solution. -/
theorem alexandrovOn_unit_density_barriers [NeZero n] {v : E n → ℝ}
    (hvc : Continuous v) {S : Set (E n)} (hS : IsCompact S)
    {R : ℝ} (hR : 0 ≤ R) (hSR : S ⊆ Metric.closedBall (0 : E n) R)
    (hbv : ∀ y ∈ frontier S, v y = 0)
    (hvid : ∀ A : Set (E n), IsCompact A → A ⊆ interior S →
      volume (subgradientImageOn S v A) = volume A) :
    ∀ x ∈ S, ‖x‖ ^ 2 / 2 - R ^ 2 / 2 ≤ v x ∧ v x ≤ 0 := by
  let q : E n → ℝ := fun y => ‖y‖ ^ 2 / 2 - R ^ 2 / 2
  have hqc : Continuous q := by fun_prop
  have hvid' : ∀ A : Set (E n), IsCompact A → A ⊆ interior S → volume (subgradientImageOn S v A) =
      (volume.withDensity (fun _ => ENNReal.ofReal (1 : ℝ))) A := by simpa using hvid
  have hqid : ∀ A : Set (E n), IsCompact A → A ⊆ interior S → volume (subgradientImageOn S q A) =
      (volume.withDensity (fun _ => ENNReal.ofReal (1 : ℝ))) A := by
    intro A _ hAS
    simpa [q, sub_eq_add_neg] using congrArg (fun B => volume B)
      (subgradientImageOn_unit_paraboloid hAS (-(R ^ 2 / 2)))
  have hqb : ∀ y ∈ frontier S, q y ≤ v y := by
    intro y hy
    rw [hbv y hy]
    have hn : ‖y‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hSR (hS.isClosed.closure_subset hy.1)
    dsimp [q]
    nlinarith [norm_nonneg y]
  have hlo := alexandrovOn_comparison_of_density_le hvc hqc hS hqb measurable_const
    (fun _ _ => zero_le_one) (fun _ _ => zero_lt_one) (fun _ _ => le_rfl)
    (finite_density_mass_on_compact continuous_const hS) hvid' hqid
  have hzid : ∀ A : Set (E n), IsCompact A → A ⊆ interior S → volume (subgradientImageOn S (fun _ => (0 : ℝ)) A) =
      (volume.withDensity (fun _ => ENNReal.ofReal (0 : ℝ))) A := by
    intro A _ hAS
    rw [volume_subgradientImageOn_constant hAS]
    simp
  have hhi := alexandrovOn_comparison_of_density_le continuous_const hvc hS
    (fun y hy => (hbv y hy).le) measurable_const
    (fun _ _ => le_rfl) (fun _ _ => zero_lt_one) (fun _ _ => zero_le_one)
    (finite_density_mass_on_compact continuous_const hS) hzid hvid'
  exact fun x hx => ⟨hlo x hx, hhi x hx⟩

/-- The quantitative constant-density perturbation estimate used on an
affinely normalized section, with the correct local Dirichlet interface. -/
theorem alexandrovOn_normalized_constant_density_perturbation [NeZero n] {u v f : E n → ℝ}
    (huc : Continuous u) (hvc : Continuous v) (hfc : Continuous f)
    {S : Set (E n)} (hS : IsCompact S) {R : ℝ} (hR : 0 ≤ R)
    (hSR : S ⊆ Metric.closedBall (0 : E n) R)
    (hbu : ∀ y ∈ frontier S, u y = 0) (hbv : ∀ y ∈ frontier S, v y = 0)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hf : ∀ y ∈ interior S, |f y - 1| ≤ δ)
    (huid : ∀ A : Set (E n), IsCompact A → A ⊆ interior S →
      volume (subgradientImageOn S u A) = (volume.withDensity (fun y => ENNReal.ofReal (f y))) A)
    (hvid : ∀ A : Set (E n), IsCompact A → A ⊆ interior S →
      volume (subgradientImageOn S v A) = volume A) :
    ∀ x ∈ S, |u x - v x| ≤ δ * R ^ 2 / 2 := by
  intro x hx
  have he := alexandrovOn_constant_density_perturbation huc hvc hfc hS hbu hbv hδ hδ1 hf huid hvid x hx
  obtain ⟨hlo, hhi⟩ := alexandrovOn_unit_density_barriers hvc hS hR hSR hbv hvid x hx
  have hvb : |v x| ≤ R ^ 2 / 2 := by rw [abs_of_nonpos hhi]; nlinarith [sq_nonneg ‖x‖]
  exact he.trans (by nlinarith)

end GaussianTilt.MomentMapRegularity
