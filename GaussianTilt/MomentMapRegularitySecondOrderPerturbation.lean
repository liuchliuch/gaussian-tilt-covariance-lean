import GaussianTilt.MomentMapRegularitySecondOrderComparison

/-!
# Constant-density comparison on sections

These are genuine perturbation estimates for Alexandrov solutions. Given
a constant-density Dirichlet comparison solution, the proved comparison
principle controls the error by the oscillation of the actual density.
No Hessian, ellipticity, or second-order regularity is assumed. Existence
and interior estimates for the comparison solution remain separate steps.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators Gradient NNReal ENNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

/-- Literal compact-set Alexandrov data are unique under common boundary
values and a positive density. -/
theorem alexandrov_unique_of_same_density [NeZero n] {u v f : E n → ℝ}
    (hu : ConvexOn ℝ univ u) (hv : ConvexOn ℝ univ v)
    (huc : Continuous u) (hvc : Continuous v)
    {S : Set (E n)} (hS : IsCompact S)
    (hb : ∀ y ∈ frontier S, u y = v y)
    (hfm : Measurable f) (hfp : ∀ y ∈ interior S, 0 < f y)
    (huid : ∀ A : Set (E n), IsCompact A → A ⊆ S →
      volume (subgradientImage u A) = (volume.withDensity (fun y => ENNReal.ofReal (f y))) A)
    (hvid : ∀ A : Set (E n), IsCompact A → A ⊆ S →
      volume (subgradientImage v A) = (volume.withDensity (fun y => ENNReal.ofReal (f y))) A) :
    ∀ x ∈ S, u x = v x := by
  have hlo := alexandrov_comparison_of_density_le hu huc hvc hS
    (fun y hy => (hb y hy).ge) hfm (fun y hy => (hfp y hy).le) hfp
    (fun _ _ => le_rfl) huid hvid
  have hhi := alexandrov_comparison_of_density_le hv hvc huc hS
    (fun y hy => (hb y hy).le) hfm (fun y hy => (hfp y hy).le) hfp
    (fun _ _ => le_rfl) hvid huid
  exact fun x hx => le_antisymm (hhi x hx) (hlo x hx)

/-- A constant-density Alexandrov solution has exactly the expected
constant density after positive vertical rescaling. -/
lemma alexandrov_identity_scaled_constant {v : E n → ℝ} {d : ℝ} {S : Set (E n)}
    (hvid : ∀ A : Set (E n), IsCompact A → A ⊆ S →
      volume (subgradientImage v A) = ENNReal.ofReal d * volume A)
    {t : ℝ} (ht : 0 < t) (b : ℝ) {A : Set (E n)} (hA : IsCompact A) (hAS : A ⊆ S) :
    volume (subgradientImage (fun y => t * v y + b) A) =
      (volume.withDensity (fun _ => ENNReal.ofReal (t ^ n * d))) A := by
  rw [volume_subgradientImage_pos_mul_add_const v ht b A, hvid A hA hAS,
    withDensity_apply _ hA.measurableSet, setLIntegral_const,
    ENNReal.ofReal_mul (pow_nonneg ht.le _), mul_assoc]

/-- Density pinching between the powers `(1±δ)^n` gives a pointwise
comparison with the constant-density Dirichlet solution. -/
theorem alexandrov_constant_density_sandwich [NeZero n] {u v f : E n → ℝ}
    (hu : ConvexOn ℝ univ u) (hv : ConvexOn ℝ univ v)
    (huc : Continuous u) (hvc : Continuous v)
    {S : Set (E n)} (hS : IsCompact S)
    (hbu : ∀ y ∈ frontier S, u y = 0) (hbv : ∀ y ∈ frontier S, v y = 0)
    (hfm : Measurable f) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hf : ∀ y ∈ interior S, (1 - δ) ^ n ≤ f y ∧ f y ≤ (1 + δ) ^ n)
    (huid : ∀ A : Set (E n), IsCompact A → A ⊆ S →
      volume (subgradientImage u A) = (volume.withDensity (fun y => ENNReal.ofReal (f y))) A)
    (hvid : ∀ A : Set (E n), IsCompact A → A ⊆ S → volume (subgradientImage v A) = volume A) :
    ∀ x ∈ S, (1 + δ) * v x ≤ u x ∧ u x ≤ (1 - δ) * v x := by
  have hminus : 0 < 1 - δ := sub_pos.mpr hδ1
  have hplus : 0 < 1 + δ := by linarith
  have hfp : ∀ y ∈ interior S, 0 < f y :=
    fun y hy => (pow_pos hminus _).trans_le (hf y hy).1
  have hvid' : ∀ A : Set (E n), IsCompact A → A ⊆ S →
      volume (subgradientImage v A) = ENNReal.ofReal 1 * volume A := by simpa using hvid
  have hscale (t : ℝ) (ht : 0 < t) : ∀ A : Set (E n), IsCompact A → A ⊆ S →
      volume (subgradientImage (fun y => t * v y) A) =
        (volume.withDensity (fun _ => ENNReal.ofReal (t ^ n))) A := by
    intro A hA hAS
    simpa using alexandrov_identity_scaled_constant hvid' ht 0 hA hAS
  have hlo := alexandrov_comparison_of_density_le hu huc (continuous_const.mul hvc) hS
    (fun y hy => by simp [hbu y hy, hbv y hy]) measurable_const
    (fun y hy => (hfp y hy).le) (fun _ _ => pow_pos hplus n)
    (fun y hy => (hf y hy).2) huid (hscale _ hplus)
  have hhi := alexandrov_comparison_of_density_le (hv.smul hminus.le)
    (continuous_const.mul hvc) huc hS
    (fun y hy => by simp [hbu y hy, hbv y hy]) hfm
    (fun _ _ => (pow_pos hminus n).le) hfp (fun y hy => (hf y hy).1)
    (hscale _ hminus) huid
  exact fun x hx => ⟨hlo x hx, hhi x hx⟩

/-- The first quantitative constant-density perturbation estimate: literal
Alexandrov density oscillation at most `δ` gives an error at most `δ |v|`.
The reference `v` has the same zero boundary values and unit Alexandrov
density. This is a comparison estimate, not a regularity assumption. -/
theorem alexandrov_constant_density_perturbation [NeZero n] {u v f : E n → ℝ}
    (hu : ConvexOn ℝ univ u) (hv : ConvexOn ℝ univ v)
    (huc : Continuous u) (hvc : Continuous v)
    {S : Set (E n)} (hS : IsCompact S)
    (hbu : ∀ y ∈ frontier S, u y = 0) (hbv : ∀ y ∈ frontier S, v y = 0)
    (hfm : Measurable f) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hf : ∀ y ∈ interior S, |f y - 1| ≤ δ)
    (huid : ∀ A : Set (E n), IsCompact A → A ⊆ S →
      volume (subgradientImage u A) = (volume.withDensity (fun y => ENNReal.ofReal (f y))) A)
    (hvid : ∀ A : Set (E n), IsCompact A → A ⊆ S → volume (subgradientImage v A) = volume A) :
    ∀ x ∈ S, |u x - v x| ≤ δ * |v x| := by
  have hpminus : (1 - δ) ^ n ≤ 1 - δ :=
    pow_le_of_le_one (sub_pos.mpr hδ1).le (by linarith) (NeZero.ne n)
  have hpplus : 1 + δ ≤ (1 + δ) ^ n :=
    le_self_pow₀ (by linarith : (1 : ℝ) ≤ 1 + δ) (NeZero.ne n)
  have hs := alexandrov_constant_density_sandwich hu hv huc hvc hS hbu hbv hfm hδ hδ1
    (fun y hy => ⟨hpminus.trans (by linarith [(abs_le.mp (hf y hy)).1]),
      (by linarith [(abs_le.mp (hf y hy)).2, hpplus])⟩) huid hvid
  intro x hx
  obtain ⟨hlo, hhi⟩ := hs x hx
  apply abs_le.mpr
  constructor <;> nlinarith [le_abs_self (v x), neg_abs_le (v x)]

end GaussianTilt.MomentMapRegularity
