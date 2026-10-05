import GaussianTilt.Paouris

/-!
# The density-body gauge is a genuine norm

The geometric nondegeneracy argument uses a rank-one dilation: a nonzero
kernel vector of a seminorm would leave its open unit ball invariant under
a linear map of determinant two, contradicting its positive finite volume.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators

namespace GaussianTilt.Paouris

variable {n : ℕ} {f : Reference.Space n → ℝ}

lemma density_at_zero_pos (hf : Reference.logconcaveDensity f)
    (heven : Function.Even f) (hnorm : ∫ x, f x = 1) : 0 < f 0 := by
  by_contra h
  have heq : f = 0 := by
    ext x
    exact le_antisymm ((density_le_at_zero hf heven x).trans (not_lt.mp h)) (hf.1 x)
  simp only [heq, Pi.zero_apply, integral_zero] at hnorm
  norm_num at hnorm

lemma densityBody_volume_lt_top (hf : Reference.logconcaveDensity f)
    (heven : Function.Even f) (hnorm : ∫ x, f x = 1) :
    volume (densityBody f) < ⊤ :=
  (integrable_of_integral_eq_one hnorm).measure_ge_lt_top
    (div_pos (density_at_zero_pos hf heven hnorm) (by positivity))

/-- The rank-one expansion along `x`, normalized using a nonzero coordinate. -/
def coordinateDilation (x : Reference.Space n) (i : Fin n) :
    Reference.Space n →ₗ[ℝ] Reference.Space n :=
  LinearMap.id + (((x i)⁻¹ • LinearMap.proj i).comp
    (EuclideanSpace.equiv (Fin n) ℝ).toLinearMap).smulRight x

lemma coordinateDilation_apply (x y : Reference.Space n) (i : Fin n) :
    coordinateDilation x i y = y + (y i / x i) • x := by
  simp only [coordinateDilation, LinearMap.add_apply, LinearMap.id_apply,
    LinearMap.smulRight_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul]
  congr 2
  change (x i)⁻¹ * y i = y i / x i
  ring

lemma coordinateDilation_det (x : Reference.Space n) (i : Fin n) (hi : x i ≠ 0) :
    LinearMap.det (coordinateDilation x i) = 2 := by
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let v : Fin n → ℝ := Pi.single i ((x i)⁻¹)
  have hm : LinearMap.toMatrix b b (coordinateDilation x i) =
      1 + Matrix.replicateCol Unit (fun j ↦ x j) * Matrix.replicateRow Unit v := by
    ext j k
    simp only [LinearMap.toMatrix_apply, coordinateDilation_apply, b,
      OrthonormalBasis.coe_toBasis, OrthonormalBasis.coe_toBasis_repr_apply,
      EuclideanSpace.basisFun_repr, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul, EuclideanSpace.basisFun_apply, EuclideanSpace.single_apply,
      Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply, Matrix.replicateCol_apply,
      Matrix.replicateRow_apply, Finset.univ_unique, Finset.sum_singleton, v]
    by_cases hki : k = i <;> by_cases hjk : j = k <;> simp_all [Pi.single_apply, eq_comm]
    <;> ring
  rw [← LinearMap.det_toMatrix b, hm,
    Matrix.det_one_add_replicateCol_mul_replicateRow]
  norm_num [v, dotProduct, Pi.single_apply, hi]

/-- A seminorm whose open unit ball has positive finite volume is a norm.
The proof supplies the geometric step often left implicit in the density-body
argument. -/
theorem seminorm_definite_of_ball_volume (p : Seminorm ℝ (Reference.Space n))
    (hpos : 0 < volume {x | p x < 1}) (hfinite : volume {x | p x < 1} < ⊤)
    {x : Reference.Space n} (hx : p x = 0) : x = 0 := by
  by_contra hxne
  obtain ⟨i, hi⟩ : ∃ i : Fin n, x i ≠ 0 := by
    by_contra h
    push_neg at h
    apply hxne
    ext j
    exact h j
  have hsub : coordinateDilation x i '' {y | p y < 1} ⊆ {y | p y < 1} := by
    rintro _ ⟨y, hy, rfl⟩
    change p (coordinateDilation x i y) < 1
    rw [coordinateDilation_apply]
    apply lt_of_le_of_lt (map_add_le_add p _ _) ?_
    rw [map_smul_eq_mul, hx, mul_zero, add_zero]
    exact hy
  have hm := measure_mono (μ := (volume : Measure (Reference.Space n))) hsub
  rw [Measure.addHaar_image_linearMap volume, coordinateDilation_det x i hi] at hm
  norm_num at hm
  have hr := ENNReal.toReal_mono hfinite.ne hm
  have hp := ENNReal.toReal_pos hpos.ne' hfinite.ne
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat] at hr
  linarith

/-- The actual density gauge as a bundled seminorm. -/
def densitySeminorm (hf : Reference.logconcaveDensity f)
    (heven : Function.Even f) (hn : 0 < n) (hnorm : ∫ x, f x = 1) :
    Seminorm ℝ (Reference.Space n) :=
  gaugeSeminorm ((balanced_iff_neg_mem (densityBody_convex hf)).mpr
    (fun _ hx ↦ densityBody_neg_mem heven hx)) (densityBody_convex hf)
    (absorbent_nhds_zero (densityBody_mem_nhds_zero hf heven hn hnorm))

@[simp] lemma densitySeminorm_apply (hf : Reference.logconcaveDensity f)
    (heven : Function.Even f) (hn : 0 < n) (hnorm : ∫ x, f x = 1)
    (x : Reference.Space n) :
    densitySeminorm hf heven hn hnorm x = densityGauge f x := rfl

/-- Nondegeneracy of the constructed gauge follows from the density
normalization, not an extra geometric assumption. -/
theorem densityGauge_eq_zero_iff (hf : Reference.logconcaveDensity f)
    (heven : Function.Even f) (hn : 0 < n) (hnorm : ∫ x, f x = 1)
    (x : Reference.Space n) : densityGauge f x = 0 ↔ x = 0 := by
  refine ⟨fun hx ↦ ?_, fun hx ↦ by simp [hx, densityGauge]⟩
  have hnhds := densityBody_mem_nhds_zero hf heven hn hnorm
  have heq : {y | densitySeminorm hf heven hn hnorm y < 1} = interior (densityBody f) :=
    gauge_lt_one_eq_interior (densityBody_convex hf) hnhds
  refine seminorm_definite_of_ball_volume (densitySeminorm hf heven hn hnorm) ?_ ?_ hx
  · rw [heq]
    exact isOpen_interior.measure_pos volume (densityBody_interior_nonempty hf hn hnorm)
  · rw [heq]
    exact lt_of_le_of_lt (measure_mono interior_subset) (densityBody_volume_lt_top hf heven hnorm)

/-- The density body produces a genuine norm, encoded as an `AddGroupNorm`
with its real homogeneity proved below. -/
def densityNorm (hf : Reference.logconcaveDensity f)
    (heven : Function.Even f) (hn : 0 < n) (hnorm : ∫ x, f x = 1) :
    AddGroupNorm (Reference.Space n) where
  toAddGroupSeminorm := (densitySeminorm hf heven hn hnorm).toAddGroupSeminorm
  eq_zero_of_map_eq_zero' x hx := (densityGauge_eq_zero_iff hf heven hn hnorm x).mp hx

@[simp] lemma densityNorm_apply (hf : Reference.logconcaveDensity f)
    (heven : Function.Even f) (hn : 0 < n) (hnorm : ∫ x, f x = 1)
    (x : Reference.Space n) :
    densityNorm hf heven hn hnorm x = densityGauge f x := rfl

lemma densityNorm_smul (hf : Reference.logconcaveDensity f)
    (heven : Function.Even f) (hn : 0 < n) (hnorm : ∫ x, f x = 1)
    (a : ℝ) (x : Reference.Space n) :
    densityNorm hf heven hn hnorm (a • x) = |a| * densityNorm hf heven hn hnorm x :=
  map_smul_eq_mul (densitySeminorm hf heven hn hnorm) a x

/-- Full density-body norm lemma in the short proof of Paouris: for every
even normalized logconcave density in positive dimension there is a genuine
continuous norm whose dimension-th moment is at most 500 times its first
moment. Both moments are proved integrable. -/
theorem exists_norm_moment_comparison (hf : Reference.logconcaveDensity f)
    (heven : Function.Even f) (hn : 0 < n) (hnorm : ∫ x, f x = 1) :
    ∃ q : AddGroupNorm (Reference.Space n),
      Continuous q ∧ (∀ (a : ℝ) x, q (a • x) = |a| * q x) ∧
      Integrable (fun x ↦ q x * f x) ∧ Integrable (fun x ↦ q x ^ n * f x) ∧
      (∫ x, q x ^ n * f x) ^ (1 / (n : ℝ)) ≤ 500 * ∫ x, q x * f x := by
  refine ⟨densityNorm hf heven hn hnorm,
    densityGauge_continuous hf heven hn hnorm,
    densityNorm_smul hf heven hn hnorm,
    densityGauge_firstMoment_integrable hf heven hn hnorm,
    densityGauge_moment_integrable hf heven hn hnorm,
    densityGauge_moment_comparison hf heven hn hnorm⟩

/-- Conversion from the independent density specification to actual
Bochner expectations under the corresponding law. -/
lemma integral_densityLaw (hf : Reference.logconcaveDensity f)
    (g : Reference.Space n → ℝ) :
    (∫ x, g x ∂volume.withDensity (fun x ↦ ENNReal.ofReal (f x))) =
      ∫ x, g x * f x := by
  have h := integral_withDensity_eq_integral_toReal_smul (μ := volume) hf.2.1.ennreal_ofReal
    (Filter.Eventually.of_forall fun x ↦ ENNReal.ofReal_lt_top) g
  simpa only [ENNReal.toReal_ofReal (hf.1 _), smul_eq_mul, mul_comm] using h

lemma integrable_densityLaw_iff (hf : Reference.logconcaveDensity f)
    (g : Reference.Space n → ℝ) :
    Integrable g (volume.withDensity (fun x ↦ ENNReal.ofReal (f x))) ↔
      Integrable (fun x ↦ g x * f x) := by
  have h := integrable_withDensity_iff_integrable_smul' (μ := volume)
    hf.2.1.ennreal_ofReal (Filter.Eventually.of_forall fun x ↦ ENNReal.ofReal_lt_top)
    (g := g)
  simpa only [ENNReal.toReal_ofReal (hf.1 _), smul_eq_mul, mul_comm] using h

lemma density_integral_eq_one_of_probability (hf : Reference.logconcaveDensity f)
    [IsProbabilityMeasure (volume.withDensity (fun x ↦ ENNReal.ofReal (f x)))] :
    ∫ x, f x = 1 := by
  have h := integral_densityLaw hf (fun _ ↦ 1)
  simpa only [one_mul, integral_const, measureReal_univ_eq_one, smul_eq_mul, mul_one] using h.symm

/-- The norm-comparison lemma for an actual probability law satisfying the
project's independent logconcave-density specification. -/
theorem exists_norm_moment_comparison_probability
    (μ : Measure (Reference.Space n)) [IsProbabilityMeasure μ]
    (hf : Reference.logconcaveDensity f) (heven : Function.Even f)
    (hμ : μ = volume.withDensity (fun x ↦ ENNReal.ofReal (f x))) (hn : 0 < n) :
    ∃ q : AddGroupNorm (Reference.Space n),
      Continuous q ∧ (∀ (a : ℝ) x, q (a • x) = |a| * q x) ∧
      Integrable q μ ∧ Integrable (fun x ↦ q x ^ n) μ ∧
      (∫ x, q x ^ n ∂μ) ^ (1 / (n : ℝ)) ≤ 500 * ∫ x, q x ∂μ := by
  subst μ
  obtain ⟨q, hc, hs, hi₁, hiₙ, hm⟩ :=
    exists_norm_moment_comparison hf heven hn (density_integral_eq_one_of_probability hf)
  refine ⟨q, hc, hs, (integrable_densityLaw_iff hf _).mpr hi₁,
    (integrable_densityLaw_iff hf _).mpr hiₙ, ?_⟩
  rw [integral_densityLaw hf, integral_densityLaw hf]
  exact hm

end GaussianTilt.Paouris
