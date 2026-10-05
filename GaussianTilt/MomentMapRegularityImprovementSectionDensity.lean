import GaussianTilt.MomentMapRegularityImprovementNormalizedSection

/-! # Small relative density oscillation on the actual normalized section -/
noncomputable section
open Set Metric
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

/-- Actual source Hölder density bounds become uniformly small after
centered section normalization. Both the full-section oscillation and the
centered Hölder modulus are derived. -/
theorem normalized_section_density_bounds {f : E n → ℝ}
    (T : E n ≃L[ℝ] E n) {S K : Set (E n)} {x : E n} {α F m ε M : ℝ}
    (hα : 0≤α) (hF : 0≤F) (hm : 0 < m) (hε : 0≤ε) (hM : 0≤M)
    (hx : x∈K) (hSK : S⊆K) (hSball : S⊆closedBall x ε) (hfm : m≤f x)
    (hT : ‖(T.symm : E n →L[ℝ] E n)‖≤M)
    (hf : ∀ y∈K, ∀ z∈K, |f y-f z|≤F*‖y-z‖^α) :
    ∀ y∈(fun z=>T (z-x)) '' S,
      |normalizedSectionDensity f T x y-1|≤F*ε^α/m ∧
      |normalizedSectionDensity f T x y-1|≤(F*M^α/m)*‖y‖^α := by
  have hfx : 0 < f x := hm.trans_le hfm
  rintro y ⟨z,hz,rfl⟩
  have hsource : affineSource T x (T (z-x))=z := by simp [affineSource]
  have he : normalizedSectionDensity f T x (T (z-x))-1=(f z-f x)/f x := by
    simp only [normalizedSectionDensity,hsource]
    field_simp
  rw [he,abs_div,abs_of_pos hfx]
  have hbase := hf z (hSK hz) x hx
  have hnorm : ‖z-x‖≤ε := hSball hz
  have hnormM : ‖z-x‖≤M*‖T (z-x)‖ := by
    have hh := ((T.symm : E n →L[ℝ] E n).le_opNorm (T (z-x))).trans
      (mul_le_mul_of_nonneg_right hT (norm_nonneg _))
    simpa using hh
  constructor
  · have hb := hbase.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hnorm hα) hF)
    exact (div_le_div_of_nonneg_right hb hfx.le).trans
      (div_le_div_of_nonneg_left (by positivity) hm hfm)
  · have hb := hbase.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hnormM hα) hF)
    have hh := (div_le_div_of_nonneg_right hb hfx.le).trans
      (div_le_div_of_nonneg_left (by positivity) hm hfm)
    rw [Real.mul_rpow hM (norm_nonneg _)] at hh
    convert hh using 1 <;> ring

end GaussianTilt.MomentMapRegularity
