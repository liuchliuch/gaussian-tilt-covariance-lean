import GaussianTilt.MomentMapRegularityReferenceClassicalMeasure

/-! # Pointwise density bounds from true local compact-set inequalities -/
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

lemma continuous_ge_one_of_compact_integral_lower {U : Set (E n)} (hU : IsOpen U)
    {f : E n → ℝ} (hf : ContinuousOn f U) (hfn : ∀ x ∈ U, 0 ≤ f x)
    (hineq : ∀ A : Set (E n), IsCompact A → A ⊆ U →
      volume A ≤ ∫⁻ y in A, ENNReal.ofReal (f y)) {x : E n} (hx : x ∈ U) : 1 ≤ f x := by
  by_contra hn
  have hlt : f x < 1 := lt_of_not_ge hn
  let q := (f x+1)/2
  have hq : f x < q := by dsimp [q]; linarith
  have hq1 : q < 1 := by dsimp [q]; linarith
  have hmemU : ∀ᶠ y in 𝓝 x, y ∈ U := hU.mem_nhds hx
  have hnear : ∀ᶠ y in 𝓝 x, y ∈ U ∧ f y < q :=
    hmemU.and ((hf x hx).continuousAt (hU.mem_nhds hx) |>.eventually (eventually_lt_nhds hq))
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp hnear
  let A := Metric.closedBall x (r/2)
  have hA : IsCompact A := isCompact_closedBall _ _
  have hmem (y : E n) (hy : y ∈ A) : y ∈ U ∧ f y < q :=
    hball (lt_of_le_of_lt hy (half_lt_self hr))
  have hp : 0 < volume A := measure_closedBall_pos volume x (half_pos hr)
  have hfin : volume A ≠ ⊤ := hA.measure_ne_top
  have h1 := hineq A hA (fun y hy => (hmem y hy).1)
  have h2 : (∫⁻ y in A, ENNReal.ofReal (f y)) ≤ ENNReal.ofReal q * volume A := by
    calc
      _ ≤ ∫⁻ _y in A, ENNReal.ofReal q := by
        apply setLIntegral_mono' hA.measurableSet
        intro y hy
        exact ENNReal.ofReal_le_ofReal (hmem y hy).2.le
      _ = _ := by simp
  have hqE : ENNReal.ofReal q < 1 := ENNReal.ofReal_lt_one.mpr hq1
  have h3 : ENNReal.ofReal q * volume A < volume A := by
    simpa only [one_mul] using (ENNReal.mul_lt_mul_right hp.ne' hfin).mpr hqE
  exact h3.not_ge (h1.trans h2)

lemma continuous_le_one_of_compact_integral_upper {U : Set (E n)} (hU : IsOpen U)
    {f : E n → ℝ} (hf : ContinuousOn f U)
    (hineq : ∀ A : Set (E n), IsCompact A → A ⊆ U →
      (∫⁻ y in A, ENNReal.ofReal (f y)) ≤ volume A) {x : E n} (hx : x ∈ U) : f x ≤ 1 := by
  by_contra hn
  have hlt : 1 < f x := lt_of_not_ge hn
  let q := (f x+1)/2
  have hq : q < f x := by dsimp [q]; linarith
  have hq1 : 1 < q := by dsimp [q]; linarith
  have hmemU : ∀ᶠ y in 𝓝 x, y ∈ U := hU.mem_nhds hx
  have hnear : ∀ᶠ y in 𝓝 x, y ∈ U ∧ q < f y :=
    hmemU.and ((hf x hx).continuousAt (hU.mem_nhds hx) |>.eventually (eventually_gt_nhds hq))
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp hnear
  let A := Metric.closedBall x (r/2)
  have hA : IsCompact A := isCompact_closedBall _ _
  have hmem (y : E n) (hy : y ∈ A) : y ∈ U ∧ q < f y :=
    hball (lt_of_le_of_lt hy (half_lt_self hr))
  have hp : 0 < volume A := measure_closedBall_pos volume x (half_pos hr)
  have hfin : volume A ≠ ⊤ := hA.measure_ne_top
  have h1 := hineq A hA (fun y hy => (hmem y hy).1)
  have h2 : ENNReal.ofReal q * volume A ≤ ∫⁻ y in A, ENNReal.ofReal (f y) := by
    calc
      _ = ∫⁻ _y in A, ENNReal.ofReal q := by simp
      _ ≤ _ := by
        apply setLIntegral_mono' hA.measurableSet
        intro y hy
        exact ENNReal.ofReal_le_ofReal (hmem y hy).2.le
  have hqE : 1 < ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_lt_ofReal_iff (zero_lt_one.trans hq1) |>.mpr hq1
  have h3 : volume A < ENNReal.ofReal q * volume A := by
    simpa only [one_mul] using (ENNReal.mul_lt_mul_right hp.ne' hfin).mpr hqE
  exact h3.not_ge (h2.trans h1)

end GaussianTilt.MomentMapRegularity
