import GaussianTilt.MomentMapRegularityDual

/-! # A.e. differentiation of the actual interior Legendre potential

Near each interior target slope, uniform tilted coercivity makes the full
conjugate agree with one fixed finite-ball conjugate. These truncations are
finite convex functions on all of space. Their proved a.e. differentiation
therefore yields a.e. differentiation of the full conjugate on the target.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators Gradient
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

def truncatedConjugateValues (φ : E n → ℝ) (k : ℕ) (p : E n) : Set ℝ :=
  (fun x => inner ℝ p x - φ x) '' Metric.closedBall 0 ((k : ℝ) + 1)

def truncatedConjugate (φ : E n → ℝ) (k : ℕ) (p : E n) : ℝ :=
  sSup (truncatedConjugateValues φ k p)

lemma truncatedConjugateValues_nonempty (φ : E n → ℝ) (k : ℕ) (p : E n) :
    (truncatedConjugateValues φ k p).Nonempty :=
  ⟨-φ 0, 0, Metric.mem_closedBall_self (by positivity), by simp⟩

lemma truncatedConjugateValues_bddAbove {φ : E n → ℝ} (hφ : Continuous φ)
    (k : ℕ) (p : E n) : BddAbove (truncatedConjugateValues φ k p) :=
  ((isCompact_closedBall (0 : E n) ((k : ℝ) + 1)).image
    ((continuous_const.inner continuous_id).sub hφ)).bddAbove

lemma truncatedConjugate_fenchel_le {φ : E n → ℝ} (hφ : Continuous φ)
    (k : ℕ) (p : E n) {x : E n} (hx : ‖x‖ ≤ (k : ℝ) + 1) :
    inner ℝ p x - φ x ≤ truncatedConjugate φ k p :=
  le_csSup (truncatedConjugateValues_bddAbove hφ k p) ⟨x, by simpa using hx, rfl⟩

lemma truncatedConjugate_convex {φ : E n → ℝ} (hφ : Continuous φ) (k : ℕ) :
    ConvexOn ℝ univ (truncatedConjugate φ k) := by
  refine ⟨convex_univ, ?_⟩
  intro p _ q _ a b ha hb hab
  apply csSup_le (truncatedConjugateValues_nonempty φ k _)
  rintro _ ⟨x, hx, rfl⟩
  have hx' : ‖x‖ ≤ (k : ℝ) + 1 := by simpa using hx
  have hp := mul_le_mul_of_nonneg_left (truncatedConjugate_fenchel_le hφ k p hx') ha
  have hq := mul_le_mul_of_nonneg_left (truncatedConjugate_fenchel_le hφ k q hx') hb
  have hsum : a * φ x + b * φ x = φ x := by rw [← add_mul, hab, one_mul]
  simp only [inner_add_left, real_inner_smul_left, smul_eq_mul]
  nlinarith

/-- A local, uniform finite-source truncation is derived from tilted growth.
The radius is constructed and works for an entire target neighborhood. -/
theorem conjugate_locally_eq_truncated_of_growth {φ : E n → ℝ} (hφ : Continuous φ)
    {p : E n} {r B : ℝ} (hr : 0 < r)
    (hbound : ∀ y, r * ‖y‖ - B ≤ φ y - inner ℝ p y) :
    ∃ k : ℕ, ∀ᶠ q in 𝓝 p, conjugate φ q = truncatedConjugate φ k q := by
  obtain ⟨k, hk⟩ := exists_nat_gt (2 * (B + |φ 0| + 1) / r)
  have hk' : 2 * (B + |φ 0| + 1) < (k : ℝ) * r := (div_lt_iff₀ hr).mp hk
  refine ⟨k, Filter.mem_of_superset (Metric.ball_mem_nhds p (half_pos hr)) ?_⟩
  intro q hq
  have hq' : ‖q - p‖ < r / 2 := by simpa [Metric.mem_ball, dist_eq_norm] using hq
  have hzero : -φ 0 ≤ truncatedConjugate φ k q := by
    simpa using truncatedConjugate_fenchel_le hφ k q (x := 0) (by simp; positivity)
  have hup : ∀ y, inner ℝ q y - φ y ≤ truncatedConjugate φ k q := by
    intro y
    by_cases hy : ‖y‖ ≤ (k : ℝ) + 1
    · exact truncatedConjugate_fenchel_le hφ k q hy
    · have hy' : (k : ℝ) + 1 < ‖y‖ := lt_of_not_ge hy
      have hi := real_inner_le_norm (q - p) y
      rw [inner_sub_left] at hi
      have hb := hbound y
      have hqn := mul_le_mul_of_nonneg_right hq'.le (norm_nonneg y)
      have hrn := mul_lt_mul_of_pos_left hy' hr
      have hv : inner ℝ q y - φ y ≤ -φ 0 := by
        nlinarith [le_abs_self (φ 0)]
      exact hv.trans hzero
  have hbdd : BddAbove (conjugateValues φ q) := by
    refine ⟨truncatedConjugate φ k q, ?_⟩
    rintro _ ⟨y, rfl⟩
    exact hup y
  apply le_antisymm
  · exact csSup_le (conjugateValues_nonempty φ q) (by rintro _ ⟨y, rfl⟩; exact hup y)
  · apply csSup_le (truncatedConjugateValues_nonempty φ k q)
    rintro _ ⟨y, _, rfl⟩
    exact conjugate_fenchel_le hbdd y

/-- The full conjugate is a.e. differentiable on the actual open target.
This uses countably many globally finite convex truncations, avoiding any
unproved local Rademacher or Monge--Ampère regularity theorem. -/
theorem conjugate_ae_differentiable_on_target {φ V : E n → ℝ}
    (hφ : Continuous φ) (hc : ConvexOn ℝ univ φ) {K : Set (E n)}
    (hK : IsOpen K) (hV : ContinuousOn V K)
    (hmap : (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x)))).map
      (gradient φ) = volume.withDensity (fun x => ENNReal.ofReal
        (K.indicator (fun y => Real.exp (-V y)) x))) :
    ∀ᵐ p ∂volume, p ∈ K → DifferentiableAt ℝ (conjugate φ) p := by
  have htrunc : ∀ᵐ p ∂volume, ∀ k : ℕ, DifferentiableAt ℝ (truncatedConjugate φ k) p :=
    ae_all_iff.mpr (fun k => MomentMapCoercivity.convex_ae_differentiable
      (truncatedConjugate_convex hφ k))
  filter_upwards [htrunc] with p hp hpK
  have hg : Measurable (gradient φ) :=
    (InnerProductSpace.toDual ℝ (E n)).symm.continuous.measurable.comp (measurable_fderiv ℝ φ)
  obtain ⟨r, B, hr, _, hb⟩ := tilted_linear_lower_bound_of_gradient_transport hc hK hg.aemeasurable
    ((withDensity_absolutelyContinuous volume _).ae_le
      (MomentMapCoercivity.convex_ae_differentiable hc)) hmap
    (fun q hq ε hε => target_ball_pos hK hV hq hε) hpK
  obtain ⟨k, heq⟩ := conjugate_locally_eq_truncated_of_growth hφ hr hb
  exact (hp k).congr_of_eventuallyEq heq

lemma supporting_vector_eq_gradient_of_eventually {φ : E n → ℝ} {p x : E n}
    (hd : DifferentiableAt ℝ φ x)
    (hs : ∀ᶠ y in 𝓝 x, φ x + inner ℝ p (y - x) ≤ φ y) : gradient φ x = p := by
  let F : E n → ℝ := fun y => φ y - inner ℝ p y
  have hmin : IsLocalMin F x := by
    filter_upwards [hs] with y hy
    change φ x - inner ℝ p x ≤ φ y - inner ℝ p y
    rw [inner_sub_right] at hy
    linarith
  have hdF : HasFDerivAt F ((InnerProductSpace.toDual ℝ (E n)) (gradient φ x) -
      innerSL ℝ p) x := hd.hasGradientAt.hasFDerivAt.sub (innerSL ℝ p).hasFDerivAt
  have hz : (InnerProductSpace.toDual ℝ (E n)) (gradient φ x) = innerSL ℝ p := by
    apply sub_eq_zero.mp
    rw [← hdF.fderiv]
    exact hmin.fderiv_eq_zero
  exact (InnerProductSpace.toDual ℝ (E n)).injective hz

/-- Actual Fenchel equality identifies the inverse gradient wherever the
interior conjugate is differentiable. No inverse transport map is assumed. -/
theorem conjugate_gradient_eq_of_support {φ : E n → ℝ} {K : Set (E n)}
    (hK : IsOpen K) (hfinite : ∀ q ∈ K, BddAbove (conjugateValues φ q))
    {p x : E n} (hp : p ∈ K) (hd : DifferentiableAt ℝ (conjugate φ) p)
    (hs : ∀ y, φ x + inner ℝ p (y - x) ≤ φ y) : gradient (conjugate φ) p = x := by
  apply supporting_vector_eq_gradient_of_eventually hd
  filter_upwards [hK.mem_nhds hp] with q hq
  have heq := conjugate_eq_of_support hs
  have hq' := conjugate_fenchel_le (hfinite q hq) x
  rw [heq, inner_sub_right]
  linarith [real_inner_comm x q, real_inner_comm x p]

lemma target_ae_mem {K : Set (E n)} (hK : IsOpen K) {V : E n → ℝ}
    (hV : ContinuousOn V K) :
    ∀ᵐ p ∂volume.withDensity (fun x => ENNReal.ofReal
      (K.indicator (fun y => Real.exp (-V y)) x)), p ∈ K := by
  classical
  have hm : Measurable (K.indicator (fun y => Real.exp (-V y))) :=
    (Real.continuous_exp.comp_continuousOn hV.neg).measurable_piecewise
      continuousOn_const hK.measurableSet
  apply (ae_withDensity_iff (ENNReal.measurable_ofReal.comp hm)).mpr
  apply ae_of_all
  intro p hp
  by_contra hpK
  exact hp (by simp [hpK])

/-- Almost every target point has exactly one source contact point. This is
proved from a.e. differentiation of the constructed conjugate and is the
measure-theoretic prerequisite for identifying its Alexandrov measure. -/
theorem ae_unique_source_support {φ V : E n → ℝ}
    (hφ : Continuous φ) (hc : ConvexOn ℝ univ φ) {K : Set (E n)}
    (hK : IsOpen K) (hKc : Convex ℝ K) (hV : ContinuousOn V K)
    (hmap : (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x)))).map
      (gradient φ) = volume.withDensity (fun x => ENNReal.ofReal
        (K.indicator (fun y => Real.exp (-V y)) x))) :
    ∀ᵐ p ∂volume.withDensity (fun x => ENNReal.ofReal
      (K.indicator (fun y => Real.exp (-V y)) x)),
      ∀ x y : E n,
        (∀ z, φ x + inner ℝ p (z - x) ≤ φ z) →
        (∀ z, φ y + inner ℝ p (z - y) ≤ φ z) → x = y := by
  have hfinite := (conjugate_regular_on_target hφ hc hK hKc hV hmap).1
  have hd := (withDensity_absolutelyContinuous volume (fun x => ENNReal.ofReal
    (K.indicator (fun y => Real.exp (-V y)) x))).ae_le
      (conjugate_ae_differentiable_on_target hφ hc hK hV hmap)
  filter_upwards [hd, target_ae_mem hK hV] with p hdp hp x y hx hy
  exact (conjugate_gradient_eq_of_support hK hfinite hp (hdp hp) hx).symm.trans
    (conjugate_gradient_eq_of_support hK hfinite hp (hdp hp) hy)

/-- The two actual gradients are inverse at almost every source point. -/
theorem ae_conjugate_gradient_left_inverse {φ V : E n → ℝ}
    (hφ : Continuous φ) (hc : ConvexOn ℝ univ φ) {K : Set (E n)}
    (hK : IsOpen K) (hKc : Convex ℝ K) (hV : ContinuousOn V K)
    (hmap : (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x)))).map
      (gradient φ) = volume.withDensity (fun x => ENNReal.ofReal
        (K.indicator (fun y => Real.exp (-V y)) x))) :
    ∀ᵐ x ∂volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x))),
      gradient (conjugate φ) (gradient φ x) = x := by
  have hfinite := (conjugate_regular_on_target hφ hc hK hKc hV hmap).1
  have hg : Measurable (gradient φ) :=
    (InnerProductSpace.toDual ℝ (E n)).symm.continuous.measurable.comp (measurable_fderiv ℝ φ)
  have hd := (withDensity_absolutelyContinuous volume (fun x => ENNReal.ofReal
    (K.indicator (fun y => Real.exp (-V y)) x))).ae_le
      (conjugate_ae_differentiable_on_target hφ hc hK hV hmap)
  have ht := Filter.Eventually.and hd (target_ae_mem hK hV)
  rw [← hmap] at ht
  have hpull := ae_of_ae_map hg.aemeasurable ht
  have hs := (withDensity_absolutelyContinuous volume (fun x => ENNReal.ofReal
    (Real.exp (-φ x)))).ae_le (MomentMapCoercivity.convex_ae_differentiable hc)
  filter_upwards [hpull, hs] with x hx hdx
  exact conjugate_gradient_eq_of_support hK hfinite hx.2 (hx.1 hx.2)
    (convex_gradient_support hc hdx)

/-- The gradient of the constructed conjugate genuinely transports the
whole target law back to the original exponential source law. -/
theorem conjugate_gradient_transport {φ V : E n → ℝ}
    (hφ : Continuous φ) (hc : ConvexOn ℝ univ φ) {K : Set (E n)}
    (hK : IsOpen K) (hKc : Convex ℝ K) (hV : ContinuousOn V K)
    (hmap : (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x)))).map
      (gradient φ) = volume.withDensity (fun x => ENNReal.ofReal
        (K.indicator (fun y => Real.exp (-V y)) x))) :
    (volume.withDensity (fun x => ENNReal.ofReal
      (K.indicator (fun y => Real.exp (-V y)) x))).map (gradient (conjugate φ)) =
      volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x))) := by
  have hg (f : E n → ℝ) : Measurable (gradient f) :=
    (InnerProductSpace.toDual ℝ (E n)).symm.continuous.measurable.comp (measurable_fderiv ℝ f)
  rw [← hmap, Measure.map_map (hg (conjugate φ)) (hg φ)]
  exact (Measure.map_congr
    (ae_conjugate_gradient_left_inverse hφ hc hK hKc hV hmap)).trans Measure.map_id

end GaussianTilt.MomentMapRegularity
