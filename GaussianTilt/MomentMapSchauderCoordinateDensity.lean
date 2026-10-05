import GaussianTilt.MomentMapSchauderLocalSmoothDensity

/-! # Direct raw-coordinate smooth-density bootstrap for intrinsic jets -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1800000
open Set
open scoped ContDiff
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapRegularity GaussianTilt.Letwin
variable {n : ℕ}

lemma norm_coordinateEquiv_le (x : KernelSpace n) : ‖coordinateEquiv n x‖ ≤ ‖x‖ := by
  exact (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr (fun i => PiLp.norm_apply_le x i)

/-- Direct CoordinateSpace-domain endpoint. Entrywise first C²,α data are
converted to the genuine Euclidean bilinear norm, the local bootstrap is
proved there, and the resulting smoothness is transported back. -/
theorem coordinate_positive_density_contDiffOn_infty [NeZero n]
    {φ ρ : CoordinateSpace n → ℝ} {U : Set (CoordinateSpace n)} (hU : IsOpen U)
    (hφ : ContDiffOn ℝ 2 φ U) (hρ : ContDiffOn ℝ ∞ ρ U) (hρpos : ∀ x ∈ U, 0 < ρ x)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hpos : ∀ x ∈ U, (coordinateHessian φ x).PosDef)
    (hMA : ∀ x ∈ U, (coordinateHessian φ x).det=ρ x)
    (hloc : ∀ a ∈ U, ∃ R H : ℝ, 0 < R ∧ 0 ≤ H ∧ Metric.closedBall a R ⊆ U ∧
      ∀ x ∈ Metric.closedBall a R, ∀ y ∈ Metric.closedBall a R, ∀ i j,
        |coordinateHessian φ x i j-coordinateHessian φ y i j| ≤ H*‖x-y‖^α) :
    ContDiffOn ℝ ∞ φ U := by
  let c := coordinateEquiv n
  let v : KernelSpace n → ℝ := φ ∘ c
  let ρv : KernelSpace n → ℝ := ρ ∘ c
  let V := c ⁻¹' U
  have hV : IsOpen V := hU.preimage c.continuous
  have hcv : MapsTo c V U := fun x hx => hx
  have hv : ContDiffOn ℝ 2 v V := hφ.comp c.contDiff.contDiffOn hcv
  have hρv : ContDiffOn ℝ ∞ ρv V := hρ.comp c.contDiff.contDiffOn hcv
  have hraw : coordinatePullback v=φ := by
    funext x
    exact congrArg φ (c.apply_symm_apply x)
  have hP : ∀ x ∈ V, (coordinateHessian (coordinatePullback v) (coordinateEquiv n x)).PosDef := by
    intro x hx
    rw [hraw]
    exact hpos (c x) hx
  have hE : ∀ x ∈ V, (coordinateHessian (coordinatePullback v) (coordinateEquiv n x)).det=ρv x := by
    intro x hx
    rw [hraw]
    exact hMA (c x) hx
  have hlocal : ∀ a ∈ V, ∃ R H : ℝ, 0 < R ∧ 0 ≤ H ∧ Metric.closedBall a R ⊆ V ∧
      ∀ x ∈ Metric.closedBall a R, ∀ y ∈ Metric.closedBall a R,
        ‖fderiv ℝ (fderiv ℝ v) x-fderiv ℝ (fderiv ℝ v) y‖ ≤ H*‖x-y‖^α := by
    intro a ha
    obtain ⟨R, H, hR, hH, hsub, hh⟩ := hloc (c a) ha
    have hball : ∀ x ∈ Metric.closedBall a R, c x ∈ Metric.closedBall (c a) R := by
      intro x hx
      rw [Metric.mem_closedBall, dist_eq_norm, ← map_sub]
      exact (norm_coordinateEquiv_le (x-a)).trans (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx)
    have hballV : Metric.closedBall a R ⊆ V := fun x hx => hsub (hball x hx)
    refine ⟨R, (n : ℝ)^2*H, hR, by positivity, hballV, ?_⟩
    intro x hx y hy
    have he (z : KernelSpace n) (hz : z ∈ V) :
        coordinateHessian φ (c z)=euclideanHessianMatrix v z := by
      rw [← hraw]
      exact coordinateHessian_pullback_eq_euclidean_at (hv.contDiffAt (hV.mem_nhds hz))
    have hn : ‖c x-c y‖ ≤ ‖x-y‖ := by rw [← map_sub]; exact norm_coordinateEquiv_le _
    have hb := euclidean_bilinear_norm_le_of_entries
      (fderiv ℝ (fderiv ℝ v) x-fderiv ℝ (fderiv ℝ v) y)
      (M := H*‖x-y‖^α) (by positivity) ?_
    · exact hb.trans_eq (by ring)
    · intro i j
      have hh' := (hh (c x) (hball x hx) (c y) (hball y hy) i j).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hn hα.le) hH)
      rw [he x (hballV hx), he y (hballV hy)] at hh'
      exact hh'
  have hs := local_positive_density_contDiffOn_infty hV hv hρv
    (fun x hx => hρpos (c x) hx) hα hα1 hP hE hlocal
  have hback : ContDiffOn ℝ ∞ (v ∘ c.symm) U := hs.comp c.symm.contDiff.contDiffOn (fun x hx => by
    change c (c.symm x) ∈ U
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hx)
  have he : v ∘ c.symm=φ := by
    funext x
    exact congrArg φ (c.apply_symm_apply x)
  rw [he] at hback
  exact hback

/-- Uniform stored Hessian-entry Hölder bounds on the intrinsic body
immediately provide the local hypotheses needed by the raw-coordinate
interior-smoothness endpoint. -/
theorem coordinate_positive_density_contDiffOn_infty_of_holder_entries [NeZero n]
    {φ ρ : CoordinateSpace n → ℝ} {U : Set (CoordinateSpace n)} (hU : IsOpen U)
    (hφ : ContDiffOn ℝ 2 φ U) (hρ : ContDiffOn ℝ ∞ ρ U) (hρpos : ∀ x ∈ U, 0 < ρ x)
    {α H : ℝ} (hα : 0 < α) (hα1 : α < 1) (hH : 0 ≤ H)
    (hpos : ∀ x ∈ U, (coordinateHessian φ x).PosDef)
    (hMA : ∀ x ∈ U, (coordinateHessian φ x).det=ρ x)
    (hh : ∀ x ∈ U, ∀ y ∈ U, ∀ i j,
      |coordinateHessian φ x i j-coordinateHessian φ y i j| ≤ H*‖x-y‖^α) :
    ContDiffOn ℝ ∞ φ U := by
  apply coordinate_positive_density_contDiffOn_infty hU hφ hρ hρpos hα hα1 hpos hMA
  intro a ha
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds ha)
  have hsub : Metric.closedBall a (r/2) ⊆ U := (Metric.closedBall_subset_ball (by linarith)).trans hball
  exact ⟨r/2, H, by positivity, hH, hsub, fun x hx y hy => hh x (hsub hx) y (hsub hy)⟩

end GaussianTilt.MomentMapSchauder
