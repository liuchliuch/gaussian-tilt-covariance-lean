import GaussianTilt.MomentMapSchauderCompactHolder
import GaussianTilt.MomentMapSchauderCutoffForcing
import GaussianTilt.MomentMapSchauderCutoffHolder

/-! # C²-only interior constant-coefficient Schauder regularity

Unlike the variable-coefficient a-priori theorem, this endpoint needs no
initial Hessian Hölder bound. The actual compact-support Poisson estimate
and explicitly controlled cutoff forcing produce that regularity.
-/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1600000
open Matrix Set
open scoped ContDiff BigOperators Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

theorem exists_constant_interior_holder_of_C2 [NeZero n]
    {u : KernelSpace n → ℝ} (hu : ContDiff ℝ 2 u)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (a : KernelSpace n) {R H α : ℝ} (hR : 0 < R) (hH : 0 ≤ H)
    (hα : 0 < α) (hα1 : α < 1)
    (hforceH : ∀ x ∈ Metric.closedBall a R, ∀ y ∈ Metric.closedBall a R,
      |euclideanEllipticOperator A u x-euclideanEllipticOperator A u y| ≤ H*‖x-y‖^α) :
    ∃ C : ℝ, 0 < C ∧
      (∀ x ∈ Metric.ball a (R/2), ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ C) ∧
      (∀ x ∈ Metric.ball a (R/2), ∀ y ∈ Metric.ball a (R/2),
        ‖fderiv ℝ (fderiv ℝ u) x-fderiv ℝ (fderiv ℝ u) y‖ ≤ C*‖x-y‖^α) := by
  let S := Metric.closedBall a R
  have hS : IsCompact S := isCompact_closedBall _ _
  have hSc : Convex ℝ S := convex_closedBall _ _
  have hDu : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  obtain ⟨U, hU, hub, huH⟩ := exists_contDiff_holder_bound_on_compact_convex
    (hu.of_le (by norm_num) : ContDiff ℝ 1 u) hS hSc hα.le hα1.le
  obtain ⟨D, hD, hDb, hDH⟩ := exists_contDiff_holder_bound_on_compact_convex hDu hS hSc hα.le hα1.le
  obtain ⟨j, hj⟩ := hS.exists_bound_of_continuousOn
    (hDu.fderiv_right (m := 0) (by norm_num)).continuous.continuousOn
  let J := max j 1
  have hJ : 0 ≤ J := (show (0 : ℝ) ≤ 1 by norm_num).trans (le_max_right _ _)
  have hJb : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ J := fun x hx => (hj x hx).trans (le_max_left _ _)
  let M := ‖A‖
  have hM : 0 ≤ M := norm_nonneg A
  have hAb : ∀ x : KernelSpace n, ∀ i j, |A i j| ≤ M := fun _ i j => by
    simpa only [Real.norm_eq_abs] using Matrix.norm_entry_le_entrywise_sup_norm A (i := i) (j := j)
  have hAs : A.IsSymm := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hA.isHermitian
  let F := (n : ℝ)^2*M*J
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hfb : ∀ x ∈ S, |euclideanEllipticOperator A u x| ≤ F := by
    intro x hx
    have hh := abs_matrixContraction_le hM hJ (hAb x)
      (fun i j => (abs_euclidean_bilinear_entry_le_norm _ i j).trans (hJb x hx))
    simpa only [Fintype.card_fin] using hh
  obtain ⟨B₁, B₂, B₃, hB₁, hB₂, hB₃, hcut⟩ :=
    exists_scaled_cutoff_jet_holder_bounds (E := KernelSpace n) hα.le hα1.le
  let r := R/2
  have hr : 0 < r := by dsimp [r]; positivity
  let χ := scaledInteriorCutoff a r
  have hχ : ContDiff ℝ 2 χ := contDiff_infty.mp (scaledInteriorCutoff_contDiff a r) 2
  have hs : tsupport χ ⊆ S := by
    have he : 2*r=R := by dsimp [r]; ring
    simpa only [he] using tsupport_scaledInteriorCutoff_subset a hr
  have hχb : ∀ x, |χ x| ≤ 1 := fun x => by
    rw [abs_of_nonneg (scaledInteriorCutoff_nonneg a x r)]
    exact scaledInteriorCutoff_le_one a x r
  let C₁ := B₁/r
  let C₂ := B₂/r^2
  let L₀ := (B₁+2)*r^(-α)
  let L₁ := (B₂+2*B₁)*r^(-1-α)
  let L₂ := (B₃+2*B₂)*r^(-2-α)
  have hC₁ : 0 ≤ C₁ := by dsimp [C₁]; positivity
  have hC₂ : 0 ≤ C₂ := by dsimp [C₂]; positivity
  have hL₀ : 0 ≤ L₀ := by dsimp [L₀]; positivity
  have hL₁ : 0 ≤ L₁ := by dsimp [L₁]; positivity
  have hL₂ : 0 ≤ L₂ := by dsimp [L₂]; positivity
  have hcut' := hcut a r hr
  have hub' : ∀ x ∈ S, |u x| ≤ U := by simpa only [Real.norm_eq_abs] using hub
  have huH' : ∀ x ∈ S, ∀ y ∈ S, |u x-u y| ≤ U*‖x-y‖^α := by simpa only [Real.norm_eq_abs] using huH
  have hrem := euclideanCutoffRemainder_bounds hC₁ hC₂ hL₁ hL₂ hU.le hD.le hU.le hD.le
    hs hcut'.1 hcut'.2.1 hcut'.2.2.2.1 hcut'.2.2.2.2 hub' hDb huH' hDH
  have hforcing := euclidean_cutoff_forcing_bounds hu hχ hM (le_refl (0 : ℝ)) zero_le_one hL₀ hF hH
    (by positivity) (by positivity) (fun _ => hAs) hs hAb
    (fun x y i j => by simp) hχb hcut'.2.2.1 hfb hforceH (fun _ _ => rfl) hrem.1 hrem.2
  obtain ⟨lam, Λ, hlam, hΛ, hell⟩ := exists_uniform_ellipticity_on_compact
    (H := fun _ : KernelSpace n => A) hS continuous_const.continuousOn (fun _ _ => hA)
  have haS : a ∈ S := Metric.mem_closedBall_self hR.le
  obtain ⟨C₀, hC₀, hbase⟩ := exists_compact_constant_elliptic_schauder (n := n) hα hα1 hlam hΛ.le
  have hvb : ∀ x, |χ x*u x| ≤ U := by
    intro x
    by_cases hx : x ∈ S
    · rw [abs_mul]
      exact (mul_le_mul (hχb x) (hub' x hx) (abs_nonneg _) zero_le_one).trans_eq (one_mul U)
    · rw [(cutoff_jets_zero_off hs hx).1, zero_mul, abs_zero]; exact hU.le
  let Fv := 1*F+(n : ℝ)^2*M*(C₂*U+2*(C₁*D))
  let Hv := 1*H+F*L₀+(n : ℝ)^2*(M*(C₂*U+U*L₂+2*(C₁*D+D*L₁))+0*(C₂*U+2*(C₁*D)))
  have hFv : 0 ≤ Fv := by dsimp [Fv]; positivity
  have hHv : 0 ≤ Hv := by dsimp [Hv]; positivity
  have hb := hbase A hA (fun v => (hell a haS v).1) (fun v => (hell a haS v).2)
    (fun x => χ x*u x) (hχ.mul hu) (scaledInteriorCutoff_compact a hr).mul_right U Fv Hv
    hU.le hFv hHv hvb hforcing.1 hforcing.2
  let C := C₀*(U+Fv+Hv)+1
  have hC : 0 < C := by dsimp [C]; positivity
  have hle : C₀*(U+Fv+Hv) ≤ C := by dsimp [C]; linarith
  have hone : ∀ x ∈ Metric.ball a r, χ x=1 := fun x hx =>
    scaledInteriorCutoff_one hr (Metric.mem_closedBall.mp (Metric.ball_subset_closedBall hx))
  refine ⟨C, hC, ?_, ?_⟩
  · intro x hx
    have he := (cutoff_mul_derivatives_eq (u := u) Metric.isOpen_ball hone hx).2.2
    exact (he ▸ hb.1 x).trans hle
  · intro x hx y hy
    have he := (cutoff_mul_derivatives_eq (u := u) Metric.isOpen_ball hone hx).2.2
    have he' := (cutoff_mul_derivatives_eq (u := u) Metric.isOpen_ball hone hy).2.2
    exact (he ▸ he' ▸ hb.2 x y).trans (mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg (norm_nonneg _) α))

lemma euclideanEllipticOperator_one_eq_laplacian {u : KernelSpace n → ℝ}
    (hu : ContDiff ℝ 2 u) (x : KernelSpace n) :
    euclideanEllipticOperator 1 u x=kernelLaplacian u x := by
  simp only [euclideanEllipticOperator, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, kernelLaplacian, directionalHessian_eq_secondFrechet hu]

/-- Light Poisson interface for C² representatives obtained from weak
Dirichlet solutions. The Hessian Hölder modulus is a conclusion. -/
theorem exists_poisson_interior_holder_of_C2 [NeZero n]
    {u : KernelSpace n → ℝ} (hu : ContDiff ℝ 2 u) (a : KernelSpace n)
    {R H α : ℝ} (hR : 0 < R) (hH : 0 ≤ H) (hα : 0 < α) (hα1 : α < 1)
    (hforceH : ∀ x ∈ Metric.closedBall a R, ∀ y ∈ Metric.closedBall a R,
      |kernelLaplacian u x-kernelLaplacian u y| ≤ H*‖x-y‖^α) :
    ∃ C : ℝ, 0 < C ∧ (∀ x ∈ Metric.ball a (R/2), ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ C) ∧
      (∀ x ∈ Metric.ball a (R/2), ∀ y ∈ Metric.ball a (R/2),
        ‖fderiv ℝ (fderiv ℝ u) x-fderiv ℝ (fderiv ℝ u) y‖ ≤ C*‖x-y‖^α) := by
  apply exists_constant_interior_holder_of_C2 hu Matrix.PosDef.one a hR hH hα hα1
  simpa only [euclideanEllipticOperator_one_eq_laplacian hu] using hforceH

end GaussianTilt.MomentMapSchauder
