import GaussianTilt.MomentMapSchauderLinearCoefficientBounds
import GaussianTilt.MomentMapSchauderSourceUniform

/-! # Step-uniform estimates for differentiated linear equations

The actual coefficient-increment forcing is derived and bounded. These
estimates support repeated source bootstrap, with no assumed linear
regularity gain or Dirichlet inverse.
-/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1800000
open Matrix Set
open scoped ContDiff
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

theorem exists_uniform_linear_difference_schauder [NeZero n]
    {φ g : KernelSpace n → ℝ} (hφ : ContDiff ℝ 2 φ) (hg : ContDiff ℝ 1 g)
    {A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, ContDiff ℝ 1 (fun x => A x i j))
    (a : KernelSpace n) {R Hφ Hg HA α : ℝ} (hR : 0 < R)
    (hHφ : 0 ≤ Hφ) (hHg : 0 ≤ Hg) (hHA : 0 ≤ HA) (hα : 0 < α) (hα1 : α < 1)
    (hpos : ∀ x ∈ Metric.closedBall a (2*R), (A x).PosDef)
    (heq : ∀ x ∈ Metric.closedBall a (2*R), euclideanEllipticOperator (A x) φ x=g x)
    (hAH : ∀ x ∈ Metric.closedBall a (2*R), ∀ y ∈ Metric.closedBall a (2*R), ∀ i j,
      ‖fderiv ℝ (fun z => A z i j) x-fderiv ℝ (fun z => A z i j) y‖ ≤ HA*‖x-y‖^α)
    (hφH : ∀ x ∈ Metric.closedBall a (2*R), ∀ y ∈ Metric.closedBall a (2*R),
      ‖fderiv ℝ (fderiv ℝ φ) x-fderiv ℝ (fderiv ℝ φ) y‖ ≤ Hφ*‖x-y‖^α)
    (hgH : ∀ x ∈ Metric.closedBall a (2*R), ∀ y ∈ Metric.closedBall a (2*R),
      ‖fderiv ℝ g x-fderiv ℝ g y‖ ≤ Hg*‖x-y‖^α) :
    ∃ r C : ℝ, 0 < r ∧ r ≤ R ∧ 0 < C ∧
      ∀ e : KernelSpace n, ‖e‖ ≤ 1 → ∀ s : ℝ, s ≠ 0 → |s| ≤ R →
      (∀ x ∈ Metric.ball a r,
        ‖fderiv ℝ (fderiv ℝ (vectorDifferenceQuotient φ (s • e) s)) x‖ ≤ C) ∧
      (∀ x ∈ Metric.ball a r, ∀ y ∈ Metric.ball a r,
        ‖fderiv ℝ (fderiv ℝ (vectorDifferenceQuotient φ (s • e) s)) x-
          fderiv ℝ (fderiv ℝ (vectorDifferenceQuotient φ (s • e) s)) y‖ ≤ C*‖x-y‖^α) := by
  let S := Metric.closedBall a (2*R)
  have hS : IsCompact S := isCompact_closedBall _ _
  have hφ₁ : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hDφ : ContDiff ℝ 1 (fderiv ℝ φ) := hφ.fderiv_right (by norm_num)
  have hD2c : Continuous (fderiv ℝ (fderiv ℝ φ)) := (hDφ.fderiv_right (m := 0) (by norm_num)).continuous
  obtain ⟨m₁, hm₁⟩ := hS.exists_bound_of_continuousOn hDφ.continuous.continuousOn
  obtain ⟨m₂, hm₂⟩ := hS.exists_bound_of_continuousOn hD2c.continuousOn
  obtain ⟨mg, hmg⟩ := hS.exists_bound_of_continuousOn
    (hg.fderiv_right (m := 0) (by norm_num)).continuous.continuousOn
  let M₁ := max m₁ 1
  let M₂ := max m₂ 1
  let G := max mg 1
  have hM₁ : 0 < M₁ := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hM₂ : 0 < M₂ := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hG : 0 < G := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hb₁ : ∀ x ∈ S, ‖fderiv ℝ φ x‖ ≤ M₁ := fun x hx => (hm₁ x hx).trans (le_max_left _ _)
  have hb₂ : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ φ) x‖ ≤ M₂ := fun x hx => (hm₂ x hx).trans (le_max_left _ _)
  have hbg : ∀ x ∈ S, ‖fderiv ℝ g x‖ ≤ G := fun x hx => (hmg x hx).trans (le_max_left _ _)
  have hLip : ∀ x ∈ S, ∀ y ∈ S, ‖fderiv ℝ φ x-fderiv ℝ φ y‖ ≤ M₂*‖x-y‖ := by
    intro x hx y hy
    exact Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hDφ.differentiable le_rfl z) hb₂ (convex_closedBall a (2*R)) hy hx
  have hfirstH : ∀ x ∈ S, ∀ y ∈ S,
      ‖fderiv ℝ φ x-fderiv ℝ φ y‖ ≤ (M₂+2*M₁)*‖x-y‖^α := by
    simpa only [Real.one_rpow, mul_one] using holder_bound_of_sup_and_lipschitz
      hM₁.le hM₂.le hα.le hα1.le zero_lt_one hb₁ hLip
  obtain ⟨M, DA, K, hM, hDA, hK, hAb, hDAb, hAH₀⟩ :=
    exists_C1_matrix_bounds_on_compact_convex hA hS (convex_closedBall a (2*R)) hα.le hα1.le
  obtain ⟨lam, Λ, hlam, hΛ, hell⟩ := exists_uniform_ellipticity_on_compact hS
    (continuous_matrix_of_contDiff_entries hA).continuousOn hpos
  obtain ⟨r, C₀, hr, hrR, hC₀, hbase⟩ :=
    exists_interior_first_jet_schauder (n := n) hα hα1 hlam hΛ.le hK.le hM.le hR
  let C := C₀*(M₁+M₂+(M₂+2*M₁)+Hφ+(G+(n : ℝ)^2*DA*M₂)+(Hg+(n : ℝ)^2*(DA*Hφ+HA*M₂)))
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨r, C, hr, by linarith, hC, ?_⟩
  intro e he s hs hsR
  have hseg : ∀ x ∈ Metric.closedBall a R, ∀ t ∈ Icc (0 : ℝ) 1, x+t • (s • e) ∈ S :=
    fun x hx t ht => segment_mem_double_closedBall hR.le hx he hsR ht
  have hsub : Metric.closedBall a R ⊆ S := Metric.closedBall_subset_closedBall (by linarith)
  have hshift : ∀ x ∈ Metric.closedBall a R, x+s • e ∈ S := fun x hx => by
    simpa only [one_smul] using hseg x hx 1 ⟨by norm_num, le_rfl⟩
  have haR : a ∈ Metric.closedBall a R := Metric.mem_closedBall_self hR.le
  have hc := hell (a+s • e) (hshift a haR)
  have hsym : ∀ x ∈ Metric.closedBall a R, (A (x+s • e)).IsSymm := by
    intro x hx
    have hh := (hpos _ (hshift x hx)).isHermitian
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hh
  have hcoefH : ∀ x ∈ Metric.closedBall a R, ∀ y ∈ Metric.closedBall a R, ∀ i j,
      |A (x+s • e) i j-A (y+s • e) i j| ≤ K*‖x-y‖^α := by
    intro x hx y hy i j
    have heq : (x+s • e)-(y+s • e)=x-y := by abel
    simpa only [heq] using hAH₀ _ (hshift x hx) _ (hshift y hy) i j
  have hfirst := differenceQuotient_first_jet_bounds hφ hb₁ hb₂ hfirstH hφH e hs hseg
  have hqb : ∀ x ∈ Metric.closedBall a R, |vectorDifferenceQuotient φ (s • e) s x| ≤ M₁ :=
    fun x hx => (hfirst.1 x hx).trans (mul_le_of_le_one_right hM₁.le he)
  have hqDb : ∀ x ∈ Metric.closedBall a R, ‖fderiv ℝ (vectorDifferenceQuotient φ (s • e) s) x‖ ≤ M₂ :=
    fun x hx => (hfirst.2.1 x hx).trans (mul_le_of_le_one_right hM₂.le he)
  have hqH : ∀ x ∈ Metric.closedBall a R, ∀ y ∈ Metric.closedBall a R,
      |vectorDifferenceQuotient φ (s • e) s x-vectorDifferenceQuotient φ (s • e) s y| ≤ (M₂+2*M₁)*‖x-y‖^α := by
    intro x hx y hy
    exact (hfirst.2.2.1 x hx y hy).trans (mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_right (by positivity) he) (Real.rpow_nonneg (norm_nonneg _) α))
  have hqDH : ∀ x ∈ Metric.closedBall a R, ∀ y ∈ Metric.closedBall a R,
      ‖fderiv ℝ (vectorDifferenceQuotient φ (s • e) s) x-fderiv ℝ (vectorDifferenceQuotient φ (s • e) s) y‖ ≤ Hφ*‖x-y‖^α := by
    intro x hx y hy
    exact (hfirst.2.2.2 x hx y hy).trans (mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_right hHφ he) (Real.rpow_nonneg (norm_nonneg _) α))
  have hgqb : ∀ x ∈ Metric.closedBall a R, |vectorDifferenceQuotient g (s • e) s x| ≤ G := by
    intro x hx
    have hh := norm_vectorDifferenceQuotient_le hg x e hs (fun t ht => hbg _ (hseg x hx t ht))
    rw [Real.norm_eq_abs] at hh
    exact hh.trans (mul_le_of_le_one_right hG.le he)
  have hgqH : ∀ x ∈ Metric.closedBall a R, ∀ y ∈ Metric.closedBall a R,
      |vectorDifferenceQuotient g (s • e) s x-vectorDifferenceQuotient g (s • e) s y| ≤ Hg*‖x-y‖^α := by
    intro x hx y hy
    have hh := vectorDifferenceQuotient_holder_bound hg hgH x y e hs (hseg x hx) (hseg y hy)
    rw [Real.norm_eq_abs] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hHg he)
      (Real.rpow_nonneg (norm_nonneg _) α))
  have hAdiff := matrixDifferenceQuotient_bounds hA hDA.le hHA hDAb hAH e he hs hseg
  have hforce := linearDifferenceForcing_bounds hDA.le hHA hM₂.le hHφ hG.le hHg (s • e) s
    hAdiff.1 hAdiff.2 (fun x hx => hb₂ x (hsub hx))
    (fun x hx y hy => hφH x (hsub hx) y (hsub hy)) hgqb hgqH
  exact hbase a (fun x => A (x+s • e)) (hpos _ (hshift a haR))
    (fun v => (hc v).1) (fun v => (hc v).2) (hAb _ (hshift a haR)) hsym hcoefH
    (vectorDifferenceQuotient φ (s • e) s) (linearDifferenceForcing A φ g (s • e) s)
    (contDiff_vectorDifferenceQuotient hφ _ _) M₁ M₂ (2*|s⁻¹| * M₂) (M₂+2*M₁) Hφ (2*|s⁻¹| * Hφ)
    (G+(n : ℝ)^2*DA*M₂) (Hg+(n : ℝ)^2*(DA*Hφ+HA*M₂))
    hM₁.le hM₂.le (by positivity) (by positivity) hHφ (by positivity) (by positivity) (by positivity)
    hqb hqDb (fun x hx => norm_second_quotient_le hφ hb₂ _ x s (hsub hx) (hshift x hx))
    hqH hqDH (differenceQuotient_initial_second_jet_holder hφ hφH _ s hsub hshift)
    hforce.1 hforce.2 (fun x hx => linear_difference_elliptic_equation hφ _ x s
      (heq x (hsub hx)) (heq _ (hshift x hx)))

end GaussianTilt.MomentMapSchauder
