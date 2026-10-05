import GaussianTilt.MomentMapSchauderEuclideanSource

/-! # Step-uniform Schauder estimates for genuine source difference quotients -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1600000
open Matrix Set
open scoped ContDiff
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma segment_mem_double_closedBall {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a x e : E} {R s t : ℝ} (hR : 0 ≤ R) (hx : x ∈ Metric.closedBall a R)
    (he : ‖e‖ ≤ 1) (hs : |s| ≤ R) (ht : t ∈ Icc (0 : ℝ) 1) :
    x+t • (s • e) ∈ Metric.closedBall a (2*R) := by
  rw [Metric.mem_closedBall, dist_eq_norm]
  have hx' : ‖x-a‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx
  have hn : ‖t • (s • e)‖ ≤ R := by
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ht.1]
    calc
      t*(|s| * ‖e‖) ≤ 1*(R*1) := mul_le_mul ht.2
        (mul_le_mul hs he (norm_nonneg e) hR) (by positivity) zero_le_one
      _ = R := by ring
  have heq : x+t • (s • e)-a=(x-a)+t • (s • e) := by abel
  rw [heq]
  exact (norm_add_le _ _).trans (by linarith)

lemma norm_second_quotient_le {φ : KernelSpace n → ℝ} (hφ : ContDiff ℝ 2 φ)
    {S : Set (KernelSpace n)} {M : ℝ}
    (hb : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ φ) x‖ ≤ M)
    (h x : KernelSpace n) (s : ℝ) (hx : x ∈ S) (hxh : x+h ∈ S) :
    ‖fderiv ℝ (fderiv ℝ (vectorDifferenceQuotient φ h s)) x‖ ≤ 2*|s⁻¹| * M := by
  rw [secondFrechet_vectorDifferenceQuotient hφ, vectorDifferenceQuotient, norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add (hb _ hxh) (hb _ hx)))
    (abs_nonneg _)).trans_eq (by ring)

/-- All ellipticity, coefficient Hölder, lower-order forcing, and cutoff
constants are derived from the actual C²,α source and C¹,α log-density.
The final estimate is uniform in every sufficiently small nonzero step. -/
theorem exists_uniform_source_difference_schauder [NeZero n]
    {φ g : KernelSpace n → ℝ} (hφ : ContDiff ℝ 2 φ) (hg : ContDiff ℝ 1 g)
    (hpos : ∀ x, (euclideanHessianMatrix φ x).PosDef)
    (hMA : ∀ x, Real.log (euclideanHessianMatrix φ x).det=g x)
    (a : KernelSpace n) {R Hφ Hg α : ℝ} (hR : 0 < R)
    (hHφ : 0 ≤ Hφ) (hHg : 0 ≤ Hg) (hα : 0 < α) (hα1 : α < 1)
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
  obtain ⟨lam, Λ, M, K, hlam, hΛ, hM, hK, hcoef, hcoefH⟩ :=
    exists_euclidean_source_coefficient_bounds hφ hpos hS hHφ hφH
  obtain ⟨r, C₀, hr, hrR, hC₀, hbase⟩ :=
    exists_interior_first_jet_schauder (n := n) hα hα1 hlam hΛ.le hK.le hM.le hR
  let C := C₀*(M₁+M₂+(M₂+2*M₁)+Hφ+G+Hg)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨r, C, hr, by linarith, hC, ?_⟩
  intro e he s hs hsR
  have hseg : ∀ x ∈ Metric.closedBall a R, ∀ t ∈ Icc (0 : ℝ) 1, x+t • (s • e) ∈ S :=
    fun x hx t ht => segment_mem_double_closedBall hR.le hx he hsR ht
  have hsub : Metric.closedBall a R ⊆ S := Metric.closedBall_subset_closedBall (by linarith)
  have hshift : ∀ x ∈ Metric.closedBall a R, x+s • e ∈ S := fun x hx => by
    simpa only [one_smul] using hseg x hx 1 ⟨by norm_num, le_rfl⟩
  have haR : a ∈ Metric.closedBall a R := Metric.mem_closedBall_self hR.le
  have hc := hcoef (s • e) a (hsub haR) (hshift a haR)
  have hsym : ∀ x ∈ Metric.closedBall a R, (euclideanSourceCoefficient φ (s • e) x).IsSymm := by
    intro x hx
    have hh := (hcoef (s • e) x (hsub hx) (hshift x hx)).1.isHermitian
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hh
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
  exact hbase a (euclideanSourceCoefficient φ (s • e)) hc.1 (fun v => (hc.2.2 v).1)
    (fun v => (hc.2.2 v).2) hc.2.1 hsym
    (fun x hx y hy => hcoefH (s • e) x y (hsub hx) (hshift x hx) (hsub hy) (hshift y hy))
    (vectorDifferenceQuotient φ (s • e) s) (vectorDifferenceQuotient g (s • e) s)
    (contDiff_vectorDifferenceQuotient hφ _ _) M₁ M₂ (2*|s⁻¹| * M₂) (M₂+2*M₁) Hφ (2*|s⁻¹| * Hφ) G Hg
    hM₁.le hM₂.le (by positivity) (by positivity) hHφ (by positivity) hG.le hHg
    hqb hqDb (fun x hx => norm_second_quotient_le hφ hb₂ _ x s (hsub hx) (hshift x hx))
    hqH hqDH (differenceQuotient_initial_second_jet_holder hφ hφH _ s hsub hshift)
    hgqb hgqH (fun x _ => euclidean_source_quotient_equation hφ hpos hMA _ x s)

end GaussianTilt.MomentMapSchauder
