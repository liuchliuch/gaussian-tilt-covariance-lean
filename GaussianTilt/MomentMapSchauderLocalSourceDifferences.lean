import GaussianTilt.MomentMapSchauderSourceUniform
import GaussianTilt.MomentMapSchauderSourceThirdOrder

/-! # Source difference estimates with genuinely local positivity and PDE data -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 2000000
open Set Matrix MeasureTheory
open scoped ContDiff BigOperators
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

theorem euclidean_source_quotient_equation_at {φ g : KernelSpace n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (h x : KernelSpace n) (s : ℝ)
    (hposx : (euclideanHessianMatrix φ x).PosDef)
    (hposxh : (euclideanHessianMatrix φ (x+h)).PosDef)
    (hMAx : Real.log (euclideanHessianMatrix φ x).det=g x)
    (hMAxh : Real.log (euclideanHessianMatrix φ (x+h)).det=g (x+h)) :
    euclideanEllipticOperator (euclideanSourceCoefficient φ h x) (vectorDifferenceQuotient φ h s) x =
      vectorDifferenceQuotient g h s x := by
  have htrace : Matrix.trace (euclideanSourceCoefficient φ h x *
      euclideanHessianMatrix (vectorDifferenceQuotient φ h s) x) =
      vectorDifferenceQuotient g h s x := by
    rw [euclideanHessianMatrix_vectorDifferenceQuotient hφ, Matrix.mul_smul, Matrix.trace_smul]
    change s⁻¹*Matrix.trace (averagedInverse (euclideanHessianMatrix φ x) (euclideanHessianMatrix φ (x+h)) *
      (euclideanHessianMatrix φ (x+h)-euclideanHessianMatrix φ x)) = _
    rw [← logdet_sub_eq_trace_averagedInverse hposx hposxh, hMAxh, hMAx]
    rfl
  have hsym := euclideanHessianMatrix_isSymm (contDiff_vectorDifferenceQuotient hφ h s) x
  convert htrace using 1
  simp only [euclideanEllipticOperator, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hsym.apply i j]
  rfl

theorem exists_euclidean_source_coefficient_bounds_on {φ : KernelSpace n → ℝ}
    (hφ : ContDiff ℝ 2 φ) {S : Set (KernelSpace n)} (hS : IsCompact S)
    (hpos : ∀ x ∈ S, (euclideanHessianMatrix φ x).PosDef) {H α : ℝ} (hH : 0 ≤ H)
    (hh : ∀ x ∈ S, ∀ y ∈ S, ‖fderiv ℝ (fderiv ℝ φ) x-fderiv ℝ (fderiv ℝ φ) y‖ ≤ H*‖x-y‖^α) :
    ∃ lam Λ M K : ℝ, 0 < lam ∧ 0 < Λ ∧ 0 < M ∧ 0 < K ∧
      (∀ h x : KernelSpace n, x ∈ S → x+h ∈ S →
        (euclideanSourceCoefficient φ h x).PosDef ∧
        (∀ i j, |euclideanSourceCoefficient φ h x i j| ≤ M) ∧
        (∀ v, lam*‖v‖^2 ≤ euclideanQuadratic (euclideanSourceCoefficient φ h x) v ∧
          euclideanQuadratic (euclideanSourceCoefficient φ h x) v ≤ Λ*‖v‖^2)) ∧
      (∀ h x y : KernelSpace n, x ∈ S → x+h ∈ S → y ∈ S → y+h ∈ S → ∀ i j,
        |euclideanSourceCoefficient φ h x i j-euclideanSourceCoefficient φ h y i j| ≤ K*‖x-y‖^α) := by
  have hcont : ContinuousOn (euclideanHessianMatrix φ) S := (continuous_euclideanHessianMatrix hφ).continuousOn
  obtain ⟨M, hM, hMb⟩ := exists_bound_inv_segments_on_compact hS hcont hpos
  obtain ⟨lam, Λ, hlam, hΛ, hell⟩ := exists_uniform_ellipticity_averagedInverse_on_compact hS hcont hpos
  let K := (n : ℝ)^2*M^2*H+1
  refine ⟨lam, Λ, M, K, hlam, hΛ, hM, by dsimp [K]; positivity, ?_, ?_⟩
  · intro h x hx hxh
    exact ⟨averagedInverse_posDef (hpos x hx) (hpos (x+h) hxh),
      abs_averagedInverse_entry_le (hMb x hx (x+h) hxh), hell x hx (x+h) hxh⟩
  · intro h x y hx hxh hy hyh i j
    have hp := Real.rpow_nonneg (norm_nonneg (x-y)) α
    have he : (x+h)-(y+h)=x-y := by abel
    have hh' : ∀ a ∈ S, ∀ b ∈ S, ∀ i j,
        |euclideanHessianMatrix φ a i j-euclideanHessianMatrix φ b i j| ≤ H*‖a-b‖^α := by
      intro a ha b hb i j
      exact (abs_euclidean_bilinear_entry_le_norm
        (fderiv ℝ (fderiv ℝ φ) a-fderiv ℝ (fderiv ℝ φ) b) i j).trans (hh a ha b hb)
    have hb := abs_averagedInverse_entry_sub_le (hpos x hx) (hpos (x+h) hxh) (hpos y hy) (hpos (y+h) hyh)
      hM.le (mul_nonneg hH hp) (hMb x hx (x+h) hxh) (hMb y hy (y+h) hyh)
      (hh' x hx y hy) (by simpa only [he] using hh' (x+h) hxh (y+h) hyh) i j
    change |euclideanSourceCoefficient φ h x i j-euclideanSourceCoefficient φ h y i j| ≤ _ at hb
    apply hb.trans
    simp only [Fintype.card_fin]
    dsimp [K]
    nlinarith

theorem exists_uniform_source_difference_schauder_local [NeZero n]
    {φ g : KernelSpace n → ℝ} (hφ : ContDiff ℝ 2 φ) (hg : ContDiff ℝ 1 g)
    (a : KernelSpace n) {R Hφ Hg α : ℝ} (hR : 0 < R)
    (hpos : ∀ x ∈ Metric.closedBall a (2*R), (euclideanHessianMatrix φ x).PosDef)
    (hMA : ∀ x ∈ Metric.closedBall a (2*R), Real.log (euclideanHessianMatrix φ x).det=g x)
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
    exists_euclidean_source_coefficient_bounds_on hφ hS hpos hHφ hφH
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
    hgqb hgqH (fun x hx => euclidean_source_quotient_equation_at hφ _ x s
      (hpos x (hsub hx)) (hpos _ (hshift x hx)) (hMA x (hsub hx)) (hMA _ (hshift x hx)))


/-- Constant-logdet C³,α gain requiring positivity and the equation only
on the displayed compact ball. No global positive extension is needed. -/
theorem exists_local_logdet_third_order [NeZero n]
    {φ : KernelSpace n → ℝ} (hφ : ContDiff ℝ 2 φ) (a : KernelSpace n)
    {R H α c : ℝ} (hR : 0 < R) (hH : 0 ≤ H) (hα : 0 < α) (hα1 : α < 1)
    (hpos : ∀ x ∈ Metric.closedBall a (2*R), (euclideanHessianMatrix φ x).PosDef)
    (hMA : ∀ x ∈ Metric.closedBall a (2*R), Real.log (euclideanHessianMatrix φ x).det=c)
    (hφH : ∀ x ∈ Metric.closedBall a (2*R), ∀ y ∈ Metric.closedBall a (2*R),
      ‖fderiv ℝ (fderiv ℝ φ) x-fderiv ℝ (fderiv ℝ φ) y‖ ≤ H*‖x-y‖^α) :
    ∃ r C : ℝ, 0 < r ∧ r ≤ R ∧ 0 < C ∧ ContDiffOn ℝ 3 φ (Metric.ball a r) ∧
      (∀ x ∈ Metric.ball a r, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) x‖ ≤ C) ∧
      (∀ x ∈ Metric.ball a r, ∀ y ∈ Metric.ball a r,
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) x-fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) y‖ ≤ C*‖x-y‖^α) := by
  obtain ⟨r, C, hr, hrR, hC, hq⟩ := exists_uniform_source_difference_schauder_local
    hφ (contDiff_const : ContDiff ℝ 1 (fun _ : KernelSpace n => c)) a hR hpos hMA hH
    (le_refl (0 : ℝ)) hα hα1 hφH (fun x hx y hy => by simp)
  obtain ⟨hc, hb, hh⟩ := contDiffOn_three_of_uniform_second_difference_bounds hφ a hr hR hC.le hα hq
  exact ⟨r/2, C, by linarith, by linarith, hC, hc, hb, hh⟩

end GaussianTilt.MomentMapSchauder
