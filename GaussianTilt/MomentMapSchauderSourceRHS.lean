import GaussianTilt.MomentMapSchauderSourceThirdOrder

/-! # C¹,α regularity of the literal moment-map right-hand side

The potential is required smooth only on its open convex target domain.
Compact source sets generate compact families of target segments, where
actual first and second target derivatives are bounded by compactness.
-/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1400000
open Set InnerProductSpace
open scoped ContDiff Gradient
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma contDiff_gradient_C1 {φ : KernelSpace n → ℝ} (hφ : ContDiff ℝ 2 φ) :
    ContDiff ℝ 1 (gradient φ) :=
  (toDual ℝ (KernelSpace n)).symm.contDiff.comp (hφ.fderiv_right (by norm_num))

lemma norm_gradient_sub (φ : KernelSpace n → ℝ) (x y : KernelSpace n) :
    ‖gradient φ x-gradient φ y‖=‖fderiv ℝ φ x-fderiv ℝ φ y‖ := by
  simpa only [map_sub] using (toDual ℝ (KernelSpace n)).symm.norm_map (fderiv ℝ φ x-fderiv ℝ φ y)

lemma norm_frechetHessian_sub (φ : KernelSpace n → ℝ) (x y : KernelSpace n) :
    ‖frechetHessian φ x-frechetHessian φ y‖=‖fderiv ℝ (fderiv ℝ φ) x-fderiv ℝ (fderiv ℝ φ) y‖ := by
  have he (v : KernelSpace n) :
      ‖(frechetHessian φ x-frechetHessian φ y) v‖=
      ‖(fderiv ℝ (fderiv ℝ φ) x-fderiv ℝ (fderiv ℝ φ) y) v‖ := by
    simpa only [map_sub] using (toDual ℝ (KernelSpace n)).symm.norm_map
      (fderiv ℝ (fderiv ℝ φ) x v-fderiv ℝ (fderiv ℝ φ) y v)
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (fderiv ℝ (fderiv ℝ φ) x-fderiv ℝ (fderiv ℝ φ) y))
    intro v
    rw [he]
    exact (fderiv ℝ (fderiv ℝ φ) x-fderiv ℝ (fderiv ℝ φ) y).le_opNorm v
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (frechetHessian φ x-frechetHessian φ y))
    intro v
    rw [← he]
    exact (frechetHessian φ x-frechetHessian φ y).le_opNorm v

lemma norm_clm_comp_sub_le {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A B : F →L[ℝ] G) (P Q : E →L[ℝ] F) :
    ‖A.comp P-B.comp Q‖ ≤ ‖A‖*‖P-Q‖+‖A-B‖*‖Q‖ := by
  have he : A.comp P-B.comp Q=A.comp (P-Q)+(A-B).comp Q := by
    ext v
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply, map_sub]
    abel
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
    (ContinuousLinearMap.opNorm_comp_le _ _))

def sourceRHS (φ V : KernelSpace n → ℝ) (x : KernelSpace n) : ℝ := -φ x+V (gradient φ x)

lemma contDiff_sourceRHS {φ V : KernelSpace n → ℝ} (hφ : ContDiff ℝ 2 φ)
    {Ω : Set (KernelSpace n)} (hΩ : IsOpen Ω) (hV : ContDiffOn ℝ 2 V Ω)
    (hmap : ∀ x, gradient φ x ∈ Ω) : ContDiff ℝ 1 (sourceRHS φ V) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  exact (hφ.contDiffAt.of_le (by norm_num)).neg.add
    (((hV.contDiffAt (hΩ.mem_nhds (hmap x))).of_le (by norm_num)).comp x
      (contDiff_gradient_C1 hφ).contDiffAt)

lemma fderiv_sourceRHS {φ V : KernelSpace n → ℝ} (hφ : ContDiff ℝ 2 φ)
    {Ω : Set (KernelSpace n)} (hΩ : IsOpen Ω) (hV : ContDiffOn ℝ 2 V Ω)
    (hmap : ∀ x, gradient φ x ∈ Ω) (x : KernelSpace n) :
    fderiv ℝ (sourceRHS φ V) x = -fderiv ℝ φ x+
      (fderiv ℝ V (gradient φ x)).comp (frechetHessian φ x) := by
  have hdV := (hV.contDiffAt (hΩ.mem_nhds (hmap x))).differentiableAt (by norm_num)
  have hdφ := hφ.differentiable (by norm_num) x
  exact ((hdφ.hasFDerivAt.neg).add (hdV.hasFDerivAt.comp x (hasFDerivAt_gradient_frechetHessian hφ x))).fderiv

/-- A true C²,α source makes −φ+V(∇φ) C¹,α on every compact convex source
set. Target derivative bounds and the resulting constant are constructed. -/
theorem exists_sourceRHS_derivative_holder {φ V : KernelSpace n → ℝ}
    (hφ : ContDiff ℝ 2 φ) {Ω S : Set (KernelSpace n)}
    (hΩ : IsOpen Ω) (hΩc : Convex ℝ Ω) (hV : ContDiffOn ℝ 2 V Ω)
    (hmap : ∀ x, gradient φ x ∈ Ω) (hS : IsCompact S) (hSc : Convex ℝ S)
    {H α : ℝ} (hH : 0 ≤ H) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hφH : ∀ x ∈ S, ∀ y ∈ S, ‖fderiv ℝ (fderiv ℝ φ) x-fderiv ℝ (fderiv ℝ φ) y‖ ≤ H*‖x-y‖^α) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ S, ∀ y ∈ S,
      ‖fderiv ℝ (sourceRHS φ V) x-fderiv ℝ (sourceRHS φ V) y‖ ≤ C*‖x-y‖^α := by
  have hDφ : ContDiff ℝ 1 (fderiv ℝ φ) := hφ.fderiv_right (by norm_num)
  have hD2c := (hDφ.fderiv_right (m := 0) (by norm_num)).continuous
  obtain ⟨m₁, hm₁⟩ := hS.exists_bound_of_continuousOn hDφ.continuous.continuousOn
  obtain ⟨m₂, hm₂⟩ := hS.exists_bound_of_continuousOn hD2c.continuousOn
  let M₁ := max m₁ 1
  let M₂ := max m₂ 1
  have hM₁ : 0 ≤ M₁ := (show (0 : ℝ) ≤ 1 by norm_num).trans (le_max_right _ _)
  have hM₂ : 0 ≤ M₂ := (show (0 : ℝ) ≤ 1 by norm_num).trans (le_max_right _ _)
  have hb₁ : ∀ x ∈ S, ‖fderiv ℝ φ x‖ ≤ M₁ := fun x hx => (hm₁ x hx).trans (le_max_left _ _)
  have hb₂ : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ φ) x‖ ≤ M₂ := fun x hx => (hm₂ x hx).trans (le_max_left _ _)
  let Q : Set (KernelSpace n × KernelSpace n × ℝ) := S ×ˢ (S ×ˢ Icc (0 : ℝ) 1)
  let F : KernelSpace n × KernelSpace n × ℝ → KernelSpace n := fun p =>
    (1-p.2.2) • gradient φ p.1+p.2.2 • gradient φ p.2.1
  let T := F '' Q
  have hcF : Continuous F :=
    (continuous_const.sub (continuous_snd.comp continuous_snd)).smul
      ((contDiff_gradient_C1 hφ).continuous.comp continuous_fst) |>.add
      ((continuous_snd.comp continuous_snd).smul
        ((contDiff_gradient_C1 hφ).continuous.comp (continuous_fst.comp continuous_snd)))
  have hT : IsCompact T := (hS.prod (hS.prod isCompact_Icc)).image hcF
  have hTΩ : T ⊆ Ω := by
    rintro z ⟨p, hp, rfl⟩
    exact hΩc (hmap p.1) (hmap p.2.1) (sub_nonneg.mpr hp.2.2.2) hp.2.2.1 (by ring)
  have hTmem : ∀ x ∈ S, gradient φ x ∈ T := by
    intro x hx
    refine ⟨(x, x, 0), ⟨hx, hx, by norm_num, by norm_num⟩, ?_⟩
    simp [F]
  have hseg : ∀ x ∈ S, ∀ y ∈ S, segment ℝ (gradient φ x) (gradient φ y) ⊆ T := by
    intro x hx y hy z hz
    rw [segment_eq_image_lineMap] at hz
    obtain ⟨t, ht, htz⟩ := hz
    exact ⟨(x, y, t), ⟨hx, hy, ht⟩, by simpa only [F, AffineMap.lineMap_apply_module] using htz⟩
  have hDV : ContDiffOn ℝ 1 (fderiv ℝ V) Ω := hV.fderiv_of_isOpen hΩ (by norm_num)
  have hD2V : ContDiffOn ℝ 0 (fderiv ℝ (fderiv ℝ V)) Ω := hDV.fderiv_of_isOpen hΩ (by norm_num)
  obtain ⟨q, hq⟩ := hT.exists_bound_of_continuousOn (hDV.continuousOn.mono hTΩ)
  obtain ⟨p, hp⟩ := hT.exists_bound_of_continuousOn (hD2V.continuousOn.mono hTΩ)
  let N := max q 1
  let P := max p 1
  have hN : 0 ≤ N := (show (0 : ℝ) ≤ 1 by norm_num).trans (le_max_right _ _)
  have hP : 0 ≤ P := (show (0 : ℝ) ≤ 1 by norm_num).trans (le_max_right _ _)
  have hNb : ∀ x ∈ T, ‖fderiv ℝ V x‖ ≤ N := fun x hx => (hq x hx).trans (le_max_left _ _)
  have hPb : ∀ x ∈ T, ‖fderiv ℝ (fderiv ℝ V) x‖ ≤ P := fun x hx => (hp x hx).trans (le_max_left _ _)
  have hVLip : ∀ x ∈ S, ∀ y ∈ S,
      ‖fderiv ℝ V (gradient φ x)-fderiv ℝ V (gradient φ y)‖ ≤ P*‖gradient φ x-gradient φ y‖ := by
    intro x hx y hy
    exact Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z hz => (hDV.contDiffAt (hΩ.mem_nhds (hTΩ (hseg x hx y hy hz)))).differentiableAt le_rfl)
      (fun z hz => hPb z (hseg x hx y hy hz)) (convex_segment (𝕜 := ℝ) _ _)
      (right_mem_segment ℝ _ _) (left_mem_segment ℝ _ _)
  have hLip : ∀ x ∈ S, ∀ y ∈ S, ‖fderiv ℝ φ x-fderiv ℝ φ y‖ ≤ M₂*‖x-y‖ := by
    intro x hx y hy
    exact Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hDφ.differentiable le_rfl z) hb₂ hSc hy hx
  let L := M₂+2*M₁
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hh₁ : ∀ x ∈ S, ∀ y ∈ S, ‖fderiv ℝ φ x-fderiv ℝ φ y‖ ≤ L*‖x-y‖^α := by
    simpa only [Real.one_rpow, mul_one] using holder_bound_of_sup_and_lipschitz hM₁ hM₂ hα hα1 zero_lt_one hb₁ hLip
  refine ⟨L+N*H+P*L*M₂+1, by positivity, ?_⟩
  intro x hx y hy
  rw [fderiv_sourceRHS hφ hΩ hV hmap, fderiv_sourceRHS hφ hΩ hV hmap]
  have hVdiff := (hVLip x hx y hy).trans
    (mul_le_mul_of_nonneg_left (by simpa only [norm_gradient_sub] using hh₁ x hx y hy) hP)
  have hHdiff : ‖frechetHessian φ x-frechetHessian φ y‖ ≤ H*‖x-y‖^α := by
    simpa only [norm_frechetHessian_sub] using hφH x hx y hy
  have hHb : ‖frechetHessian φ y‖ ≤ M₂ := by simpa only [norm_frechetHessian] using hb₂ y hy
  have hc := (norm_clm_comp_sub_le (fderiv ℝ V (gradient φ x)) (fderiv ℝ V (gradient φ y))
    (frechetHessian φ x) (frechetHessian φ y)).trans
      (add_le_add (mul_le_mul (hNb _ (hTmem x hx)) hHdiff (norm_nonneg _) hN)
        (mul_le_mul hVdiff hHb (norm_nonneg _) (by positivity)))
  have he : -fderiv ℝ φ x+(fderiv ℝ V (gradient φ x)).comp (frechetHessian φ x)-
      (-fderiv ℝ φ y+(fderiv ℝ V (gradient φ y)).comp (frechetHessian φ y)) =
      -(fderiv ℝ φ x-fderiv ℝ φ y)+
        ((fderiv ℝ V (gradient φ x)).comp (frechetHessian φ x)-
          (fderiv ℝ V (gradient φ y)).comp (frechetHessian φ y)) := by abel
  rw [he]
  apply (norm_add_le _ _).trans
  have hn : ‖-(fderiv ℝ φ x-fderiv ℝ φ y)‖ ≤ L*‖x-y‖^α := by
    simpa only [norm_neg] using hh₁ x hx y hy
  exact (add_le_add hn hc).trans (by nlinarith [Real.rpow_nonneg (norm_nonneg (x-y)) α])

/-- First source bootstrap with the actual moment-map nonlinearity. The
right-hand side Hölder assumption is discharged from the first C²,α source
regularity and target C² regularity on its open convex domain. -/
theorem exists_moment_source_third_order_holder [NeZero n]
    {φ V : KernelSpace n → ℝ} (hφ : ContDiff ℝ 2 φ)
    {Ω : Set (KernelSpace n)} (hΩ : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (hV : ContDiffOn ℝ 2 V Ω) (hmap : ∀ x, gradient φ x ∈ Ω)
    (hpos : ∀ x, (euclideanHessianMatrix φ x).PosDef)
    (hMA : ∀ x, Real.log (euclideanHessianMatrix φ x).det= -φ x+V (gradient φ x))
    (a : KernelSpace n) {R H α : ℝ} (hR : 0 < R) (hH : 0 ≤ H)
    (hα : 0 < α) (hα1 : α < 1)
    (hφH : ∀ x ∈ Metric.closedBall a (2*R), ∀ y ∈ Metric.closedBall a (2*R),
      ‖fderiv ℝ (fderiv ℝ φ) x-fderiv ℝ (fderiv ℝ φ) y‖ ≤ H*‖x-y‖^α) :
    ∃ r C : ℝ, 0 < r ∧ r ≤ R ∧ 0 < C ∧ ContDiffOn ℝ 3 φ (Metric.ball a r) ∧
      (∀ x ∈ Metric.ball a r, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) x‖ ≤ C) ∧
      (∀ x ∈ Metric.ball a r, ∀ y ∈ Metric.ball a r,
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) x-fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) y‖ ≤ C*‖x-y‖^α) := by
  obtain ⟨Hg, hHg, hgH⟩ := exists_sourceRHS_derivative_holder hφ hΩ hΩc hV hmap
    (isCompact_closedBall a (2*R)) (convex_closedBall a (2*R)) hH hα.le hα1.le hφH
  exact exists_source_third_order_holder hφ (contDiff_sourceRHS hφ hΩ hV hmap) hpos hMA a hR
    hH hHg.le hα hα1 hφH hgH

/-- A global C² moment source with local C²,α moduli is genuinely C³.
There is no assumed differentiated elliptic equation or source derivative. -/
theorem moment_source_contDiff_three [NeZero n]
    {φ V : KernelSpace n → ℝ} (hφ : ContDiff ℝ 2 φ)
    {Ω : Set (KernelSpace n)} (hΩ : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (hV : ContDiffOn ℝ 2 V Ω) (hmap : ∀ x, gradient φ x ∈ Ω)
    (hpos : ∀ x, (euclideanHessianMatrix φ x).PosDef)
    (hMA : ∀ x, Real.log (euclideanHessianMatrix φ x).det= -φ x+V (gradient φ x))
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hloc : ∀ a : KernelSpace n, ∃ R H : ℝ, 0 < R ∧ 0 ≤ H ∧
      ∀ x ∈ Metric.closedBall a (2*R), ∀ y ∈ Metric.closedBall a (2*R),
        ‖fderiv ℝ (fderiv ℝ φ) x-fderiv ℝ (fderiv ℝ φ) y‖ ≤ H*‖x-y‖^α) :
    ContDiff ℝ 3 φ := by
  apply contDiff_iff_contDiffAt.mpr
  intro a
  obtain ⟨R, H, hR, hH, hholder⟩ := hloc a
  obtain ⟨r, C, hr, _, _, hc, _⟩ := exists_moment_source_third_order_holder
    hφ hΩ hΩc hV hmap hpos hMA a hR hH hα hα1 hholder
  exact hc.contDiffAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))

end GaussianTilt.MomentMapSchauder
