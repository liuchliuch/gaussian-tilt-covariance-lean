import GaussianTilt.MomentMapSchauderLocalLogdetBootstrap

/-! # Smoothness of genuine local constant-density Monge–Ampère solutions -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 2000000
open Set
open scoped ContDiff
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapRegularity GaussianTilt.Letwin
variable {n : ℕ}

lemma boundedHolderOn_iteratedFDeriv_two {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {S : Set E} {α : ℝ}
    (hf : BoundedHolderOn α (fderiv ℝ (fderiv ℝ f)) S) :
    BoundedHolderOn α (iteratedFDeriv ℝ 2 f) S := by
  have h0 : BoundedHolderOn α (iteratedFDeriv ℝ 0 (fderiv ℝ (fderiv ℝ f))) S :=
    hf.map (continuousMultilinearCurryFin0 ℝ E (E →L[ℝ] E →L[ℝ] F)).symm.toContinuousLinearEquiv.toContinuousLinearMap
  exact boundedHolderOn_iteratedFDeriv_succ (f := f)
    (boundedHolderOn_iteratedFDeriv_succ (f := fderiv ℝ f) h0)

lemma continuousOn_secondFrechet {u : KernelSpace n → ℝ} {U : Set (KernelSpace n)}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U) : ContinuousOn (fderiv ℝ (fderiv ℝ u)) U :=
  ((hu.fderiv_of_isOpen hU (m := 1) (by norm_num)).fderiv_of_isOpen hU (m := 0) (by norm_num)).continuousOn

lemma locallyHolderJetOn_two_of_hessian_holder {u : KernelSpace n → ℝ}
    {U : Set (KernelSpace n)} (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hloc : ∀ a ∈ U, ∃ R H : ℝ, 0 < R ∧ 0 ≤ H ∧ Metric.closedBall a R ⊆ U ∧
      ∀ x ∈ Metric.closedBall a R, ∀ y ∈ Metric.closedBall a R,
        ‖fderiv ℝ (fderiv ℝ u) x-fderiv ℝ (fderiv ℝ u) y‖ ≤ H*‖x-y‖^α) :
    LocallyHolderJetOn α 2 u U := by
  intro a ha
  obtain ⟨R, H, hR, hH, hsub, hh⟩ := hloc a ha
  obtain ⟨J, hJ⟩ := (isCompact_closedBall a R).exists_bound_of_continuousOn
    ((continuousOn_secondFrechet hU hu).mono hsub)
  have hb : BoundedHolderOn α (fderiv ℝ (fderiv ℝ u)) (Metric.closedBall a R) := by
    refine ⟨max J H, hH.trans (le_max_right _ _), fun x hx => (hJ x hx).trans (le_max_left _ _), ?_⟩
    intro x hx y hy
    exact (hh x hx y hy).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (norm_nonneg _) α))
  exact ⟨R, hR, hsub, holderJetOn_of_top_on hU hu (isCompact_closedBall a R)
    (convex_closedBall a R) hsub hα hα1 (boundedHolderOn_iteratedFDeriv_two hb)⟩

/-- A genuine local C²,α solution of constant log determinant is smooth.
No global C², positive-Hessian, or PDE extension is assumed. -/
theorem local_logdet_contDiffOn_infty [NeZero n]
    {u : KernelSpace n → ℝ} {U : Set (KernelSpace n)} (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U)
    {α c : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hpos : ∀ x ∈ U, (euclideanHessianMatrix u x).PosDef)
    (hMA : ∀ x ∈ U, Real.log (euclideanHessianMatrix u x).det=c)
    (hloc : ∀ a ∈ U, ∃ R H : ℝ, 0 < R ∧ 0 ≤ H ∧ Metric.closedBall a R ⊆ U ∧
      ∀ x ∈ Metric.closedBall a R, ∀ y ∈ Metric.closedBall a R,
        ‖fderiv ℝ (fderiv ℝ u) x-fderiv ℝ (fderiv ℝ u) y‖ ≤ H*‖x-y‖^α) :
    ContDiffOn ℝ ∞ u U :=
  local_logdet_contDiffOn_infty_of_holderJets hU hu hα hα1 hpos hMA
    (locallyHolderJetOn_two_of_hessian_holder hU hu hα.le hα1.le hloc)

/-- The local determinant-one endpoint in the raw Hessian coordinates used
by the Alexandrov reference-limit construction. -/
theorem local_det_one_contDiffOn_infty [NeZero n]
    {u : KernelSpace n → ℝ} {U : Set (KernelSpace n)} (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hpos : ∀ x ∈ U, (coordinateHessian (coordinatePullback u) (coordinateEquiv n x)).PosDef)
    (hMA : ∀ x ∈ U, (coordinateHessian (coordinatePullback u) (coordinateEquiv n x)).det=1)
    (hloc : ∀ a ∈ U, ∃ R H : ℝ, 0 < R ∧ 0 ≤ H ∧ Metric.closedBall a R ⊆ U ∧
      ∀ x ∈ Metric.closedBall a R, ∀ y ∈ Metric.closedBall a R,
        ‖fderiv ℝ (fderiv ℝ u) x-fderiv ℝ (fderiv ℝ u) y‖ ≤ H*‖x-y‖^α) :
    ContDiffOn ℝ ∞ u U := by
  have he (x : KernelSpace n) (hx : x ∈ U) :=
    coordinateHessian_pullback_eq_euclidean_at (hu.contDiffAt (hU.mem_nhds hx))
  apply local_logdet_contDiffOn_infty hU hu hα hα1
    (fun x hx => by simpa only [he x hx] using hpos x hx) (c := 0) ?_ hloc
  intro x hx
  have hh := hMA x hx
  rw [he x hx] at hh
  rw [hh, Real.log_one]

/-- Lipschitz Hessian data, as produced by the genuine Calabi/reference
limit estimates, provide the local α-Hölder input with α=1/2. -/
theorem locallyHolderJetOn_two_of_lipschitz_hessian {u : KernelSpace n → ℝ}
    {U : Set (KernelSpace n)} (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U)
    {L : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ x ∈ U, ∀ y ∈ U, ‖fderiv ℝ (fderiv ℝ u) x-fderiv ℝ (fderiv ℝ u) y‖ ≤ L*‖x-y‖) :
    LocallyHolderJetOn (1/2 : ℝ) 2 u U := by
  apply locallyHolderJetOn_two_of_hessian_holder hU hu (by norm_num) (by norm_num)
  intro a ha
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds ha)
  let R := r/2
  have hR : 0 < R := by dsimp [R]; positivity
  have hsub : Metric.closedBall a R ⊆ U := (Metric.closedBall_subset_ball (by dsimp [R]; linarith)).trans hball
  obtain ⟨j, hj⟩ := (isCompact_closedBall a R).exists_bound_of_continuousOn
    ((continuousOn_secondFrechet hU hu).mono hsub)
  let J := max j 0
  have hJ : 0 ≤ J := le_max_right _ _
  have hJb : ∀ x ∈ Metric.closedBall a R, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ J := fun x hx => (hj x hx).trans (le_max_left _ _)
  refine ⟨R, L+2*J, hR, by positivity, hsub, ?_⟩
  simpa only [Real.one_rpow, mul_one] using holder_bound_of_sup_and_lipschitz hJ hL
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) ≤ 1) zero_lt_one hJb
    (fun x hx y hy => hLip x (hsub hx) y (hsub hy))

/-- Public reference-transfer endpoint: local C², actual Lipschitz Hessian,
and the true positive determinant-one equation imply local smoothness.
All hypotheses are confined to the displayed open region. -/
theorem reference_contDiffOn_infty_of_C2_lipschitz_hessian [NeZero n]
    {u : KernelSpace n → ℝ} {U : Set (KernelSpace n)} (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U)
    (hpos : ∀ x ∈ U, (coordinateHessian (coordinatePullback u) (coordinateEquiv n x)).PosDef)
    (hMA : ∀ x ∈ U, (coordinateHessian (coordinatePullback u) (coordinateEquiv n x)).det=1)
    {L : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ x ∈ U, ∀ y ∈ U, ‖fderiv ℝ (fderiv ℝ u) x-fderiv ℝ (fderiv ℝ u) y‖ ≤ L*‖x-y‖) :
    ContDiffOn ℝ ∞ u U := by
  have he (x : KernelSpace n) (hx : x ∈ U) :=
    coordinateHessian_pullback_eq_euclidean_at (hu.contDiffAt (hU.mem_nhds hx))
  apply local_logdet_contDiffOn_infty_of_holderJets hU hu (by norm_num : (0 : ℝ) < 1/2)
    (by norm_num : (1/2 : ℝ) < 1) (fun x hx => by simpa only [he x hx] using hpos x hx)
    (c := 0) ?_ (locallyHolderJetOn_two_of_lipschitz_hessian hU hu hL hLip)
  intro x hx
  have hh := hMA x hx
  rw [he x hx] at hh
  rw [hh, Real.log_one]

end GaussianTilt.MomentMapSchauder
