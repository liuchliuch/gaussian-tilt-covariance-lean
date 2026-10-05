import GaussianTilt.MomentMapLinearDirichletQuantitativeCoefficientChart

/-! # Genuine forward scaled chart and uniform derivative transport bounds -/
noncomputable section
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 1000
open Set Filter
open scoped Topology ContDiff
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapRegularity GaussianTilt.Letwin
variable {n : ℕ}

def scaledRawForwardChart (w : KernelSpace n → ℝ) (a : KernelSpace n) (j : Fin n)
    (s : ℝ) (x : CoordinateSpace n) : CoordinateSpace n :=
  s⁻¹ • coordinateEquiv n (flatteningMap w a j ((coordinateEquiv n).symm x))

lemma contDiff_scaledRawForwardChart {w : KernelSpace n → ℝ} (hw : ContDiff ℝ ∞ w)
    (a : KernelSpace n) (j : Fin n) (s : ℝ) :
    ContDiff ℝ ∞ (scaledRawForwardChart w a j s) :=
  contDiff_const.smul ((coordinateEquiv n).contDiff.comp
    ((contDiff_flatteningMap hw a j).comp (coordinateEquiv n).symm.contDiff))

lemma scaledRawInverse_forward {w : KernelSpace n → ℝ} (hw : ContDiff ℝ ∞ w)
    (a : KernelSpace n) (j : Fin n)
    (hj : fderiv ℝ w a (EuclideanSpace.basisFun (Fin n) ℝ j) ≠ 0)
    {s : ℝ} (hs : s ≠ 0) {x : CoordinateSpace n}
    (hx : (coordinateEquiv n).symm x ∈ (regularLevelFlatteningChart hw a j hj).source) :
    scaledRawInverseChart hw a j hj s (scaledRawForwardChart w a j s x)=x := by
  unfold scaledRawForwardChart scaledRawInverseChart
  rw [map_smul,ContinuousLinearEquiv.symm_apply_apply,smul_smul,mul_inv_cancel₀ hs,one_smul]
  have hh := (regularLevelFlatteningChart hw a j hj).left_inv hx
  change (regularLevelFlatteningChart hw a j hj).symm
    (flatteningMap w a j ((coordinateEquiv n).symm x))=(coordinateEquiv n).symm x at hh
  rw [hh,ContinuousLinearEquiv.apply_symm_apply]

lemma scaledRawForward_inverse {w : KernelSpace n → ℝ} (hw : ContDiff ℝ ∞ w)
    (a : KernelSpace n) (j : Fin n)
    (hj : fderiv ℝ w a (EuclideanSpace.basisFun (Fin n) ℝ j) ≠ 0)
    {s : ℝ} (hs : s ≠ 0) {y : CoordinateSpace n}
    (hy : s • (coordinateEquiv n).symm y ∈ (regularLevelFlatteningChart hw a j hj).target) :
    scaledRawForwardChart w a j s (scaledRawInverseChart hw a j hj s y)=y := by
  unfold scaledRawForwardChart scaledRawInverseChart
  rw [ContinuousLinearEquiv.symm_apply_apply]
  have hh := (regularLevelFlatteningChart hw a j hj).right_inv hy
  change flatteningMap w a j ((regularLevelFlatteningChart hw a j hj).symm
    (s • (coordinateEquiv n).symm y))=s • (coordinateEquiv n).symm y at hh
  rw [hh,map_smul,ContinuousLinearEquiv.apply_symm_apply,smul_smul,inv_mul_cancel₀ hs,one_smul]

lemma scaledRawForward_self (w : KernelSpace n → ℝ) (a : KernelSpace n) (j : Fin n) (s : ℝ) :
    scaledRawForwardChart w a j s (coordinateEquiv n a)=0 := by
  simp [scaledRawForwardChart,flatteningMap_self]

lemma scaledRawForward_normal (w : KernelSpace n → ℝ) (a : KernelSpace n) (j : Fin n)
    (s : ℝ) (x : CoordinateSpace n) :
    scaledRawForwardChart w a j s x j=s⁻¹*(w a-w ((coordinateEquiv n).symm x)) := by
  change s⁻¹*(flatteningMap w a j ((coordinateEquiv n).symm x)) j=_
  rw [flatteningMap_normal]
  ring

/-- The actual inverse maps yield the inverse derivative needed to recover
original intrinsic derivative fields, including at boundary points. -/
theorem scaled_raw_chart_derivative_left_inverse {w : KernelSpace n → ℝ}
    (hw : ContDiff ℝ ∞ w) (a : KernelSpace n) (j : Fin n)
    (hj : fderiv ℝ w a (EuclideanSpace.basisFun (Fin n) ℝ j) ≠ 0)
    {s : ℝ} (hs : s ≠ 0) {x : CoordinateSpace n}
    (hx : (coordinateEquiv n).symm x ∈ (regularLevelFlatteningChart hw a j hj).source)
    (hX : DifferentiableAt ℝ (scaledRawInverseChart hw a j hj s) (scaledRawForwardChart w a j s x)) :
    (fderiv ℝ (scaledRawInverseChart hw a j hj s) (scaledRawForwardChart w a j s x)).comp
      (fderiv ℝ (scaledRawForwardChart w a j s) x)=ContinuousLinearMap.id ℝ (CoordinateSpace n) := by
  have hn : {z : CoordinateSpace n | (coordinateEquiv n).symm z ∈
      (regularLevelFlatteningChart hw a j hj).source} ∈ 𝓝 x :=
    ((regularLevelFlatteningChart hw a j hj).open_source.preimage (coordinateEquiv n).symm.continuous).mem_nhds hx
  have he : (fun z => scaledRawInverseChart hw a j hj s (scaledRawForwardChart w a j s z)) =ᶠ[𝓝 x] id := by
    filter_upwards [hn] with z hz
    exact scaledRawInverse_forward hw a j hj hs hz
  have hd := (he.fderiv (𝕜 := ℝ)).self_of_nhds
  change fderiv ℝ (scaledRawInverseChart hw a j hj s ∘ scaledRawForwardChart w a j s) x=fderiv ℝ id x at hd
  rw [fderiv_comp x hX ((contDiff_scaledRawForwardChart hw a j s).differentiable (by simp) x),fderiv_id] at hd
  exact hd

/-- Fixed forward-chart constants in physical Euclidean distance. The
bound on the derivative difference is obtained by a genuine mean-value
argument applied to the smooth derivative field. -/
theorem exists_scaled_raw_forward_bounds {w : KernelSpace n → ℝ} (hw : ContDiff ℝ ∞ w)
    (a : KernelSpace n) (j : Fin n) (s ρ : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧
      (∀ x ∈ Metric.closedBall a ρ, ‖fderiv ℝ (scaledRawForwardChart w a j s) (coordinateEquiv n x)‖ ≤ C) ∧
      (∀ x ∈ Metric.closedBall a ρ, ∀ z ∈ Metric.closedBall a ρ,
        ‖fderiv ℝ (scaledRawForwardChart w a j s) (coordinateEquiv n x)-
          fderiv ℝ (scaledRawForwardChart w a j s) (coordinateEquiv n z)‖ ≤ C*dist x z) ∧
      (∀ x ∈ Metric.closedBall a ρ, ∀ z ∈ Metric.closedBall a ρ,
        ‖(coordinateEquiv n).symm (scaledRawForwardChart w a j s (coordinateEquiv n x)-
          scaledRawForwardChart w a j s (coordinateEquiv n z))‖ ≤ C*dist x z) := by
  let Y := scaledRawForwardChart w a j s
  let F := fun x : KernelSpace n => fderiv ℝ Y (coordinateEquiv n x)
  let G := fun x : KernelSpace n => (coordinateEquiv n).symm (Y (coordinateEquiv n x))
  have hY : ContDiff ℝ ∞ Y := contDiff_scaledRawForwardChart hw a j s
  have hF : ContDiff ℝ ∞ F := (hY.fderiv_right (m := ∞) (by simp)).comp (coordinateEquiv n).contDiff
  have hG : ContDiff ℝ ∞ G := (coordinateEquiv n).symm.contDiff.comp (hY.comp (coordinateEquiv n).contDiff)
  have hsum : Continuous (fun x => ‖F x‖+‖fderiv ℝ F x‖+‖fderiv ℝ G x‖) :=
    (hF.continuous.norm.add (hF.fderiv_right (m := ∞) (by simp)).continuous.norm).add
      (hG.fderiv_right (m := ∞) (by simp)).continuous.norm
  obtain ⟨C₀,hC₀⟩ := (isCompact_closedBall a ρ).exists_bound_of_continuousOn hsum.continuousOn
  let C := max 1 C₀
  have hbounds (x : KernelSpace n) (hx : x ∈ Metric.closedBall a ρ) :
      ‖F x‖ ≤ C ∧ ‖fderiv ℝ F x‖ ≤ C ∧ ‖fderiv ℝ G x‖ ≤ C := by
    have hh := hC₀ x hx
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)] at hh
    have hhC : C₀ ≤ C := le_max_right _ _
    constructor
    · linarith [norm_nonneg (fderiv ℝ F x),norm_nonneg (fderiv ℝ G x)]
    constructor
    · linarith [norm_nonneg (F x),norm_nonneg (fderiv ℝ G x)]
    · linarith [norm_nonneg (F x),norm_nonneg (fderiv ℝ F x)]
  refine ⟨C,le_max_left _ _,fun x hx => (hbounds x hx).1,?_,?_⟩
  · intro x hx z hz
    exact (convex_closedBall a ρ).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun y _ => (hF.differentiable (by simp) y).hasFDerivAt.hasFDerivWithinAt)
      (fun y hy => (hbounds y hy).2.1) hz hx
  · intro x hx z hz
    have hh := (convex_closedBall a ρ).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun y _ => (hG.differentiable (by simp) y).hasFDerivAt.hasFDerivWithinAt)
      (fun y hy => (hbounds y hy).2.2) hz hx
    simpa only [G,map_sub,dist_eq_norm] using hh

end GaussianTilt.MomentMapLinearDirichlet
