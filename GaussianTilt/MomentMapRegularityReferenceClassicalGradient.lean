import GaussianTilt.MomentMapRegularityReferenceQuadratic

/-! # Actual local classical gradients for the Alexandrov identification -/
noncomputable section
open Set Filter Matrix MeasureTheory
open scoped Topology ContDiff Gradient BigOperators
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin GaussianTilt.MomentMapSchauder
variable {n : ℕ}

lemma contDiff_one_gradient_of_two {u : E n → ℝ} (hu : ContDiff ℝ 2 u) :
    ContDiff ℝ 1 (gradient u) :=
  (InnerProductSpace.toDual ℝ (E n)).symm.contDiff.comp (hu.fderiv_right (m:=1) (by norm_num))

lemma matrix_fderiv_coordinateGradient_two {f : CoordinateSpace n → ℝ}
    (hf : ContDiff ℝ 2 f) (x : CoordinateSpace n) :
    LinearMap.toMatrix' (fderiv ℝ (coordinateGradient f) x).toLinearMap = coordinateHessian f x := by
  ext i j
  change (fderiv ℝ (fun y a => coordinateDerivative a f y) x (Pi.single j 1)) i = _
  rw [fderiv_pi (fun a => (contDiff_coordinateDerivative hf (m:=1) (by norm_num) a).differentiable le_rfl x)]
  rfl

lemma determinant_fderiv_gradient_eq_coordinateHessian_two {u : E n → ℝ}
    (hu : ContDiff ℝ 2 u) (x : E n) :
    (fderiv ℝ (gradient u) x).det =
      (coordinateHessian (coordinatePullback u) (coordinateEquiv n x)).det := by
  let e := coordinateEquiv n
  have hg := (contDiff_one_gradient_of_two hu).differentiable le_rfl
  have hU : ContDiff ℝ 2 (coordinatePullback u) := contDiff_coordinatePullback hu
  have he : coordinateGradient (coordinatePullback u) = fun y => e (gradient u (e.symm y)) :=
    funext (coordinateGradient_pullback (hu.differentiable (by norm_num)))
  have hd : fderiv ℝ (coordinateGradient (coordinatePullback u)) (e x) =
      e.toContinuousLinearMap.comp ((fderiv ℝ (gradient u) x).comp e.symm.toContinuousLinearMap) := by
    rw [he]
    have hinner := (hg (e.symm (e x))).hasFDerivAt.comp (e x) e.symm.hasFDerivAt
    have houter := e.hasFDerivAt.comp (e x) hinner
    simpa only [Function.comp_def,e.symm_apply_apply] using houter.fderiv
  have hmat := matrix_fderiv_coordinateGradient_two hU (e x)
  rw [← hmat,LinearMap.det_toMatrix',hd]
  exact (LinearMap.det_conj (fderiv ℝ (gradient u) x).toLinearMap e.toLinearEquiv).symm

lemma secondFrechet_pos_of_coordinateHessian_posDef {u : E n → ℝ}
    (hu : ContDiff ℝ 2 u) {x v : E n}
    (hH : (coordinateHessian (coordinatePullback u) (coordinateEquiv n x)).PosDef) (hv : v ≠ 0) :
    0 < fderiv ℝ (fderiv ℝ u) x v v := by
  have hraw : coordinateEquiv n v ≠ 0 := fun h => hv ((coordinateEquiv n).injective (by simpa using h))
  have hh := hH.2 (coordinateEquiv n v) hraw
  simp only [star_trivial] at hh
  change 0 < matrixQuadratic (coordinateHessian (coordinatePullback u) (coordinateEquiv n x)) (coordinateEquiv n v) at hh
  rw [← secondFDeriv_eq_hessianQuadratic (contDiff_coordinatePullback hu).contDiffAt,
    secondFDeriv_coordinatePullback hu] at hh
  simpa only [(coordinateEquiv n).symm_apply_apply] using hh

/-- Positive actual Hessians along every connecting segment force gradient
injectivity on a convex set; global positivity or global convexity is not
assumed. -/
lemma gradient_injOn_of_hessian_posDef {u : E n → ℝ} (hu : ContDiff ℝ 2 u)
    {K : Set (E n)} (hK : Convex ℝ K)
    (hH : ∀ x ∈ K, (coordinateHessian (coordinatePullback u) (coordinateEquiv n x)).PosDef) :
    InjOn (gradient u) K := by
  intro x hx y hy hxy
  by_contra hne
  let v := y-x
  have hv : v ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  let f := fun t : ℝ => u (x+t • v)
  have hf : ContDiff ℝ 2 f := hu.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hline (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : x+t • v ∈ K := by
    have hh := hK hx hy (show 0 ≤ 1-t by linarith [ht.2]) ht.1 (by ring : (1-t)+t=1)
    convert hh using 1 <;> dsimp [v] <;> module
  have hfd : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hstrict : StrictMonoOn (deriv f) (Icc (0 : ℝ) 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hfd.continuous.continuousOn
    intro t ht
    rw [second_deriv_affine_line_comp hu]
    exact secondFrechet_pos_of_coordinateHessian_posDef hu (hH _ (hline t (interior_subset ht))) hv
  have hend : deriv f 0 = deriv f 1 := by
    rw [deriv_affine_line_comp (hu.differentiable (by norm_num)),
      deriv_affine_line_comp (hu.differentiable (by norm_num))]
    simp only [zero_smul,one_smul,add_zero]
    have he : x+v=y := by dsimp [v]; abel
    rw [he,← inner_gradient_eq_fderiv,← inner_gradient_eq_fderiv,hxy]
  exact (ne_of_lt (hstrict (by simp) (by simp) (by norm_num))) hend

lemma gradient_congr_nhds {u v : E n → ℝ} {x : E n} (he : u =ᶠ[𝓝 x] v) :
    gradient u =ᶠ[𝓝 x] gradient v := by
  filter_upwards [he.fderiv (𝕜:=ℝ)] with y hy
  simp only [gradient,hy]

lemma coordinatePullback_congr_nhds {u v : E n → ℝ} {x : E n} (he : u =ᶠ[𝓝 x] v) :
    coordinatePullback u =ᶠ[𝓝 (coordinateEquiv n x)] coordinatePullback v := by
  have ht : Tendsto (coordinateEquiv n).symm (𝓝 (coordinateEquiv n x)) (𝓝 x) := by
    simpa only [ContinuousAt,(coordinateEquiv n).symm_apply_apply] using
      (coordinateEquiv n).symm.continuous.continuousAt (x:=coordinateEquiv n x)
  exact he.comp_tendsto ht

end GaussianTilt.MomentMapRegularity
