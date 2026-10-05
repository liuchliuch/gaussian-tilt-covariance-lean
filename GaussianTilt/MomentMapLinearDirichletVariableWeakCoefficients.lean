import GaussianTilt.MomentMapLinearDirichletVariableWeakFlattenedEquation
import GaussianTilt.MomentMapSchauderUniformEllipticity
import GaussianTilt.MomentMapSchauderMatrixCalculus
import Mathlib.Analysis.Calculus.Deriv.Abs

/-! # Genuine positivity and compact bounds of the weak chart coefficients -/
noncomputable section
open Set MeasureTheory Filter Matrix
open scoped Topology ContDiff ENNReal BigOperators NNReal Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapRegularity
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 1000

lemma contDiff_chartJacobian_entry {F : CoordinateSpace n → CoordinateSpace n}
    (hF : ContDiff ℝ ∞ F) (i k:Fin n) : ContDiff ℝ ∞ (fun x=>chartJacobian F x i k) := by
  have hh : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (by simp)
  exact (contDiff_apply ℝ ℝ i).comp (hh.clm_apply contDiff_const)

lemma contDiff_chartJacobian {F : CoordinateSpace n → CoordinateSpace n}
    (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (chartJacobian F) :=
  contDiff_pi.mpr (fun i=>contDiff_pi.mpr (contDiff_chartJacobian_entry hF i))

lemma contDiff_chartJacobian_det {ψ : CoordinateSpace n → CoordinateSpace n}
    (hψ : ContDiff ℝ ∞ ψ) : ContDiff ℝ ∞ (fun x=>(fderiv ℝ ψ x).det) := by
  have hh := GaussianTilt.MomentMapSchauder.contDiff_matrix_det_field (contDiff_chartJacobian_entry hψ)
  simpa only [chartJacobian,LinearMap.det_toMatrix'] using hh

lemma divergenceChartCoefficient_posDef {V : Set (CoordinateSpace n)} (hV:IsOpen V)
    {F ψ : CoordinateSpace n → CoordinateSpace n} (hF:ContDiff ℝ ∞ F) (hψ:ContDiff ℝ ∞ ψ)
    (hleft:∀ x ∈ V, F (ψ x) = x) {z:CoordinateSpace n} (hz:z∈V) :
    (divergenceChartCoefficient F ψ z).PosDef := by
  have hGJ := chartJacobian_inverse_of_left_inverse hV (hF.differentiable (by simp))
    (hψ.differentiable (by simp)).differentiableOn hleft hz
  have hJG := Matrix.mul_eq_one_comm.mp hGJ
  have hinj : Function.Injective (chartJacobian F (ψ z)).vecMul := by
    intro x y he
    have ht := congrArg (fun q=>q ᵥ* chartJacobian ψ z) he
    simpa only [Matrix.vecMul_vecMul,hJG,Matrix.vecMul_one] using ht
  have hgram : (chartJacobian F (ψ z)*(chartJacobian F (ψ z))ᵀ).PosDef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.PosDef.mul_conjTranspose_self (chartJacobian F (ψ z)) hinj
  exact hgram.smul (abs_pos.mpr (jacobian_ne_zero_of_local_left_inverse hV
    (hF.differentiable (by simp)) (hψ.differentiable (by simp)).differentiableOn hleft hz))

lemma contDiffOn_divergenceChartCoefficient {V : Set (CoordinateSpace n)} (hV:IsOpen V)
    {F ψ : CoordinateSpace n → CoordinateSpace n} (hF:ContDiff ℝ ∞ F) (hψ:ContDiff ℝ ∞ ψ)
    (hleft:∀ x ∈ V, F (ψ x) = x) : ContDiffOn ℝ ∞ (divergenceChartCoefficient F ψ) V := by
  have hd := (contDiff_chartJacobian_det hψ).contDiffOn.abs (fun x hx=>
    jacobian_ne_zero_of_local_left_inverse hV (hF.differentiable (by simp))
      (hψ.differentiable (by simp)).differentiableOn hleft hx)
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro k
  change ContDiffOn ℝ ∞ (fun x=>|(fderiv ℝ ψ x).det| *
    ∑ l, chartJacobian F (ψ x) i l*chartJacobian F (ψ x) k l) V
  apply hd.mul
  apply ContDiffOn.sum
  intro l _
  exact (((contDiff_chartJacobian_entry hF i l).comp hψ).mul
    ((contDiff_chartJacobian_entry hF k l).comp hψ)).contDiffOn

lemma exists_lipschitzOnWith_compact_convex_of_contDiffOn
    {X Y:Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {V S:Set X} (hV:IsOpen V) (hS:IsCompact S) (hc:Convex ℝ S) (hSV:S⊆V)
    {f:X→Y} (hf:ContDiffOn ℝ 1 f V) : ∃ L : ℝ≥0, LipschitzOnWith L f S := by
  have hdc : ContinuousOn (fderiv ℝ f) V :=
    (hf.fderiv_of_isOpen hV (m:=0) (by simp)).continuousOn
  obtain ⟨B,hB⟩ := hS.exists_bound_of_continuousOn (hdc.mono hSV)
  let L:ℝ≥0 := (max B 0).toNNReal
  refine ⟨L,hc.lipschitzOnWith_of_nnnorm_fderiv_le (fun x hx=>
    (hf.contDiffAt (hV.mem_nhds (hSV hx))).differentiableAt le_rfl) ?_⟩
  intro x hx
  change ‖fderiv ℝ f x‖≤(L:ℝ)
  simpa only [L,Real.coe_toNNReal _ (le_max_right B 0)] using (hB x hx).trans (le_max_left B 0)

/-- Quantitative ellipticity, entry bounds and a Lipschitz modulus follow
from the actual smooth inverse chart on every compact convex patch. -/
theorem divergenceChartCoefficient_compact_bounds {V S:Set (CoordinateSpace n)}
    (hV:IsOpen V) (hS:IsCompact S) (hc:Convex ℝ S) (hSV:S⊆V)
    {F ψ : CoordinateSpace n → CoordinateSpace n} (hF:ContDiff ℝ ∞ F) (hψ:ContDiff ℝ ∞ ψ)
    (hleft:∀ x ∈ V, F (ψ x) = x) :
    ∃ lam K : ℝ, ∃ L : ℝ≥0, 0 < lam ∧ 0≤K ∧
      LipschitzOnWith L (divergenceChartCoefficient F ψ) S ∧
      (∀ x ∈ S, ∀ i k, |divergenceChartCoefficient F ψ x i k|≤K) ∧
      ∀ x ∈ S, ∀ z : Fin n → ℝ, lam*(∑ i, (z i)^2)≤z ⬝ᵥ (divergenceChartCoefficient F ψ x *ᵥ z) := by
  have hA := contDiffOn_divergenceChartCoefficient hV hF hψ hleft
  obtain ⟨L,hL⟩ := exists_lipschitzOnWith_compact_convex_of_contDiffOn hV hS hc hSV (hA.of_le (by simp))
  obtain ⟨lam,Λ,hlam,hΛ,hell⟩ := GaussianTilt.MomentMapSchauder.exists_uniform_ellipticity_on_compact
    hS (hA.continuousOn.mono hSV) (fun x hx=>divergenceChartCoefficient_posDef hV hF hψ hleft (hSV hx))
  obtain ⟨B,hB⟩ := hS.exists_bound_of_continuousOn (hA.continuousOn.mono hSV)
  refine ⟨lam,max B 0,L,hlam,le_max_right _ _,hL,?_,?_⟩
  · intro x hx i k
    have ht := (norm_le_pi_norm (divergenceChartCoefficient F ψ x i) k).trans
      (norm_le_pi_norm (divergenceChartCoefficient F ψ x) i)
    exact ht.trans ((hB x hx).trans (le_max_left _ _))
  · intro x hx z
    have hh := (hell x hx (WithLp.toLp 2 z)).1
    simpa only [GaussianTilt.MomentMapSchauder.euclideanQuadratic,WithLp.ofLp_toLp,
      EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs] using hh

lemma convex_rawChartClosedBall (r : ℝ) : Convex ℝ (rawChartClosedBall (n:=n) r) := by
  simpa only [rawChartClosedBall,Metric.closedBall,dist_zero_right] using
    (convex_closedBall (0:E n) r).linear_preimage (coordinateEquiv n).symm.toLinearMap

/-- The actual regular-level model has quantitative coefficients on the
closed quarter-ball, with constants derived from its genuine derivatives. -/
theorem actual_flattening_coefficient_bounds {w : E n → ℝ} (hw : ContDiff ℝ ∞ w)
    (a : E n) (j : Fin n) (hj : fderiv ℝ w a (EuclideanSpace.basisFun (Fin n) ℝ j)≠0)
    {s : ℝ} (hs : 0 < s)
    (hInv : ∀ z∈Metric.closedBall (0:E n) (2*s),
      z∈(regularLevelFlatteningChart hw a j hj).target ∧
      ContDiffAt ℝ ∞ (regularLevelFlatteningChart hw a j hj).symm z)
    {ψ : CoordinateSpace n → CoordinateSpace n} (hψ : ContDiff ℝ ∞ ψ)
    (he : ∀ y∈rawChartClosedBall (n:=n) 1, ψ=ᶠ[𝓝 y] scaledRawInverseChart hw a j hj s) :
    ∃ lam K : ℝ, ∃ L : ℝ≥0, 0 < lam ∧ 0 ≤ K ∧
      LipschitzOnWith L (divergenceChartCoefficient (scaledRawForwardChart w a j s) ψ) (rawChartClosedBall (1/4)) ∧
      (∀ x∈rawChartClosedBall (n:=n) (1/4), ∀ i k,
        |divergenceChartCoefficient (scaledRawForwardChart w a j s) ψ x i k| ≤ K) ∧
      ∀ x∈rawChartClosedBall (n:=n) (1/4), ∀ z : Fin n → ℝ,
        lam*(∑ i,(z i)^2) ≤ z ⬝ᵥ (divergenceChartCoefficient (scaledRawForwardChart w a j s) ψ x *ᵥ z) := by
  obtain ⟨U,hU,hUb,hleft,hright,hψU,hψΩ⟩ := exists_flattening_physical_test_domain hw a j hj hs hInv hψ he
  apply divergenceChartCoefficient_compact_bounds (isOpen_rawChartBall (n:=n) (1/2))
    (isCompact_rawChartClosedBall (n:=n) (1/4)) (convex_rawChartClosedBall (1/4))
    (fun x hx => ?_) (contDiff_scaledRawForwardChart hw a j s) hψ hleft
  change ‖(coordinateEquiv n).symm x‖ ≤ 1/4 at hx
  change ‖(coordinateEquiv n).symm x‖ < 1/2
  linarith

end GaussianTilt.MomentMapLinearDirichlet
