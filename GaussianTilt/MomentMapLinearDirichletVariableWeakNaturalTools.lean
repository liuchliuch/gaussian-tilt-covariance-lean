import GaussianTilt.MomentMapLinearDirichletVariableWeakNaturalFields
import GaussianTilt.MomentMapHolderChartFields

/-! # Exact restriction and coordinate interfaces for the actual two-pass proof -/
noncomputable section
open Set MeasureTheory Filter Matrix
open scoped Topology ContDiff ENNReal BigOperators Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapSchauder
variable {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 1000

lemma continuousOn_of_boundedHolderOn_weak {Y:Type*} [NormedAddCommGroup Y]
    {S:Set (CoordinateSpace n)} {f:CoordinateSpace n → Y} {β:ℝ} (hβ:0<β)
    (hf:BoundedHolderOn β f S) : ContinuousOn f S := by
  obtain ⟨C,hC,hb,hh⟩ := hf
  exact GaussianTilt.HolderSpace.continuousOn_of_holder_bound_general hβ hh

lemma WeakBallCoefficientBounds.shrink_quarter_exponent
    {A:CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {K lam Λ D r β:ℝ}
    (hA:WeakBallCoefficientBounds A K (1/4) lam Λ D 1)
    (hD:0≤D) (hr:r≤1/4) (hβ:0≤β) (hβ1:β≤1) :
    WeakBallCoefficientBounds A K r lam Λ D β := by
  refine ⟨hA.nonneg,hA.measurable,hA.bound,fun x hx=>hA.positive x (hx.trans hr),
    fun x hx=>hA.lower x (hx.trans hr),fun x hx=>hA.upper x (hx.trans hr),?_⟩
  intro x hx y hy i k
  have hh := hA.holder x (hx.trans hr) y (hy.trans hr) i k
  have hn:‖x-y‖≤1 := by nlinarith [norm_sub_le x y]
  have hp := Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg (x-y)) hn hβ hβ1
  exact hh.trans (mul_le_mul_of_nonneg_left hp hD)

lemma WeakBallCoefficientBounds.normal_coefficient_lower
    {A:CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {K R lam Λ D β:ℝ}
    (hA:WeakBallCoefficientBounds A K R lam Λ D β) (j:Fin n)
    {x:CoordinateSpace n} (hx:‖(dirichletCoordinateEquiv n).symm x‖≤R) : lam≤A x j j := by
  have hl (z:CoordinateSpace n) : lam*(∑i:Fin n,(z i)^2)≤z ⬝ᵥ (A x *ᵥ z) := by
    have hh := hA.lower ((dirichletCoordinateEquiv n).symm x) hx (WithLp.toLp 2 z)
    simpa only [ContinuousLinearEquiv.apply_symm_apply,euclideanQuadratic,WithLp.ofLp_toLp,
      EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs] using hh
  exact normal_coefficient_lower_of_ellipticity hl j

lemma scalar_weak_equation_compact_test {U:Set (CoordinateSpace n)}
    (A:CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hAm:∀i k,AEStronglyMeasurable (fun x=>A x i k) volume)
    {K:ℝ} (hK:0≤K) (hAb:∀i k,∀ᵐx∂volume,|A x i k|≤K)
    (u:VolumeJet n) (f:Lp ℝ 2 (volume:Measure (CoordinateSpace n)))
    (heq:∀v:dirichletSobolev U,variableJetEnergy A hAm hK hAb u v.1=inner ℝ f (dirichletValue U v))
    (ψ:smoothCompactCore n) (hψ:tsupport ψ.1⊆U) :
    (∫x,∑i:Fin n,∑k:Fin n,A x i k*u k.succ x*coordinateDerivative i ψ.1 x)=∫x,f x*ψ.1 x := by
  have hh := heq (dirichletCoreToSobolev U ⟨ψ,hψ⟩)
  change variableJetEnergy A hAm hK hAb u (smoothCompactJet volume ψ)=inner ℝ f (smoothCompactToL2 volume ψ) at hh
  rw [variableJetEnergy_smooth_test,inner_Lp_smoothCompactToL2] at hh
  exact hh

lemma scalar_weak_equation_mono {U V:Set (CoordinateSpace n)} (hUV:U⊆V)
    (A:CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hAm:∀i k,AEStronglyMeasurable (fun x=>A x i k) volume)
    {K:ℝ} (hK:0≤K) (hAb:∀i k,∀ᵐx∂volume,|A x i k|≤K)
    (u:VolumeJet n) (f:Lp ℝ 2 (volume:Measure (CoordinateSpace n)))
    (heq:∀v:dirichletSobolev V,variableJetEnergy A hAm hK hAb u v.1=inner ℝ f (dirichletValue V v))
    (v:dirichletSobolev U) : variableJetEnergy A hAm hK hAb u v.1=inner ℝ f (dirichletValue U v) :=
  heq (dirichletInclusion hUV v)

end GaussianTilt.MomentMapLinearDirichlet
