import GaussianTilt.MomentMapLinearDirichletVariableWeakUniformChart
import GaussianTilt.MomentMapLinearDirichletBoundaryNormalizationPDE

/-! # Actual H¹ affine transport of frozen boundary problems -/
noncomputable section
open Set MeasureTheory Filter Matrix
open scoped Topology ContDiff ENNReal BigOperators NNReal Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapRegularity
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 1000

lemma continuousLinearEquiv_det_ne_zero (P : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) :
    P.toContinuousLinearMap.det≠0 := by
  have hh := jacobian_ne_zero_of_local_left_inverse isOpen_univ P.symm.differentiable
    P.differentiable.differentiableOn (fun x _=>P.symm_apply_apply x) (mem_univ (0:CoordinateSpace n))
  simpa only [P.fderiv] using hh

lemma exists_linear_measure_bound (P : CoordinateSpace n ≃L[ℝ] CoordinateSpace n)
    {S : Set (CoordinateSpace n)} (hS : MeasurableSet S) :
    ∃ C : ℝ, 0 < C ∧ (volume.restrict S).map P ≤ ENNReal.ofReal (C^2) • volume := by
  let lam := |P.toContinuousLinearMap.det|
  have hlam : 0 < lam := abs_pos.mpr (continuousLinearEquiv_det_ne_zero P)
  have hh := map_restrict_le_of_jacobian_lower hS P.continuous.measurable
    (D:=fun _=>P.toContinuousLinearMap) (fun x _=>P.toContinuousLinearMap.hasFDerivAt)
    P.injective.injOn hlam (fun _ _=>le_rfl)
  let C := lam⁻¹+1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,hh.trans ?_⟩
  rw [← ENNReal.ofReal_inv_of_pos hlam]
  have hb : lam⁻¹ ≤ C^2 := by dsimp [C]; nlinarith [inv_pos.mpr hlam,sq_nonneg lam⁻¹]
  apply Measure.le_iff.mpr
  intro A hA
  simp only [Measure.smul_apply,smul_eq_mul]
  exact mul_le_mul_right' (ENNReal.ofReal_le_ofReal hb) (volume A)

/-- A true affine pullback of an arbitrary upper-domain H₀¹ jet, localized
outside the entire working ball. Its weak gradient is literally PᵀDu. -/
theorem exists_halfspace_affine_sobolev_pullback {Ω:Set (CoordinateSpace n)}
    (j : Fin n) (hΩ : Ω⊆{x:CoordinateSpace n|0<x j})
    (P : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) {c R:ℝ} (hc:0<c) (hR:0<R)
    (hplane:∀x,(P x) j=c*x j) (u:dirichletSobolev Ω) :
    ∃ v:dirichletSobolev {x:CoordinateSpace n|0<x j},
      (∀ᵐ x∂volume, x∈rawChartBall (n:=n) R → v.1 0 x=u.1 0 (P x)) ∧
      ∀ i,∀ᵐ x∂volume, x∈rawChartBall (n:=n) R →
        v.1 i.succ x=∑ k, LinearMap.toMatrix' P.toLinearMap k i*u.1 k.succ (P x) := by
  have hB : Bornology.IsBounded (rawChartBall (n:=n) (2*R)) :=
    (isCompact_rawChartClosedBall (n:=n) (2*R)).isBounded.subset (fun x hx=>show x∈rawChartClosedBall (n:=n) (2*R) from (show ‖(coordinateEquiv n).symm x‖<2*R from hx).le)
  have hsub : rawChartClosedBall (n:=n) R⊆rawChartBall (2*R) := by
    intro x hx
    change ‖(coordinateEquiv n).symm x‖≤R at hx
    change ‖(coordinateEquiv n).symm x‖<2*R
    linarith
  obtain ⟨χ,hχsupp,hχone⟩ := exists_smooth_interior_cutoff (isOpen_rawChartBall (n:=n) (2*R)) hB
    (isCompact_rawChartClosedBall (n:=n) R) hsub
  obtain ⟨C,hC,hmap⟩ := exists_linear_measure_bound P (isCompact_rawChartClosedBall (n:=n) (2*R)).measurableSet
  have hχS : tsupport χ.1⊆rawChartClosedBall (n:=n) (2*R) := fun x hx=>show x∈rawChartClosedBall (n:=n) (2*R) from (show ‖(coordinateEquiv n).symm x‖<2*R from hχsupp hx).le
  have hchart : ∀ x∈tsupport χ.1, P x∈Ω → x∈{x:CoordinateSpace n|0<x j} := by
    intro x hx hxΩ
    have hp := hΩ hxΩ
    change 0<(P x) j at hp
    rw [hplane] at hp
    exact (mul_pos_iff_of_pos_left hc).mp hp
  obtain ⟨v,hval,hgrad⟩ := exists_dirichletSobolev_chart_pullback
    (isCompact_rawChartClosedBall (n:=n) (2*R)).measurableSet P.contDiff hC.le hmap χ hχS hchart u
  have hone (x:CoordinateSpace n) (hx:x∈rawChartBall (n:=n) R) : χ.1 x=1 := hχone (show x∈rawChartClosedBall (n:=n) R from (show ‖(coordinateEquiv n).symm x‖<R from hx).le)
  have hder (i:Fin n) (x:CoordinateSpace n) (hx:x∈rawChartBall (n:=n) R) :
      coordinateDerivative i χ.1 x=0 := by
    have he : χ.1=ᶠ[𝓝 x] (fun _=>1) := by
      filter_upwards [(isOpen_rawChartBall (n:=n) R).mem_nhds hx] with y hy
      exact hone y hy
    unfold coordinateDerivative
    rw [(he.fderiv (𝕜:=ℝ)).self_of_nhds]
    simp
  refine ⟨v,?_,?_⟩
  · filter_upwards [hval] with x hx hxR
    change v.1 0 x=_
    change v.1 0 x=χ.1 x*u.1 0 (P x) at hx
    rw [hx,hone x hxR,one_mul]
  · intro i
    filter_upwards [hgrad i] with x hx hxR
    rw [hx,hder i x hxR,hone x hxR,zero_mul,zero_add]
    simp only [one_mul,chartDerivativeEntry,P.fderiv]
    rfl

end GaussianTilt.MomentMapLinearDirichlet
