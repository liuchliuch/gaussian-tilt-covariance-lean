import GaussianTilt.MomentMapLinearDirichletVariableWeakAffineHarmonic
import GaussianTilt.MomentMapLinearDirichletTangentialDifferenceTranslation

/-! # Genuine centered affine H¹ pullback for interior frozen problems -/
noncomputable section
open Set MeasureTheory Filter Matrix
open scoped Topology ContDiff ENNReal BigOperators NNReal Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapRegularity
variable {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 1000

lemma coordinateGradient_translateCore (a:CoordinateSpace n) (τ:smoothCompactCore n) (x:CoordinateSpace n) :
    coordinateGradient (translateSmoothCompactCore a τ).1 x=coordinateGradient τ.1 (x+a) := by
  ext i
  exact coordinateDerivative_translateSmoothCompactCore a τ i x

/-- Compactly localized affine pullback into the genuine whole-space H¹
closure, agreeing with u(Px+a) on the entire working ball. -/
theorem exists_interior_affine_sobolev_pullback {Ω:Set (CoordinateSpace n)}
    (P:CoordinateSpace n ≃L[ℝ] CoordinateSpace n) (a:CoordinateSpace n) {R:ℝ} (hR:0<R)
    (u:dirichletSobolev Ω) :
    ∃ v:dirichletSobolev (univ:Set (CoordinateSpace n)),
      (∀ᵐ x∂volume,x∈rawChartBall (n:=n) R → v.1 0 x=u.1 0 (P x+a)) ∧
      ∀ i,∀ᵐ x∂volume,x∈rawChartBall (n:=n) R →
        v.1 i.succ x=∑ k,LinearMap.toMatrix' P.toLinearMap k i*u.1 k.succ (P x+a) := by
  let σ:CoordinateSpace n → CoordinateSpace n := fun x=>P x+a
  let F:CoordinateSpace n → CoordinateSpace n := fun x=>P.symm (x-a)
  have hσ:ContDiff ℝ ∞ σ := P.contDiff.add contDiff_const
  have hF:ContDiff ℝ ∞ F := P.symm.contDiff.comp (contDiff_id.sub contDiff_const)
  have hleft:∀ x ∈ (univ:Set (CoordinateSpace n)), F (σ x)=x := by intro x _; simp [F,σ]
  obtain ⟨ψ,C,hψ,hC,he,hmap⟩ := exists_bounded_smooth_chart_model isOpen_univ
    (isCompact_rawChartClosedBall (n:=n) (2*R)) (subset_univ _) (hF.differentiable (by simp)) hσ.contDiffOn hleft
  have hB:Bornology.IsBounded (rawChartBall (n:=n) (2*R)) :=
    (isCompact_rawChartClosedBall (n:=n) (2*R)).isBounded.subset (fun x hx=>
      show x∈rawChartClosedBall (n:=n) (2*R) from (show ‖(coordinateEquiv n).symm x‖<2*R from hx).le)
  have hsub:rawChartClosedBall (n:=n) R⊆rawChartBall (2*R) := by
    intro x hx
    change ‖(coordinateEquiv n).symm x‖≤R at hx
    change ‖(coordinateEquiv n).symm x‖<2*R
    linarith
  obtain ⟨χ,hχsupp,hχone⟩ := exists_smooth_interior_cutoff (isOpen_rawChartBall (n:=n) (2*R)) hB
    (isCompact_rawChartClosedBall (n:=n) R) hsub
  have hχS:tsupport χ.1⊆rawChartClosedBall (n:=n) (2*R) := fun x hx=>
    show x∈rawChartClosedBall (n:=n) (2*R) from (show ‖(coordinateEquiv n).symm x‖<2*R from hχsupp hx).le
  obtain ⟨v,hval,hgrad⟩ := exists_dirichletSobolev_chart_pullback
    (isCompact_rawChartClosedBall (n:=n) (2*R)).measurableSet hψ hC.le hmap χ hχS
    (Ω':=(univ:Set (CoordinateSpace n))) (fun _ _ _=>mem_univ _) u
  have hinner (x:CoordinateSpace n) (hx:x∈rawChartBall (n:=n) R) : x∈rawChartClosedBall (n:=n) R := (show ‖(coordinateEquiv n).symm x‖<R from hx).le
  have hbig (x:CoordinateSpace n) (hx:x∈rawChartBall (n:=n) R) : x∈rawChartClosedBall (n:=n) (2*R) :=
    show x∈rawChartClosedBall (n:=n) (2*R) from (show ‖(coordinateEquiv n).symm x‖<2*R from hsub (hinner x hx)).le
  have hone (x:CoordinateSpace n) (hx:x∈rawChartBall (n:=n) R) : χ.1 x=1 := hχone (hinner x hx)
  have hder (i:Fin n) (x:CoordinateSpace n) (hx:x∈rawChartBall (n:=n) R) : coordinateDerivative i χ.1 x=0 := by
    have hh:χ.1=ᶠ[𝓝 x] (fun _=>1) := by
      filter_upwards [(isOpen_rawChartBall (n:=n) R).mem_nhds hx] with y hy
      exact hone y hy
    unfold coordinateDerivative
    rw [(hh.fderiv (𝕜:=ℝ)).self_of_nhds]
    simp
  have hψval (x:CoordinateSpace n) (hx:x∈rawChartBall (n:=n) R) : ψ x=P x+a := (he x (hbig x hx)).self_of_nhds
  have hψder (x:CoordinateSpace n) (hx:x∈rawChartBall (n:=n) R) : fderiv ℝ ψ x=P.toContinuousLinearMap := by
    rw [((he x (hbig x hx)).fderiv (𝕜:=ℝ)).self_of_nhds]
    exact (P.toContinuousLinearMap.hasFDerivAt.add_const a).fderiv
  refine ⟨v,?_,?_⟩
  · filter_upwards [hval] with x hx hxR
    change v.1 0 x=χ.1 x*u.1 0 (ψ x) at hx
    rw [hx,hone x hxR,one_mul,hψval x hxR]
  · intro i
    filter_upwards [hgrad i] with x hx hxR
    rw [hx,hder i x hxR,hone x hxR,zero_mul,zero_add,hψval x hxR]
    simp only [one_mul,chartDerivativeEntry,hψder x hxR]
    rfl

lemma frozen_affine_translate_weak_harmonic {D D':Set (CoordinateSpace n)}
    (P:CoordinateSpace n ≃L[ℝ] CoordinateSpace n) (a:CoordinateSpace n)
    (hPD:MapsTo (fun x=>P x+a) D' D) {B:Matrix (Fin n) (Fin n) ℝ}
    (hB:LinearMap.toMatrix' P.toLinearMap*(LinearMap.toMatrix' P.toLinearMap)ᵀ=B)
    (G:CoordinateSpace n → CoordinateSpace n)
    (heq:∀ξ:smoothCompactCore n,tsupport ξ.1⊆D →
      (∫ x,G x ⬝ᵥ (B *ᵥ coordinateGradient ξ.1 x))=0)
    (τ:smoothCompactCore n) (hτ:tsupport τ.1⊆D') :
    (∫ z,((LinearMap.toMatrix' P.toLinearMap)ᵀ *ᵥ G (P z+a)) ⬝ᵥ coordinateGradient τ.1 z)=0 := by
  let η:smoothCompactCore n := ⟨τ.1 ∘ P.symm,τ.2.1.comp P.symm.contDiff,τ.2.2.comp_homeomorph P.symm.toHomeomorph⟩
  let ξ := translateSmoothCompactCore (-a) η
  have hξ:tsupport ξ.1⊆D := by
    intro x hx
    have ht:tsupport ξ.1⊆(fun x:CoordinateSpace n=>x-a) ⁻¹' tsupport η.1 :=
      tsupport_comp_subset_preimage (continuous_id.sub continuous_const) η.1
    have hi := tsupport_comp_subset_preimage P.symm.continuous τ.1 (ht hx)
    have hp := hPD (hτ hi)
    simpa only [P.apply_symm_apply,sub_add_cancel] using hp
  have hh := heq ξ hξ
  have hs := integral_add_right_eq_self (μ:=(volume:Measure (CoordinateSpace n)))
    (fun x=>G x ⬝ᵥ (B *ᵥ coordinateGradient ξ.1 x)) a
  have hgrad (x:CoordinateSpace n) : coordinateGradient ξ.1 (x+a)=coordinateGradient η.1 x := by
    rw [coordinateGradient_translateCore]
    simp only [add_neg_cancel_right]
  simp_rw [hgrad] at hs
  have hh' : (∫ x,G (x+a) ⬝ᵥ (B *ᵥ coordinateGradient (τ.1 ∘ P.symm) x))=0 := hs.trans hh
  rw [frozen_affine_energy_change P hB (fun x=>G (x+a)) τ] at hh'
  exact (mul_eq_zero.mp hh').resolve_left (abs_ne_zero.mpr (continuousLinearEquiv_det_ne_zero P))

/-- A genuine frozen interior weak problem becomes a genuine whole-space
Sobolev jet harmonic on the contained normalized ball. -/
theorem exists_interior_affine_normalized_harmonic_jet {Ω D:Set (CoordinateSpace n)}
    (P:CoordinateSpace n ≃L[ℝ] CoordinateSpace n) (a:CoordinateSpace n) {R:ℝ} (hR:0<R)
    (hPD:MapsTo (fun x=>P x+a) (rawChartBall (n:=n) R) D)
    {B:Matrix (Fin n) (Fin n) ℝ}
    (hB:LinearMap.toMatrix' P.toLinearMap*(LinearMap.toMatrix' P.toLinearMap)ᵀ=B)
    (u:dirichletSobolev Ω)
    (heq:∀ξ:smoothCompactCore n,tsupport ξ.1⊆D →
      (∫ x,(fun i:Fin n=>u.1 i.succ x) ⬝ᵥ (B *ᵥ coordinateGradient ξ.1 x))=0) :
    ∃ v:dirichletSobolev (univ:Set (CoordinateSpace n)),
      (∀ᵐ x∂volume,x∈rawChartBall (n:=n) R → v.1 0 x=u.1 0 (P x+a)) ∧
      (∀ i,∀ᵐ x∂volume,x∈rawChartBall (n:=n) R →
        v.1 i.succ x=∑ k,LinearMap.toMatrix' P.toLinearMap k i*u.1 k.succ (P x+a)) ∧
      ∀ τ:dirichletSobolev (rawChartBall (n:=n) R),
        (∑ i:Fin n,inner ℝ (v.1 i.succ) (τ.1 i.succ))=0 := by
  obtain ⟨v,hval,hgrad⟩ := exists_interior_affine_sobolev_pullback P a hR u
  refine ⟨v,hval,hgrad,?_⟩
  apply weak_harmonic_all_dirichlet_tests
  intro τ hτ
  have hh := frozen_affine_translate_weak_harmonic P a hPD hB (fun x i=>u.1 i.succ x) heq τ hτ
  apply Eq.trans ?_ hh
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr hgrad] with x hx
  by_cases hxR:x∈rawChartBall (n:=n) R
  · have hg : (fun i:Fin n=>v.1 i.succ x)=(LinearMap.toMatrix' P.toLinearMap)ᵀ *ᵥ (fun i:Fin n=>u.1 i.succ (P x+a)) := by
      funext i
      exact hx i hxR
    rw [hg]
  · rw [coordinateGradient_eq_zero_off_support τ.1 (fun ht=>hxR (hτ ht)),dotProduct_zero,dotProduct_zero]

end GaussianTilt.MomentMapLinearDirichlet
