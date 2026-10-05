import GaussianTilt.MomentMapLinearDirichletVariableWeakBoundaryTangentialFields
import GaussianTilt.MomentMapLinearDirichletTangentialNormalClosed
import GaussianTilt.MomentMapLinearDirichletTangentialNormalBoundedHolder

/-! # Genuine C²,α closed-boundary regularity of the scalar weak chart equation

Both Campanato applications are constructed from the literal PDE. The first
uses an exponent strictly above α (the vector load is zero); the actual
higher tangential H¹ equations then retain α. Weak normal-flux recovery
constructs the missing normal derivative and the genuine closed C² jet.
-/
noncomputable section
open Set MeasureTheory Filter Matrix
open scoped Topology ContDiff ENNReal BigOperators NNReal Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapRegularity GaussianTilt.MomentMapSchauder
variable {n : ℕ}
set_option maxHeartbeats 3500000
set_option maxSynthPendingDepth 1000

/-- The actual uniformly elliptic scalar weak boundary problem has a
true C²,α representative on a smaller closed half-ball. There is no
boundary derivative, Hessian, Campanato or replacement hypothesis. -/
theorem exists_scalar_weak_boundary_C2_holder [NeZero n]
    (j:Fin n) {A:CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {K lam Λ D lam₀:ℝ}
    (hlam:0<lam) (hΛ:0≤Λ) (hD:0≤D)
    (hA:WeakBallCoefficientBounds A K (1/4) lam Λ D 1)
    (hAs:∀ i k,ContDiffOn ℝ ∞ (fun x=>A x i k) (rawChartBall (n:=n) (1/4)))
    (hlam₀:0<lam₀) (hEll:∀ᵐx∂volume,∀z:Fin n→ℝ,lam₀*(∑i,(z i)^2)≤z ⬝ᵥ (A x *ᵥ z))
    {L:ℝ≥0} (hLip:LipschitzOnWith L A (rawChartClosedBall (n:=n) (1/4)))
    (u:dirichletSobolev (coordinateHalfBall j 1)) (f:Lp ℝ 2 (volume:Measure (CoordinateSpace n)))
    (heq:∀v:dirichletSobolev (coordinateHalfBall j (1/4)),
      variableJetEnergy A hA.measurable hA.nonneg hA.bound u.1 v.1=inner ℝ f (dirichletValue (coordinateHalfBall j (1/4)) v))
    {f₀ u₀:CoordinateSpace n → ℝ} {α:ℝ} (hα:0<α) (hα1:α<1)
    (hfH:BoundedHolderOn α f₀ (coordinateClosedHalfBall j (1/4)))
    (hfAE:∀ᵐx∂volume,x∈coordinateHalfBall j (1/4) → f x=f₀ x)
    (hu₀:ContinuousOn u₀ (coordinateClosedHalfBall j (1/4)))
    (huAE:∀ᵐx∂volume,x∈coordinateHalfBall j (1/4) → u₀ x=u.1 0 x) :
    ∃r:ℝ,0<r ∧ r≤1/16 ∧ ∃Q:CoordinateSpace n → CoordinateSpace n,
    ∃H:CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ,
      ContDiffOn ℝ 2 u₀ (coordinateClosedHalfBall j r) ∧
      ContinuousOn Q (coordinateClosedHalfBall j r) ∧ ContinuousOn H (coordinateClosedHalfBall j r) ∧
      BoundedHolderOn α H (coordinateClosedHalfBall j r) ∧
      (∀x∈coordinateClosedHalfBall j r,HasFDerivWithinAt u₀ (coordinateCovector (Q x)) (coordinateClosedHalfBall j r) x) ∧
      ∀k x,x∈coordinateClosedHalfBall j r →
        HasFDerivWithinAt (fun y=>Q y k) (coordinateCovector (H x k)) (coordinateClosedHalfBall j r) x := by
  let β:ℝ := (1+α)/2
  have hβ:0<β := by dsimp [β]; positivity
  have hβ1:β<1 := by dsimp [β]; linarith
  have hαβ:α≤β := by dsimp [β]; linarith
  have hAβ:WeakBallCoefficientBounds A K (1/4) lam Λ D β :=
    hA.shrink_quarter_exponent hD le_rfl hβ.le hβ1.le
  obtain ⟨F,hF,hFb,hFH⟩ := hfH
  have hLoad := natural_scalar_load_bounds_of_raw_bound j (1/4) β f f₀ hF hFb hfAE
  have hEqLoad:∀v:dirichletSobolev (coordinateHalfBall j (1/4)),
      variableJetEnergy A hAβ.measurable hAβ.nonneg hAβ.bound u.1 v.1=
        variableScalarVectorLoad (coordinateHalfBall j (1/4)) f (fun _=>0) v := by
    intro v
    simpa only [variableScalarVectorLoad_apply,inner_zero_left,Finset.sum_const_zero,add_zero] using heq v
  obtain ⟨rQ,hrQ,hrQbound,Q,hQH,hQc,hQAE⟩ :=
    exists_natural_coordinate_gradient_sharp_holder j (by norm_num : (0:ℝ)<1/4)
      hlam hΛ hD hβ hβ1 hAβ (fun _ hx=>hx.2) u
      (coordinateHalfBall_radius_mono j (by norm_num : (1/4:ℝ)≤1)) hLoad hEqLoad
  have hrQmax:rQ≤1/16 := by norm_num at hrQbound ⊢; exact hrQbound
  obtain ⟨r,hr,hrrQ,hrmax,W,J,hJH,hJc,hWval,hJAE,hJzero⟩ :=
    exists_boundary_tangential_second_fields j hlam hΛ hD hA hAs hlam₀ hEll hLip u f heq hα hα1
      ⟨F,hF,hFb,hFH⟩ hfAE hrQ hrQmax hαβ Q hQH hQAE
  let S := coordinateClosedHalfBall j r
  have hSc:IsCompact S := isCompact_coordinateClosedHalfBall j r
  have hScv:Convex ℝ S := convex_coordinateClosedHalfBall j r
  have hint:(interior S).Nonempty := interior_coordinateClosedHalfBall_nonempty j hr
  have hSin:interior S=coordinateHalfBall j r := interior_coordinateClosedHalfBall j hr
  have hrquarter:r≤1/4 := by linarith
  have hSquarter:S⊆coordinateClosedHalfBall j (1/4) := coordinateClosedHalfBall_mono j hrquarter
  have hSrQ:S⊆coordinateClosedHalfBall j rQ := coordinateClosedHalfBall_mono j hrrQ.le
  have hSraw:S⊆rawChartBall (n:=n) (1/4) := by
    intro x hx
    have hh:=hx.1
    change ‖(coordinateEquiv n).symm x‖≤r at hh
    change ‖(coordinateEquiv n).symm x‖<1/4
    linarith
  have hUquarter:interior S⊆coordinateHalfBall j (1/4) := by
    rw [hSin]
    exact coordinateHalfBall_radius_mono j hrquarter
  have hAH (i k:Fin n) : BoundedHolderOn α (fun x=>A x i k) S := by
    obtain ⟨C,hC,hb,hh⟩ := exists_contDiffOn_holder_bound_on_compact_convex
      (isOpen_rawChartBall (n:=n) (1/4)) ((hAs i k).of_le (by simp)) hSc hScv hSraw hα.le hα1.le
    exact ⟨C,hC.le,hb,hh⟩
  have hADH (i k l:Fin n) : BoundedHolderOn α (coordinateDerivative l (fun x=>A x i k)) S :=
    boundedHolderOn_coefficient_derivatives (isOpen_rawChartBall (n:=n) (1/4)) hSc hScv hSraw hAs hα.le hα1.le l i k
  have hQα:BoundedHolderOn α Q S := boundedHolderOn_lower_exponent hα.le hαβ (hQH.mono hSrQ)
  have hQαi (k:Fin n) : BoundedHolderOn α (fun x=>Q x k) S := hQα.map (ContinuousLinearMap.proj k)
  have hJα (k i:Fin n) : BoundedHolderOn α (fun x=>J x k i) S :=
    (hJH.map (ContinuousLinearMap.proj k)).map (ContinuousLinearMap.proj i)
  have hfα:BoundedHolderOn α f₀ S := (show BoundedHolderOn α f₀ (coordinateClosedHalfBall j (1/4)) from ⟨F,hF,hFb,hFH⟩).mono hSquarter
  have hAc (i k:Fin n) : ContinuousOn (fun x=>A x i k) S := continuousOn_of_boundedHolderOn_weak hα (hAH i k)
  have hADc (i k l:Fin n) : ContinuousOn (coordinateDerivative l (fun x=>A x i k)) S :=
    continuousOn_of_boundedHolderOn_weak hα (hADH i k l)
  have hQci (k:Fin n) : ContinuousOn (fun x=>Q x k) S := continuousOn_of_boundedHolderOn_weak hα (hQαi k)
  have hfc:ContinuousOn f₀ S := continuousOn_of_boundedHolderOn_weak hα hfα
  have hnormal (x:CoordinateSpace n) (hx:x∈S) : lam≤A x j j :=
    hA.normal_coefficient_lower j (hx.1.trans hrquarter)
  have hneq (x:CoordinateSpace n) (hx:x∈S) : A x j j≠0 := (hlam.trans_le (hnormal x hx)).ne'
  have hvalue:∀ᵐx∂volume,x∈interior S → u₀ x=u.1 0 x := by
    filter_upwards [huAE] with x hx hxs
    exact hx (hUquarter hxs)
  have hgradient (k:Fin n) : ∀ᵐx∂volume,x∈interior S → Q x k=u.1 k.succ x := by
    filter_upwards [hQAE k] with x hx hxs
    rw [hSin] at hxs
    exact hx (coordinateHalfBall_radius_mono j hrrQ.le hxs)
  have hW (k:Fin n) (hk:k≠j) : ∀ᵐx∂volume,x∈interior S → (W ⟨k,hk⟩).1 0 x=u.1 k.succ x := by
    filter_upwards [hWval ⟨k,hk⟩] with x hx hxs
    exact hx (by simpa only [hSin] using hxs)
  have hJ (k:Fin n) (hk:k≠j) (i:Fin n) : ∀ᵐx∂volume,x∈interior S → J x k i=(W ⟨k,hk⟩).1 i.succ x := by
    filter_upwards [hJAE ⟨k,hk⟩ i] with x hx hxs
    exact hx (by simpa only [hSin] using hxs)
  have hweak (ψ:smoothCompactCore n) (hψ:tsupport ψ.1⊆interior S) :
      (∫x,∑i:Fin n,∑k:Fin n,A x i k*u.1 k.succ x*coordinateDerivative i ψ.1 x)=∫x,f₀ x*ψ.1 x := by
    rw [scalar_weak_equation_compact_test A hA.measurable hA.nonneg hA.bound u.1 f heq ψ (hψ.trans hUquarter)]
    apply integral_congr_ae
    filter_upwards [hfAE] with x hx
    by_cases hxs:x∈tsupport ψ.1
    · rw [hx (hUquarter (hψ hxs))]
    · rw [image_eq_zero_of_notMem_tsupport hxs,mul_zero,mul_zero]
  obtain ⟨hC2,hDu,hDG⟩ := contDiffOn_two_closed_of_tangential_weak_gradient_representatives
    hScv hSc.isClosed hint j u (fun k hk=>W ⟨k,hk⟩) (hu₀.mono hSquarter) hvalue
    (fun i k=>(hAs i k).mono (interior_subset.trans hSraw)) hAc hADc hQci hJc hfc
    hgradient hW hJ hweak hneq
  have hHH := boundedHolderOn_recoveredWeakHessian j hlam hnormal hAH hADH hQαi hJα hfα
  exact ⟨r,hr,hrmax,Q,recoveredWeakHessian j A Q J f₀,hC2,hQc.mono hSrQ,
    continuousOn_of_boundedHolderOn_weak hα hHH,hHH,hDu,hDG⟩

end GaussianTilt.MomentMapLinearDirichlet
