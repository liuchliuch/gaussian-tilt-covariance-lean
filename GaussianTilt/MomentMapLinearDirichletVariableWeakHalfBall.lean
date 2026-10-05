import GaussianTilt.MomentMapLinearDirichletVariableWeakFlattening
import GaussianTilt.MomentMapLinearDirichletHalfBallGeometry

/-! # Genuine zero-flat-trace weak jets in the actual flattening chart -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff ENNReal BigOperators
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapRegularity
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 1000

def chartPhysicalDomain (w : E n → ℝ) (a : E n) : Set (CoordinateSpace n) :=
  {x | coordinatePullback w x<w a}

/-- The actual inverse chart and an actual compact cutoff transport any
physical H₀¹ function to H₀¹ of a flat half-ball. On the smaller half-ball,
the weak value and gradient are exactly the uncut inverse-chart pullback.
No boundary derivative or boundary regularity of the input is assumed. -/
theorem exists_flattened_dirichletSobolev {w : E n → ℝ} (hw : ContDiff ℝ ∞ w)
    (a : E n) (j : Fin n) (hj : fderiv ℝ w a (EuclideanSpace.basisFun (Fin n) ℝ j)≠0)
    {s : ℝ} (hs : 0 < s)
    (hInv : ∀ z∈Metric.closedBall (0:E n) (2*s),
      z∈(regularLevelFlatteningChart hw a j hj).target ∧
      ContDiffAt ℝ ∞ (regularLevelFlatteningChart hw a j hj).symm z)
    (u : dirichletSobolev (chartPhysicalDomain w a)) :
    ∃ ψ : CoordinateSpace n → CoordinateSpace n, ∃ C : ℝ, ∃ v : dirichletSobolev (coordinateHalfBall j 1),
      ContDiff ℝ ∞ ψ ∧ 0 < C ∧
      (∀ y∈rawChartClosedBall (n:=n) 1, ψ=ᶠ[𝓝 y] scaledRawInverseChart hw a j hj s) ∧
      (volume.restrict (rawChartClosedBall (n:=n) 1)).map ψ≤ENNReal.ofReal (C^2) • volume ∧
      (∀ᵐ y∂volume, y∈rawChartBall (n:=n) (1/2) →
        dirichletValue (coordinateHalfBall j 1) v y=dirichletValue (chartPhysicalDomain w a) u (ψ y)) ∧
      ∀ i, ∀ᵐ y∂volume, y∈rawChartBall (n:=n) (1/2) →
        v.1 i.succ y=∑ k, chartDerivativeEntry ψ i k y*u.1 k.succ (ψ y) := by
  obtain ⟨ψ,C,hψ,hC,he,hmap,hlevel⟩ := exists_actual_flattening_pullback_model hw a j hj hs hInv
  have hUbound : Bornology.IsBounded (rawChartBall (n:=n) 1) :=
    (isCompact_rawChartClosedBall (n:=n) 1).isBounded.subset (fun y hx=>show y∈rawChartClosedBall (n:=n) 1 from
      (show ‖(coordinateEquiv n).symm y‖<1 from hx).le)
  have hKsub : rawChartClosedBall (n:=n) (1/2)⊆rawChartBall 1 := by
    intro y hy
    change ‖(coordinateEquiv n).symm y‖≤1/2 at hy
    change ‖(coordinateEquiv n).symm y‖<1
    linarith
  obtain ⟨χ,hχsupp,hχone⟩ := exists_smooth_interior_cutoff (isOpen_rawChartBall 1) hUbound
    (isCompact_rawChartClosedBall (n:=n) (1/2)) hKsub
  have hχS : tsupport χ.1⊆rawChartClosedBall (n:=n) 1 := fun y hy=>show y∈rawChartClosedBall (n:=n) 1 from
    (show ‖(coordinateEquiv n).symm y‖<1 from hχsupp hy).le
  have hchart : ∀ y∈tsupport χ.1, ψ y∈chartPhysicalDomain w a → y∈coordinateHalfBall j 1 := by
    intro y hy hphys
    refine ⟨hχsupp hy,?_⟩
    have hl := hlevel y (hχS hy)
    change coordinatePullback w (ψ y)<w a at hphys
    rw [hl] at hphys
    nlinarith
  obtain ⟨v,hval,hgrad⟩ := exists_dirichletSobolev_chart_pullback
    (isCompact_rawChartClosedBall (n:=n) 1).measurableSet hψ hC.le hmap χ hχS hchart u
  have hχeq (y : CoordinateSpace n) (hy : y∈rawChartBall (n:=n) (1/2)) : χ.1 y=1 :=
    hχone (show y∈rawChartClosedBall (n:=n) (1/2) from (show ‖(coordinateEquiv n).symm y‖<1/2 from hy).le)
  have hχder (i:Fin n) (y : CoordinateSpace n) (hy : y∈rawChartBall (n:=n) (1/2)) :
      coordinateDerivative i χ.1 y=0 := by
    have heq : χ.1=ᶠ[𝓝 y] (fun _=>1) := by
      filter_upwards [(isOpen_rawChartBall (n:=n) (1/2)).mem_nhds hy] with z hz
      exact hχeq z hz
    unfold coordinateDerivative
    rw [(heq.fderiv (𝕜:=ℝ)).self_of_nhds]
    simp
  refine ⟨ψ,C,v,hψ,hC,he,hmap,?_,?_⟩
  · filter_upwards [hval] with y hy hyin
    rw [hy,hχeq y hyin,one_mul]
  · intro i
    filter_upwards [hgrad i] with y hy hyin
    rw [hy,hχder i y hyin,hχeq y hyin,zero_mul,zero_add]
    simp only [one_mul]

end GaussianTilt.MomentMapLinearDirichlet
