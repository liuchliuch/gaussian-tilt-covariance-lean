import GaussianTilt.MomentMapLinearDirichletVariableWeakChartRelations

/-! # The actual weak Poisson equation in a flattened half-ball

The unknown is an actual H₀¹ jet. Both the chart pullback and the weak
coordinate equation are constructed; no boundary regularity is assumed.
-/
noncomputable section
open Set MeasureTheory Filter Matrix
open scoped Topology ContDiff ENNReal BigOperators
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapRegularity
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 1000

lemma divergenceChartCoefficient_transpose (F ψ : CoordinateSpace n → CoordinateSpace n) (z : CoordinateSpace n) :
    (divergenceChartCoefficient F ψ z)ᵀ=divergenceChartCoefficient F ψ z := by
  simp [divergenceChartCoefficient, Matrix.transpose_smul, Matrix.transpose_mul]

lemma chart_energy_sum (F ψ : CoordinateSpace n → CoordinateSpace n) (z g q : CoordinateSpace n) :
    g ⬝ᵥ (divergenceChartCoefficient F ψ z *ᵥ q)=
      ∑ i, ∑ k, divergenceChartCoefficient F ψ z i k*g k*q i := by
  rw [Matrix.dotProduct_mulVec,← Matrix.mulVec_transpose,divergenceChartCoefficient_transpose,
    dotProduct_comm]
  simp only [dotProduct,Matrix.mulVec,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Every genuine zero-boundary weak Poisson solution yields a genuine
zero-flat-trace H¹ solution with the exact divergence coefficient and
Jacobian scalar forcing in the actual regular-level flattening chart. -/
theorem exists_flattened_weak_poisson {w : E n → ℝ} (hw : ContDiff ℝ ∞ w)
    (a : E n) (j : Fin n) (hj : fderiv ℝ w a (EuclideanSpace.basisFun (Fin n) ℝ j)≠0)
    {s : ℝ} (hs : 0 < s)
    (hInv : ∀ z∈Metric.closedBall (0:E n) (2*s),
      z∈(regularLevelFlatteningChart hw a j hj).target ∧
      ContDiffAt ℝ ∞ (regularLevelFlatteningChart hw a j hj).symm z)
    (u : dirichletSobolev (chartPhysicalDomain w a))
    (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n)))
    (hu : ∀ v : dirichletSobolev (chartPhysicalDomain w a),
      dirichletEnergy (chartPhysicalDomain w a) u v=inner ℝ f (dirichletValue (chartPhysicalDomain w a) v)) :
    ∃ ψ : CoordinateSpace n → CoordinateSpace n, ∃ C : ℝ, ∃ v : dirichletSobolev (coordinateHalfBall j 1),
      ContDiff ℝ ∞ ψ ∧ 0 < C ∧
      (∀ y∈rawChartClosedBall (n:=n) 1, ψ=ᶠ[𝓝 y] scaledRawInverseChart hw a j hj s) ∧
      (volume.restrict (rawChartClosedBall (n:=n) 1)).map ψ≤ENNReal.ofReal (C^2) • volume ∧
      (∀ᵐ y∂volume, y∈rawChartBall (n:=n) (1/2) →
        dirichletValue (coordinateHalfBall j 1) v y=dirichletValue (chartPhysicalDomain w a) u (ψ y)) ∧
      (∀ i, ∀ᵐ y∂volume, y∈rawChartBall (n:=n) (1/2) →
        v.1 i.succ y=∑ k, chartDerivativeEntry ψ i k y*u.1 k.succ (ψ y)) ∧
      ∀ τ:smoothCompactCore n, tsupport τ.1⊆coordinateHalfBall j (1/2) →
        (∫ z, ∑ i:Fin n, ∑ k:Fin n, divergenceChartCoefficient (scaledRawForwardChart w a j s) ψ z i k*
          v.1 k.succ z*coordinateDerivative i τ.1 z)=
          ∫ z, |(fderiv ℝ ψ z).det| *f (ψ z)*τ.1 z := by
  obtain ⟨ψ,C,v,hψ,hC,he,hmap,hval,hgrad⟩ := exists_flattened_dirichletSobolev hw a j hj hs hInv u
  obtain ⟨U,hU,hUb,hleft,hright,hψU,hψΩ⟩ := exists_flattening_physical_test_domain hw a j hj hs hInv hψ he
  refine ⟨ψ,C,v,hψ,hC,he,hmap,hval,hgrad,?_⟩
  intro τ hτ
  let G : CoordinateSpace n → CoordinateSpace n := fun x i=>u.1 i.succ x
  have hh := weak_divergence_equation_in_chart hU hUb (isOpen_rawChartBall (n:=n) (1/2))
    (show coordinateHalfBall j (1/2)⊆rawChartBall (n:=n) (1/2) from fun _ hx=>hx.1)
    (contDiff_scaledRawForwardChart hw a j s) hψ hleft hright hψU hψΩ G f
    (dirichlet_weak_energy_compact_test u f hu) τ hτ
  rw [← hh]
  apply integral_congr_ae
  have hgradall := ae_all_iff.mpr hgrad
  filter_upwards [hgradall] with z hz
  by_cases hzV : z∈rawChartBall (n:=n) (1/2)
  · have hg : weakChartGradient ψ G z=(fun i:Fin n=>v.1 i.succ z) := by
      ext i
      exact (hz i hzV).symm
    rw [hg,chart_energy_sum]
    rfl
  · have hg := coordinateGradient_eq_zero_off_support τ.1 (fun ht=>hzV (hτ ht).1)
    rw [hg,Matrix.mulVec_zero,dotProduct_zero]
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro k _
    have hgi := congrFun hg i
    change coordinateDerivative i τ.1 z=0 at hgi
    rw [hgi,mul_zero]

end GaussianTilt.MomentMapLinearDirichlet
