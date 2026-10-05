import GaussianTilt.MomentMapLinearDirichletVariableWeakEuclideanData

/-! # Actual Euclidean ellipticity and coefficient moduli for the weak iteration -/
noncomputable section
open Set MeasureTheory Filter Matrix
open scoped Topology ContDiff ENNReal BigOperators NNReal Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapRegularity GaussianTilt.MomentMapSchauder
variable {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 1000

/-- The exact chart Gram matrix, even after its harmless exterior
extension, has derived two-sided Euclidean ellipticity on the whole
closed working ball, including the boundary hyperplane. -/
theorem actual_flattening_euclidean_ellipticity {w:E n → ℝ} (hw:ContDiff ℝ ∞ w)
    (a:E n) (j:Fin n) (hj:fderiv ℝ w a (EuclideanSpace.basisFun (Fin n) ℝ j)≠0)
    {s:ℝ} (hs:0<s)
    (hInv:∀ z∈Metric.closedBall (0:E n) (2*s),
      z∈(regularLevelFlatteningChart hw a j hj).target ∧
      ContDiffAt ℝ ∞ (regularLevelFlatteningChart hw a j hj).symm z)
    {ψ:CoordinateSpace n → CoordinateSpace n} (hψ:ContDiff ℝ ∞ ψ)
    (he:∀ y∈rawChartClosedBall (n:=n) 1,ψ=ᶠ[𝓝 y] scaledRawInverseChart hw a j hj s)
    {A:CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hA:∀ x∈rawChartClosedBall (n:=n) (1/4),A x=divergenceChartCoefficient (scaledRawForwardChart w a j s) ψ x) :
    ∃ lam Λ:ℝ,0<lam ∧ 0<Λ ∧ ∀ x:KernelSpace n,‖x‖≤1/4 →
      (A (dirichletCoordinateEquiv n x)).PosDef ∧
      ∀ z:KernelSpace n,lam*‖z‖^2≤euclideanQuadratic (A (dirichletCoordinateEquiv n x)) z ∧
        euclideanQuadratic (A (dirichletCoordinateEquiv n x)) z≤Λ*‖z‖^2 := by
  obtain ⟨U,hU,hUb,hleft,hright,hψU,hψΩ⟩ := exists_flattening_physical_test_domain hw a j hj hs hInv hψ he
  have hsub:rawChartClosedBall (n:=n) (1/4)⊆rawChartBall (1/2) := by
    intro x hx
    change ‖(coordinateEquiv n).symm x‖≤1/4 at hx
    change ‖(coordinateEquiv n).symm x‖<1/2
    linarith
  have hAc:ContinuousOn A (rawChartClosedBall (n:=n) (1/4)) := by
    apply ((contDiffOn_divergenceChartCoefficient (isOpen_rawChartBall (n:=n) (1/2))
      (contDiff_scaledRawForwardChart hw a j s) hψ hleft).continuousOn.mono hsub).congr
    intro x hx
    exact hA x hx
  have hAp (x:CoordinateSpace n) (hx:x∈rawChartClosedBall (n:=n) (1/4)) : (A x).PosDef := by
    rw [hA x hx]
    exact divergenceChartCoefficient_posDef (isOpen_rawChartBall (n:=n) (1/2))
      (contDiff_scaledRawForwardChart hw a j s) hψ hleft (hsub hx)
  obtain ⟨lam,Λ,hlam,hΛ,hbound⟩ := exists_uniform_ellipticity_on_compact
    (isCompact_rawChartClosedBall (n:=n) (1/4)) hAc hAp
  refine ⟨lam,Λ,hlam,hΛ,?_⟩
  intro x hx
  have hxS:dirichletCoordinateEquiv n x∈rawChartClosedBall (n:=n) (1/4) := by
    change ‖(coordinateEquiv n).symm (coordinateEquiv n x)‖≤1/4
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hx
  exact ⟨hAp _ hxS,hbound _ hxS⟩

/-- The actual raw-coordinate Lipschitz coefficient field has a true
Euclidean entrywise Lipschitz modulus on the coordinate-preimage patch. -/
lemma euclidean_entry_modulus_of_coordinate_lipschitz {S:Set (CoordinateSpace n)}
    {A:CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {L:ℝ≥0} (hA:LipschitzOnWith L A S) :
    ∃ D:ℝ,0≤D ∧ ∀ x:KernelSpace n,dirichletCoordinateEquiv n x∈S →
      ∀ y:KernelSpace n,dirichletCoordinateEquiv n y∈S → ∀ i k,
        |A (dirichletCoordinateEquiv n x) i k-A (dirichletCoordinateEquiv n y) i k|≤D*‖x-y‖ := by
  let D:ℝ := (L:ℝ)*‖(dirichletCoordinateEquiv n).toContinuousLinearMap‖
  refine ⟨D,by dsimp [D]; positivity,?_⟩
  intro x hx y hy i k
  have he := (norm_le_pi_norm ((A (dirichletCoordinateEquiv n x)-A (dirichletCoordinateEquiv n y)) i) k).trans
    (norm_le_pi_norm (A (dirichletCoordinateEquiv n x)-A (dirichletCoordinateEquiv n y)) i)
  have hn := (dirichletCoordinateEquiv n).toContinuousLinearMap.le_opNorm (x-y)
  have ht := (hA.norm_sub_le hx hy).trans (mul_le_mul_of_nonneg_left
    (show ‖dirichletCoordinateEquiv n x-dirichletCoordinateEquiv n y‖≤
      ‖(dirichletCoordinateEquiv n).toContinuousLinearMap‖*‖x-y‖ by simpa only [map_sub] using hn) L.coe_nonneg)
  exact he.trans (ht.trans_eq (by dsimp [D]; ring))

lemma boundedHolderOn_composed_dirichletCoordinates {Y:Type*} [NormedAddCommGroup Y]
    {S:Set (CoordinateSpace n)} {f:CoordinateSpace n → Y} {α:ℝ} (hα:0≤α)
    (hf:BoundedHolderOn α f S) :
    BoundedHolderOn α (f ∘ dirichletCoordinateEquiv n) ((dirichletCoordinateEquiv n) ⁻¹' S) :=
  boundedHolderOn_comp_lipschitz hα hf (dirichletCoordinateEquiv n).lipschitz.lipschitzOnWith (fun _ hx=>hx)

end GaussianTilt.MomentMapLinearDirichlet
