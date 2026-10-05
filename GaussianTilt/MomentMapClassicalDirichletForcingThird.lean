import GaussianTilt.MomentMapClassicalDirichletContinuationData

/-! # Actual spatial third derivatives of the continuation forcing

Parameterized Fréchet differentiation shows joint continuity of the literal
spatial third derivatives. Compactness supplies a bound uniform in both
the continuation parameter and source point.
-/
noncomputable section
open Set Filter Matrix
open scoped Topology ContDiff BigOperators
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

def spatialCoordinateDerivative (F : ℝ × CoordinateSpace n → ℝ) (i : Fin n)
    (z : ℝ × CoordinateSpace n) : ℝ := coordinateDerivative i (fun y => F (z.1,y)) z.2

lemma contDiffAt_spatialCoordinateDerivative {F : ℝ × CoordinateSpace n → ℝ}
    {z : ℝ × CoordinateSpace n} {k m : WithTop ℕ∞} (hF : ContDiffAt ℝ k F z)
    (hm : m+1 ≤ k) (i : Fin n) : ContDiffAt ℝ m (spatialCoordinateDerivative F i) z := by
  have hparam : ContDiffAt ℝ k
      (Function.uncurry (fun q : ℝ × CoordinateSpace n => fun y : CoordinateSpace n => F (q.1,y))) (z,z.2) :=
    hF.comp (z,z.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  exact (hparam.fderiv contDiffAt_snd hm).clm_apply contDiffAt_const

lemma contDiffAt_spatialThirdDerivative {F : ℝ × CoordinateSpace n → ℝ}
    {z : ℝ × CoordinateSpace n} (hF : ContDiffAt ℝ ∞ F z) (i j k : Fin n) :
    ContDiffAt ℝ ∞ (fun z => coordinateThirdDerivative (fun y => F (z.1,y)) z.2 i j k) z := by
  exact contDiffAt_spatialCoordinateDerivative
    (contDiffAt_spatialCoordinateDerivative
      (contDiffAt_spatialCoordinateDerivative hF (m:=∞) (by simp) i) (m:=∞) (by simp) j)
    (m:=∞) (by simp) k

/-- The true spatial forcing tensor has a uniform bound on the entire
compact continuation cylinder. -/
theorem dirichletContinuationDensity_uniform_log_thirdDerivatives
    {S : Set (CoordinateSpace n)} (hS : IsCompact S) {w : CoordinateSpace n → ℝ}
    (hw : ContDiff ℝ ∞ w) (hH : ∀ x ∈ S, (coordinateHessian w x).PosDef) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ S, ∀ i j k,
      |coordinateThirdDerivative (fun y => Real.log (dirichletContinuationDensity w t y)) x i j k| ≤ B := by
  let K := Icc (0 : ℝ) 1 ×ˢ S
  let F := fun z : ℝ × CoordinateSpace n => Real.log (dirichletContinuationDensity w z.1 z.2)
  have hK : IsCompact K := isCompact_Icc.prod hS
  have hF : ∀ z ∈ K, ContDiffAt ℝ ∞ F z := fun z hz =>
    (contDiff_dirichletContinuationDensity hw).contDiffAt.log
      (dirichletContinuationDensity_pos hz.1 (hH z.2 hz.2)).ne'
  have hC : ContinuousOn (fun z => fun i j k => coordinateThirdDerivative (fun y => F (z.1,y)) z.2 i j k) K :=
    continuousOn_pi.mpr (fun i => continuousOn_pi.mpr (fun j => continuousOn_pi.mpr (fun k z hz =>
      (contDiffAt_spatialThirdDerivative (hF z hz) i j k).continuousAt.continuousWithinAt)))
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn hC
  refine ⟨max B 0,le_max_right _ _,?_⟩
  intro t ht x hx i j k
  have hn := hB (t,x) ⟨ht,hx⟩
  exact (((norm_le_pi_norm
    (fun k => coordinateThirdDerivative (fun y => F (t,y)) x i j k) k).trans
      (norm_le_pi_norm (fun j k => coordinateThirdDerivative (fun y => F (t,y)) x i j k) j)).trans
      (norm_le_pi_norm (fun i j k => coordinateThirdDerivative (fun y => F (t,y)) x i j k) i)).trans
        (hn.trans (le_max_left _ _))

end GaussianTilt.MomentMapRegularity
