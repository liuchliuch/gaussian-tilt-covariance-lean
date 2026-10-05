import GaussianTilt.MomentMapLinearDirichletFlatteningCoordinates

/-!
# Constructed quantitative bounds for the fixed flattening chart

All constants are extracted from genuine compact neighborhoods of the
actual inverse-function-theorem chart. Only the fixed defining function is
globally smooth; no unknown Dirichlet solution occurs in these hypotheses.
-/
noncomputable section
set_option maxRecDepth 4096
set_option maxSynthPendingDepth 1000
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 500000
set_option synthInstance.maxSize 2048
open Set Filter
open scoped Topology ContDiff
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

/-- Bounds on the first three actual successive Fréchet derivatives. -/
def ThreeDerivativeBound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (x : E) (C : ℝ) : Prop :=
  ‖fderiv ℝ f x‖ ≤ C ∧ ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C ∧
    ‖fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x‖ ≤ C

lemma ThreeDerivativeBound.mono {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {x : E} {C D : ℝ}
    (h : ThreeDerivativeBound f x C) (hCD : C ≤ D) : ThreeDerivativeBound f x D :=
  ⟨h.1.trans hCD,h.2.1.trans hCD,h.2.2.trans hCD⟩

theorem exists_three_derivative_bound_on_compact
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {U S : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (hS : IsCompact S) (hSU : S ⊆ U) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x ∈ S, ThreeDerivativeBound f x C := by
  have hf₁ : ContDiffOn ℝ ∞ (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by simp)
  have hf₂ : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ f)) U := hf₁.fderiv_of_isOpen hU (by simp)
  have hf₃ : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ (fderiv ℝ f))) U := hf₂.fderiv_of_isOpen hU (by simp)
  let b := fun x => ‖fderiv ℝ f x‖+‖fderiv ℝ (fderiv ℝ f) x‖+
    ‖fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x‖
  have hb : ContinuousOn b S :=
    ((hf₁.continuousOn.norm.add hf₂.continuousOn.norm).add hf₃.continuousOn.norm).mono hSU
  obtain ⟨M,hM⟩ := hS.exists_bound_of_continuousOn hb
  refine ⟨max M 1,le_max_right _ _,?_⟩
  intro x hx
  have hMx : |b x| ≤ M := by simpa only [Real.norm_eq_abs] using hM x hx
  have hh : b x ≤ max M 1 := (le_abs_self _).trans (hMx.trans (le_max_left _ _))
  dsimp only [b] at hh
  refine ⟨?_,?_,?_⟩ <;> nlinarith [norm_nonneg (fderiv ℝ f x),
    norm_nonneg (fderiv ℝ (fderiv ℝ f) x),norm_nonneg (fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x)]

/-- A fixed regular boundary point admits a compact inverse-chart ball
inside any prescribed physical neighborhood, with real derivative constants
through order three for both the chart and its inverse. -/
theorem exists_quantitative_regularLevelFlattening_bounds {w : KernelSpace n → ℝ}
    (hw : ContDiff ℝ ∞ w) (a : KernelSpace n) (j : Fin n)
    (hj : fderiv ℝ w a (EuclideanSpace.basisFun (Fin n) ℝ j) ≠ 0)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ s C : ℝ, 0 < s ∧ s ≤ 1 ∧ 1 ≤ C ∧
      (∀ z ∈ Metric.closedBall (0 : KernelSpace n) (2*s),
        z ∈ (regularLevelFlatteningChart hw a j hj).target ∧
        ContDiffAt ℝ ∞ (regularLevelFlatteningChart hw a j hj).symm z ∧
        dist ((regularLevelFlatteningChart hw a j hj).symm z) a < ρ/2 ∧
        w ((regularLevelFlatteningChart hw a j hj).symm z)=w a-z j ∧
        ThreeDerivativeBound (regularLevelFlatteningChart hw a j hj).symm z C) ∧
      (∀ x ∈ Metric.closedBall a ρ,
        ThreeDerivativeBound (flatteningMap w a j) x C ∧ ThreeDerivativeBound w x C) := by
  let Ψ := regularLevelFlatteningChart hw a j hj
  let g := Ψ.symm
  obtain ⟨R,hR,hchart⟩ := exists_regularLevelFlattening_inverse_ball hw a j hj
  have hInv : ContDiffOn ℝ ∞ g (Metric.ball (0:KernelSpace n) R) :=
    fun z hz => (hchart z hz).2.1.contDiffWithinAt
  have hg0 : g 0=a := regularLevelFlatteningChart_symm_zero hw a j hj
  have hgc : ContinuousAt g (0:KernelSpace n) :=
    Ψ.continuousAt_symm (regularLevelFlatteningChart_target hw a j hj)
  have hnear : ∀ᶠ z in 𝓝 (0:KernelSpace n), dist (g z) a < ρ/2 :=
    (hgc.dist continuousAt_const).eventually (eventually_lt_nhds (by rw [hg0]; simpa using half_pos hρ))
  obtain ⟨η,hη,hηball⟩ := Metric.eventually_nhds_iff.mp hnear
  let s := min 1 (min (R/4) (η/4))
  have hs : 0 < s := by dsimp only [s]; positivity
  have hs1 : s ≤ 1 := min_le_left _ _
  have hsR : s ≤ R/4 := (min_le_right _ _).trans (min_le_left _ _)
  have hsη : s ≤ η/4 := (min_le_right _ _).trans (min_le_right _ _)
  have hball (z : KernelSpace n) (hz : z ∈ Metric.closedBall (0:KernelSpace n) (2*s)) :
      z ∈ Metric.ball (0:KernelSpace n) R := by
    change dist z 0 < R
    change dist z 0 ≤ 2*s at hz
    linarith
  have hphysical (z : KernelSpace n) (hz : z ∈ Metric.closedBall (0:KernelSpace n) (2*s)) :
      dist (g z) a < ρ/2 := by
    apply hηball
    change dist z 0 ≤ 2*s at hz
    linarith
  obtain ⟨C₁,hC₁,hInvBound⟩ := exists_three_derivative_bound_on_compact Metric.isOpen_ball hInv
    (isCompact_closedBall (0:KernelSpace n) (2*s)) hball
  obtain ⟨C₂,hC₂,hForward⟩ := exists_three_derivative_bound_on_compact isOpen_univ
    (contDiff_flatteningMap hw a j).contDiffOn (isCompact_closedBall a ρ) (subset_univ _)
  obtain ⟨C₃,hC₃,hDefining⟩ := exists_three_derivative_bound_on_compact isOpen_univ hw.contDiffOn
    (isCompact_closedBall a ρ) (subset_univ _)
  let C := max C₁ (max C₂ C₃)
  have hC₁C : C₁ ≤ C := le_max_left _ _
  have hC₂C : C₂ ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hC₃C : C₃ ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨s,C,hs,hs1,hC₁.trans hC₁C,?_,?_⟩
  · intro z hz
    have hh := hchart z (hball z hz)
    exact ⟨hh.1,hh.2.1,hphysical z hz,hh.2.2,(hInvBound z hz).mono hC₁C⟩
  · intro x hx
    exact ⟨(hForward x hx).mono hC₂C,(hDefining x hx).mono hC₃C⟩

end GaussianTilt.MomentMapLinearDirichlet
