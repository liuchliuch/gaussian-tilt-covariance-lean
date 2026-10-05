import GaussianTilt.MomentMapLinearDirichletWeak

/-!
# Weak derivatives and the actual distributional Dirichlet equation

The zero-boundary Hilbert jets satisfy literal integration by parts against
all compact smooth tests. Consequently their value coordinate is injective,
and the constructed inverse solves the actual local distributional equation
`-Δu=f`, not merely an abstract Hilbert-space equation.
-/
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin
variable {n : ℕ}

lemma smoothCompact_unweighted_integration_by_parts (f g : smoothCompactCore n) (i : Fin n) :
    inner ℝ (smoothCompactToL2 volume (smoothCompactDerivative i f)) (smoothCompactToL2 volume g) =
      -inner ℝ (smoothCompactToL2 volume f) (smoothCompactToL2 volume (smoothCompactDerivative i g)) := by
  have hfg : Integrable (fun x => f.1 x * g.1 x) :=
    (f.2.1.continuous.mul g.2.1.continuous).integrable_of_hasCompactSupport f.2.2.mul_right
  have hdfg : Integrable (fun x => coordinateDerivative i f.1 x * g.1 x) :=
    ((smooth_coordinateDerivative f.2.1 i).continuous.mul g.2.1.continuous).integrable_of_hasCompactSupport g.2.2.mul_left
  have hfdg : Integrable (fun x => f.1 x * coordinateDerivative i g.1 x) :=
    (f.2.1.continuous.mul (smooth_coordinateDerivative g.2.1 i).continuous).integrable_of_hasCompactSupport f.2.2.mul_right
  have hh := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (v := Pi.single i 1)
    hdfg hfdg hfg (f.2.1.differentiable (by simp)) (g.2.1.differentiable (by simp))
  rw [inner_smoothCompactToL2, inner_smoothCompactToL2]
  change (∫ x, coordinateDerivative i f.1 x * g.1 x) = -(∫ x, f.1 x * coordinateDerivative i g.1 x)
  change (∫ x, f.1 x * coordinateDerivative i g.1 x) = -(∫ x, coordinateDerivative i f.1 x * g.1 x) at hh
  linarith

/-- Actual weak coordinate derivatives on the closed zero-boundary space. -/
theorem dirichletSobolev_integration_by_parts {Ω : Set (CoordinateSpace n)}
    (u : dirichletSobolev Ω) (i : Fin n) (g : smoothCompactCore n) :
    inner ℝ (u.1 i.succ) (smoothCompactToL2 volume g) =
      -inner ℝ (u.1 0) (smoothCompactToL2 volume (smoothCompactDerivative i g)) := by
  let μ : Measure (CoordinateSpace n) := volume
  have hclosed : IsClosed {v : SobolevJet μ |
      inner ℝ (v i.succ) (smoothCompactToL2 μ g) =
        -inner ℝ (v 0) (smoothCompactToL2 μ (smoothCompactDerivative i g))} :=
    isClosed_eq
      ((PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin (n + 1) => Lp ℝ 2 μ) i.succ).continuous.inner continuous_const)
      (((PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin (n + 1) => Lp ℝ 2 μ) 0).continuous.inner continuous_const).neg)
  have hcore : (LinearMap.range (dirichletJet Ω) : Set (SobolevJet μ)) ⊆
      {v | inner ℝ (v i.succ) (smoothCompactToL2 μ g) =
        -inner ℝ (v 0) (smoothCompactToL2 μ (smoothCompactDerivative i g))} := by
    rintro _ ⟨f, rfl⟩
    exact smoothCompact_unweighted_integration_by_parts f.1 g i
  exact (closure_minimal hcore hclosed) u.2

/-- No spurious derivative coordinates occur in the Dirichlet completion. -/
theorem dirichletSobolev_eq_zero_of_value_eq_zero {Ω : Set (CoordinateSpace n)}
    (u : dirichletSobolev Ω) (hu : dirichletValue Ω u = 0) : u = 0 := by
  have h0 : u.1 0 = 0 := hu
  have hd (i : Fin n) : u.1 i.succ = 0 := by
    have heq : (fun v : Lp ℝ 2 (volume : Measure (CoordinateSpace n)) => inner ℝ (u.1 i.succ) v) = fun _ => 0 := by
      apply (continuous_const.inner continuous_id).ext_on (smoothCompactToL2_dense (volume : Measure (CoordinateSpace n))) continuous_const
      rintro _ ⟨g, rfl⟩
      change inner ℝ (u.1 i.succ) (smoothCompactToL2 volume g) = 0
      rw [dirichletSobolev_integration_by_parts u i g, h0, inner_zero_left, neg_zero]
    have hz := congrFun heq (u.1 i.succ)
    exact inner_self_eq_zero.mp hz
  apply Subtype.ext
  apply PiLp.ext
  intro i
  exact Fin.cases h0 hd i

lemma dirichletValue_injective (Ω : Set (CoordinateSpace n)) : Function.Injective (dirichletValue Ω) := by
  intro u v huv
  apply sub_eq_zero.mp
  apply dirichletSobolev_eq_zero_of_value_eq_zero
  rw [map_sub, huv, sub_self]

/-- The literal Laplacian of a genuine smooth compact test. -/
def laplaceCore (g : smoothCompactCore n) : smoothCompactCore n :=
  ⟨euclideanLaplacian g.1, smooth_euclideanLaplacian g.2.1, euclideanLaplacian_compact g.2.2⟩

lemma laplaceCore_eq_sum (g : smoothCompactCore n) :
    laplaceCore g = ∑ i : Fin n, smoothCompactDerivative i (smoothCompactDerivative i g) := by
  apply Subtype.ext
  funext x
  simp only [laplaceCore, euclideanLaplacian, Submodule.coe_sum, Finset.sum_apply]
  rfl

lemma inner_Lp_smoothCompactToL2 (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n))) (g : smoothCompactCore n) :
    inner ℝ f (smoothCompactToL2 volume g) = ∫ x, f x * g.1 x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [smoothCompactToL2_ae volume g] with x hx
  simp only [hx, RCLike.inner_apply, conj_trivial]
  ring

/-- The actual distributional integration by parts for a closed H₀¹ jet. -/
theorem dirichletSobolev_laplacian_pairing {Ω : Set (CoordinateSpace n)}
    (u : dirichletSobolev Ω) (g : smoothCompactCore n) :
    (∑ i : Fin n, inner ℝ (u.1 i.succ) (smoothCompactToL2 volume (smoothCompactDerivative i g))) =
      -(∫ x, (dirichletValue Ω u) x * euclideanLaplacian g.1 x) := by
  simp_rw [dirichletSobolev_integration_by_parts]
  rw [Finset.sum_neg_distrib, ← inner_sum, ← map_sum, ← laplaceCore_eq_sum,
    inner_Lp_smoothCompactToL2]
  rfl

/-- The constructed weak inverse solves `-Δu=f` against every actual
compact smooth test supported inside the domain. -/
theorem weakDirichletLaplaceSolution_distribution {Ω : Set (CoordinateSpace n)} (i : Fin n)
    {R : ℝ} (hR : 0 ≤ R) (hΩ : ∀ x ∈ Ω, |x i| ≤ R)
    (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n)))
    {ψ : CoordinateSpace n → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψs : HasCompactSupport ψ)
    (hψΩ : tsupport ψ ⊆ Ω) :
    (∫ x, (dirichletValue Ω (weakDirichletLaplaceSolution i hR hΩ f)) x * euclideanLaplacian ψ x) =
      -(∫ x, f x * ψ x) := by
  let g : smoothCompactCore n := ⟨ψ, hψ, hψs⟩
  let v : dirichletSobolev Ω := dirichletCoreToSobolev Ω ⟨g, hψΩ⟩
  have hh := weakDirichletLaplaceSolution_coordinates i hR hΩ f v
  have he : (∑ j : Fin n, inner ℝ ((weakDirichletLaplaceSolution i hR hΩ f).1 j.succ)
      (smoothCompactToL2 volume (smoothCompactDerivative j g))) =
      inner ℝ f (smoothCompactToL2 volume g) := hh
  rw [dirichletSobolev_laplacian_pairing, inner_Lp_smoothCompactToL2] at he
  change -(∫ x, (dirichletValue Ω (weakDirichletLaplaceSolution i hR hΩ f)) x * euclideanLaplacian ψ x) =
    (∫ x, f x * ψ x) at he
  linarith

end GaussianTilt.MomentMapLinearDirichlet
