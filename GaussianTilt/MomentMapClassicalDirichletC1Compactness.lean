import GaussianTilt.MomentMapClassicalDirichletSolutionCompactness

/-!
# Genuine C¹ limits of actual smooth homotopy solutions

The global C² estimate supplies a common gradient modulus. Arzelà--Ascoli
extracts value and gradient limits simultaneously, and the uniform derivative
limit theorem identifies the latter as the true derivative on the interior.
-/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff NNReal
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

lemma hasFDerivAt_of_uniform_coordinateGradient_limit
    {Ω : Set (CoordinateSpace n)} (hΩ : IsOpen Ω)
    {u : ℕ → CoordinateSpace n → ℝ} {v : CoordinateSpace n → ℝ}
    {g : CoordinateSpace n → CoordinateSpace n}
    (hu : ∀ k, DifferentiableOn ℝ (u k) Ω)
    (hv : TendstoUniformlyOn u v atTop Ω)
    (hg : TendstoUniformlyOn (fun k => coordinateGradient (u k)) g atTop Ω)
    {x : CoordinateSpace n} (hx : x ∈ Ω) :
    HasFDerivAt v (coordinateCovector (g x)) x := by
  have hD := (coordinateCovector (n := n)).uniformContinuous.comp_tendstoUniformlyOn hg
  simp only [Function.comp_def,coordinateCovector_gradient] at hD
  apply hasFDerivAt_of_tendstoUniformlyOn hΩ hD
  · intro k y hy
    exact ((hu k y hy).differentiableAt (hΩ.mem_nhds hy)).hasFDerivAt
  · exact fun y hy => hv.tendsto_at hy
  · exact hx

lemma coordinateGradient_of_uniform_limit
    {Ω : Set (CoordinateSpace n)} (hΩ : IsOpen Ω)
    {u : ℕ → CoordinateSpace n → ℝ} {v : CoordinateSpace n → ℝ}
    {g : CoordinateSpace n → CoordinateSpace n}
    (hu : ∀ k, DifferentiableOn ℝ (u k) Ω)
    (hv : TendstoUniformlyOn u v atTop Ω)
    (hg : TendstoUniformlyOn (fun k => coordinateGradient (u k)) g atTop Ω)
    {x : CoordinateSpace n} (hx : x ∈ Ω) : coordinateGradient v x = g x := by
  ext i
  change fderiv ℝ v x (Pi.single i 1) = g x i
  rw [(hasFDerivAt_of_uniform_coordinateGradient_limit hΩ hu hv hg hx).fderiv,
    coordinateCovector_apply]
  simp [Pi.single_apply]

namespace SmoothInnerDomain
variable {S A : Set (E n)} (d : SmoothInnerDomain S A)

/-- Every sequence of genuine smooth solutions in the actual homotopy has
uniform value and gradient limits on the full body. The limit is genuinely
C¹ in the interior and retains its true zero boundary values. -/
theorem exists_C1_dirichlet_subsequence [NeZero n]
    {t : ℕ → ℝ} (ht : ∀ k, t k ∈ Icc (0:ℝ) 1)
    {u : ℕ → CoordinateSpace n → ℝ} (hu : ∀ k, ContDiff ℝ ∞ (u k))
    (hH : ∀ k, ∀ x ∈ interior {y | d.coordinateDefining y ≤ 0}, (coordinateHessian (u k) x).PosDef)
    (hub : ∀ k, ∀ x ∈ frontier {y | d.coordinateDefining y ≤ 0}, u k x = 0)
    (hMA : ∀ k, ∀ x ∈ interior {y | d.coordinateDefining y ≤ 0},
      (coordinateHessian (u k) x).det = dirichletContinuationDensity d.coordinateDefining (t k) x) :
    ∃ j : ℕ → ℕ, StrictMono j ∧ ∃ v : CoordinateSpace n → ℝ,
      ∃ g : CoordinateSpace n → CoordinateSpace n,
      ContinuousOn v {y | d.coordinateDefining y ≤ 0} ∧
      ContinuousOn g {y | d.coordinateDefining y ≤ 0} ∧
      (∀ x ∈ frontier {y | d.coordinateDefining y ≤ 0}, v x = 0) ∧
      TendstoUniformlyOn (fun k => u (j k)) v atTop {y | d.coordinateDefining y ≤ 0} ∧
      TendstoUniformlyOn (fun k => coordinateGradient (u (j k))) g atTop {y | d.coordinateDefining y ≤ 0} ∧
      ContDiffOn ℝ 1 v (interior {y | d.coordinateDefining y ≤ 0}) ∧
      ∀ x ∈ interior {y | d.coordinateDefining y ≤ 0}, HasFDerivAt v (coordinateCovector (g x)) x := by
  obtain ⟨B₀,hB₀,hval⟩ := dirichletContinuation_uniform_C0_bound d.coordinate_body_compact
    d.coordinate_body_nonempty d.coordinateDefining_smooth
    (fun x _ => d.coordinateDefining_hessian_posDef x) d.coordinate_zero_boundary
  obtain ⟨G,hG,hgrad⟩ := d.dirichletContinuation_uniform_coordinate_gradient
  obtain ⟨K,hK,hhess⟩ := d.dirichletContinuation_uniform_hessian
  let G' : ℝ≥0 := ⟨G,hG⟩
  let K' : ℝ≥0 := ⟨K,hK⟩
  have hgv (k : ℕ) := hgrad (t k) (ht k) (u k) (hu k) (hH k) (hub k) (hMA k)
  have hhv (k : ℕ) := hhess (t k) (ht k) (u k) (hu k) (hH k) (hub k) (hMA k)
  have hLip (k : ℕ) : LipschitzOnWith ((n:ℝ≥0)*G') (u k) {y | d.coordinateDefining y ≤ 0} := by
    apply d.coordinate_body_convex.lipschitzOnWith_of_nnnorm_fderiv_le
      (fun x _ => (hu k).differentiable (by simp) x)
    intro x hx
    exact_mod_cast norm_fderiv_le_of_coordinate_bound hG (hgv k x hx)
  have hLipG (k : ℕ) : LipschitzOnWith ((n:ℝ≥0)*K') (coordinateGradient (u k)) {y | d.coordinateDefining y ≤ 0} :=
    lipschitzOn_coordinateGradient_of_hessian_bound d.coordinate_body_convex (hu k) (hhv k)
  have hbounded (k : ℕ) (x : CoordinateSpace n) (hx : d.coordinateDefining x ≤ 0) :
      ‖(u k x, coordinateGradient (u k) x)‖ ≤ max B₀ G := by
    rw [Prod.norm_def]
    apply max_le_max
    · exact hval (t k) (ht k) (u k) (hu k).continuous.continuousOn
        (fun _ _ => (contDiff_infty.mp (hu k) 2).contDiffAt) (hH k) (hub k) (hMA k) x hx
    · exact (pi_norm_le_iff_of_nonneg hG).mpr (hgv k x hx)
  obtain ⟨j,hj,f,hfc,hlim⟩ := exists_uniform_subsequence_of_lipschitzOn d.coordinate_body_compact
    (fun k => (hLip k).prodMk (hLipG k)) hbounded
  have hv : TendstoUniformlyOn (fun k => u (j k)) (fun x => (f x).1) atTop {y | d.coordinateDefining y ≤ 0} :=
    uniformContinuous_fst.comp_tendstoUniformlyOn hlim
  have hg : TendstoUniformlyOn (fun k => coordinateGradient (u (j k))) (fun x => (f x).2) atTop {y | d.coordinateDefining y ≤ 0} :=
    uniformContinuous_snd.comp_tendstoUniformlyOn hlim
  have hD (x : CoordinateSpace n) (hx : x ∈ interior {y | d.coordinateDefining y ≤ 0}) :
      HasFDerivAt (fun x => (f x).1) (coordinateCovector ((f x).2)) x :=
    hasFDerivAt_of_uniform_coordinateGradient_limit isOpen_interior
      (fun k => (hu (j k)).differentiable (by simp) |>.differentiableOn)
      (hv.mono interior_subset) (hg.mono interior_subset) hx
  refine ⟨j,hj,(fun x => (f x).1),(fun x => (f x).2),hfc.fst,hfc.snd,?_,hv,hg,?_,hD⟩
  · intro x hx
    have hzero : Tendsto (fun k => u (j k) x) atTop (𝓝 0) := by
      simp_rw [hub _ x hx]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique (hv.tendsto_at (d.coordinate_body_compact.isClosed.frontier_subset hx)) hzero
  · rw [show (1:WithTop ℕ∞) = 0+1 from rfl,contDiffOn_succ_iff_fderiv_of_isOpen isOpen_interior]
    refine ⟨fun x hx => (hD x hx).differentiableAt.differentiableWithinAt,by simp,?_⟩
    rw [contDiffOn_zero]
    exact ((coordinateCovector (n := n)).continuous.comp_continuousOn
      (hfc.snd.mono interior_subset)).congr (fun x hx => (hD x hx).fderiv)

end SmoothInnerDomain
end GaussianTilt.MomentMapRegularity
