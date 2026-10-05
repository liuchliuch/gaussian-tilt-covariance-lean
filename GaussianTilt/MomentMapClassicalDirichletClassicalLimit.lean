import GaussianTilt.MomentMapClassicalDirichletInteriorThirdBounds

/-!
# Actual classical interior limits along the forcing homotopy

Global C¹ compactness and genuine local Calabi bounds identify the true
second derivative of the limit and preserve the literal determinant equation.
No boundary Hölder regularity or continuation solvability is claimed here.
-/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff NNReal
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

lemma posSemidef_of_tendsto_matrices {H : ℕ → Matrix (Fin n) (Fin n) ℝ}
    {M : Matrix (Fin n) (Fin n) ℝ} (hs : M.IsSymm)
    (hH : ∀ k, (H k).PosSemidef) (hlim : Tendsto H atTop (𝓝 M)) : M.PosSemidef := by
  refine ⟨?_,fun v => ?_⟩
  · simpa only [Matrix.IsSymm,Matrix.IsHermitian,Matrix.conjTranspose_eq_transpose_of_trivial] using hs
  · have hc : Continuous (fun N : Matrix (Fin n) (Fin n) ℝ => v ⬝ᵥ (N *ᵥ v)) := by
      unfold dotProduct Matrix.mulVec
      fun_prop
    have ht := (hc.tendsto M).comp hlim
    have hpos : ∀ᶠ k in atTop, 0 ≤ v ⬝ᵥ (H k *ᵥ v) :=
      Eventually.of_forall (fun k => by simpa only [star_trivial] using (hH k).2 v)
    simpa only [star_trivial] using ge_of_tendsto ht hpos

lemma lipschitzOn_limit_of_pointwise {X F : Type*} [PseudoMetricSpace X] [PseudoMetricSpace F]
    {S : Set X} {f : ℕ → X → F} {g : X → F} {L : ℝ≥0}
    (hL : ∀ k, LipschitzOnWith L (f k) S)
    (hlim : ∀ x ∈ S, Tendsto (fun k => f k x) atTop (𝓝 (g x))) : LipschitzOnWith L g S := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  exact le_of_tendsto ((hlim x hx).dist (hlim y hy))
    (Eventually.of_forall (fun k => (hL k).dist_le_mul x hx y hy))

namespace SmoothInnerDomain
variable {S A : Set (E n)} (d : SmoothInnerDomain S A)

/-- The already fixed C¹ limit of genuine smooth solutions is genuinely C²
at every interior point, and satisfies the actual limiting determinant
identity with a positive definite Hessian. -/
theorem classical_interior_limit_of_C1_convergence [NeZero n]
    {t : ℕ → ℝ} {τ : ℝ} (ht : ∀ k, t k ∈ Icc (0:ℝ) 1) (htlim : Tendsto t atTop (𝓝 τ))
    {u : ℕ → CoordinateSpace n → ℝ} (hu : ∀ k, ContDiff ℝ ∞ (u k))
    (hH : ∀ k, ∀ x ∈ interior {y | d.coordinateDefining y ≤ 0}, (coordinateHessian (u k) x).PosDef)
    (hub : ∀ k, ∀ x ∈ frontier {y | d.coordinateDefining y ≤ 0}, u k x = 0)
    (hMA : ∀ k, ∀ x ∈ interior {y | d.coordinateDefining y ≤ 0},
      (coordinateHessian (u k) x).det = dirichletContinuationDensity d.coordinateDefining (t k) x)
    {v : CoordinateSpace n → ℝ} {g : CoordinateSpace n → CoordinateSpace n}
    (hv : TendstoUniformlyOn u v atTop {y | d.coordinateDefining y ≤ 0})
    (hg : TendstoUniformlyOn (fun k => coordinateGradient (u k)) g atTop {y | d.coordinateDefining y ≤ 0}) :
    ContDiffOn ℝ 2 v (interior {y | d.coordinateDefining y ≤ 0}) ∧
      ∀ x ∈ interior {y | d.coordinateDefining y ≤ 0},
        (coordinateHessian v x).PosDef ∧
        (coordinateHessian v x).det = dirichletContinuationDensity d.coordinateDefining τ x := by
  have hτ : τ ∈ Icc (0:ℝ) 1 := isClosed_Icc.mem_of_tendsto htlim (Eventually.of_forall ht)
  obtain ⟨K,hK,hKH⟩ := d.dirichletContinuation_uniform_hessian
  have hpoint (x : CoordinateSpace n) (hx : x ∈ interior {y | d.coordinateDefining y ≤ 0}) :
      ContDiffAt ℝ 2 v x ∧ (coordinateHessian v x).PosDef ∧
        (coordinateHessian v x).det = dirichletContinuationDensity d.coordinateDefining τ x := by
    obtain ⟨r,T,hr,hT,hinside,hthird⟩ := d.dirichletContinuation_local_uniform_third_bound hx
    let K' : ℝ≥0 := ⟨K,hK⟩
    let T' : ℝ≥0 := ⟨T,hT⟩
    have hSub : Metric.closedBall x r ⊆ {y | d.coordinateDefining y ≤ 0} := hinside.trans interior_subset
    have hbounds (k : ℕ) (y : CoordinateSpace n) (hy : y ∈ Metric.closedBall x r) :
        ∀ i j, |coordinateHessian (u k) y i j| ≤ K' :=
      hKH (t k) (ht k) (u k) (hu k) (hH k) (hub k) (hMA k) y (hSub hy)
    have hthird' (k : ℕ) (y : CoordinateSpace n) (hy : y ∈ Metric.closedBall x r) :
        ∀ i j l, |coordinateThirdDerivative (u k) y i j l| ≤ T' :=
      hthird (t k) (ht k) (u k) (hu k) (hH k) (hub k) (hMA k) y hy
    obtain ⟨j,hj,H,hHc,hHlim,hv2,hHeq⟩ := exists_local_hessian_subsequence
      (isCompact_closedBall x r) (convex_closedBall x r) hu (hv.mono hSub) (hg.mono hSub) hbounds hthird'
    have hxball : x ∈ Metric.closedBall x r := Metric.mem_closedBall_self hr.le
    have hxint : x ∈ interior (Metric.closedBall x r) :=
      Metric.ball_subset_interior_closedBall (Metric.mem_ball_self hr)
    have hv2x := hv2.contDiffAt (isOpen_interior.mem_nhds hxint)
    have hmat : Tendsto (fun k => coordinateHessian (u (j k)) x) atTop (𝓝 (coordinateHessian v x)) := by
      rw [hHeq x hxint]
      exact hHlim.tendsto_at hxball
    have hdetlim := (continuous_id.matrix_det.tendsto (coordinateHessian v x)).comp hmat
    have hparam : Continuous (fun s : ℝ => dirichletContinuationDensity d.coordinateDefining s x) := by
      unfold dirichletContinuationDensity
      fun_prop
    have hrhs := (hparam.tendsto τ).comp (htlim.comp hj.tendsto_atTop)
    have hdet : (coordinateHessian v x).det = dirichletContinuationDensity d.coordinateDefining τ x := by
      apply tendsto_nhds_unique hdetlim
      convert hrhs using 1
      ext k
      exact hMA (j k) x hx
    have hps : (coordinateHessian v x).PosSemidef :=
      posSemidef_of_tendsto_matrices (coordinateHessian_isSymm_at hv2x)
        (fun k => (hH (j k) x hx).posSemidef) hmat
    have hpd : (coordinateHessian v x).PosDef := posDef_of_posSemidef_det_ne_zero hps (by
      rw [hdet]
      exact (dirichletContinuationDensity_pos hτ (d.coordinateDefining_hessian_posDef x)).ne')
    exact ⟨hv2x,hpd,hdet⟩
  exact ⟨fun x hx => (hpoint x hx).1.contDiffWithinAt,fun x hx => (hpoint x hx).2⟩

/-- A real subsequential classical interior limit exists for every convergent
sequence of parameters and genuine smooth solutions. -/
theorem exists_classical_dirichlet_limit [NeZero n]
    {t : ℕ → ℝ} {τ : ℝ} (ht : ∀ k, t k ∈ Icc (0:ℝ) 1) (htlim : Tendsto t atTop (𝓝 τ))
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
      ContDiffOn ℝ 2 v (interior {y | d.coordinateDefining y ≤ 0}) ∧
      ∀ x ∈ interior {y | d.coordinateDefining y ≤ 0},
        (coordinateHessian v x).PosDef ∧
        (coordinateHessian v x).det = dirichletContinuationDensity d.coordinateDefining τ x := by
  obtain ⟨j,hj,v,g,hvc,hgc,hvb,hv,hg,hv1,hD⟩ := d.exists_C1_dirichlet_subsequence ht hu hH hub hMA
  have hclass := d.classical_interior_limit_of_C1_convergence (fun k => ht (j k))
    (htlim.comp hj.tendsto_atTop) (fun k => hu (j k)) (fun k => hH (j k))
    (fun k => hub (j k)) (fun k => hMA (j k)) hv hg
  exact ⟨j,hj,v,g,hvc,hgc,hvb,hv,hg,hclass.1,hclass.2⟩

end SmoothInnerDomain
end GaussianTilt.MomentMapRegularity
