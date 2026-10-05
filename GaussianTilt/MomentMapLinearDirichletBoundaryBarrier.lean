import GaussianTilt.MomentMapLinearDirichletSmoothBarrier
import GaussianTilt.EllipticRegularityCutoffs

/-!
# Actual boundary barriers for the constructed weak Laplace inverse

A global smooth barrier is localized without changing it near the bounded
domain. This gives one- and two-sided pointwise-almost-everywhere bounds
for the genuine weak solution. A strictly subharmonic defining function
then bounds the solution right up to its zero boundary.
-/
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin
variable {n : ℕ}

lemma euclideanLaplacian_congr_nhds {f g : CoordinateSpace n → ℝ} {x : CoordinateSpace n}
    (h : f =ᶠ[𝓝 x] g) : euclideanLaplacian f x = euclideanLaplacian g x := by
  apply Finset.sum_congr rfl
  intro i _
  have hi : coordinateDerivative i f =ᶠ[𝓝 x] coordinateDerivative i g :=
    h.fderiv.mono (fun y hy => congrArg (fun A : CoordinateSpace n →L[ℝ] ℝ => A (Pi.single i 1)) hy)
  exact congrArg (fun A : CoordinateSpace n →L[ℝ] ℝ => A (Pi.single i 1)) hi.fderiv_eq

lemma exists_compact_smooth_agree_near_bounded {Ω : Set (CoordinateSpace n)}
    (hΩ : Bornology.IsBounded Ω) {b : CoordinateSpace n → ℝ} (hb : ContDiff ℝ ∞ b) :
    ∃ c : smoothCompactCore n, ∀ x ∈ closure Ω, c.1 =ᶠ[𝓝 x] b := by
  obtain ⟨M, hM⟩ := hΩ.closure.exists_norm_le
  let R : ℝ := |M| + 1
  have hR : 0 < R := by dsimp [R]; positivity
  let c : smoothCompactCore n :=
    ⟨fun x => ellipticCutoff n R x * b x,
      (ellipticCutoff_contDiff n R).mul hb, (ellipticCutoff_compact n hR.ne').mul_right⟩
  refine ⟨c, ?_⟩
  intro x hx
  have hxR : ‖x‖ < R := by have hh := hM x hx; dsimp [R]; linarith [le_abs_self M]
  filter_upwards [continuous_norm.continuousAt.eventually (gt_mem_nhds hxR)] with y hy
  change ellipticCutoff n R y * b y = b y
  rw [ellipticCutoff_eq_one hR hy.le, one_mul]

/-- No compact-support hypothesis is needed for a genuine smooth barrier
on a bounded domain; it is derived by localization. -/
theorem weakDirichletLaplaceSolution_le_global_smooth_barrier {Ω : Set (CoordinateSpace n)}
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (i : Fin n) {R : ℝ} (hR : 0 ≤ R) (hstrip : ∀ x ∈ Ω, |x i| ≤ R)
    (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n)))
    {b : CoordinateSpace n → ℝ} (hb : ContDiff ℝ ∞ b) (hb0 : ∀ x ∈ Ω, 0 ≤ b x)
    (hforce : ∀ᵐ x ∂volume, x ∈ Ω → f x ≤ -euclideanLaplacian b x) :
    ∀ᵐ x ∂volume, x ∈ Ω →
      dirichletValue Ω (weakDirichletLaplaceSolution i hR hstrip f) x ≤ b x := by
  obtain ⟨c, hc⟩ := exists_compact_smooth_agree_near_bounded hΩb hb
  have he (x : CoordinateSpace n) (hx : x ∈ Ω) : c.1 x = b x := (hc x (subset_closure hx)).eq_of_nhds
  have hbar := weakDirichletLaplaceSolution_le_smooth_barrier hΩ hΩb i hR hstrip f c
    (fun x hx => by rw [he x hx]; exact hb0 x hx) (by
      filter_upwards [hforce] with x hx hxΩ
      rw [euclideanLaplacian_congr_nhds (hc x (subset_closure hxΩ))]
      exact hx hxΩ)
  filter_upwards [hbar] with x hx hxΩ
  exact (hx hxΩ).trans_eq (he x hxΩ)

/-- Both signs of the actual weak solution are controlled by one smooth
barrier whenever its negative Laplacian dominates the absolute load. -/
theorem weakDirichletLaplaceSolution_abs_le_global_smooth_barrier {Ω : Set (CoordinateSpace n)}
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (i : Fin n) {R : ℝ} (hR : 0 ≤ R) (hstrip : ∀ x ∈ Ω, |x i| ≤ R)
    (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n)))
    {b : CoordinateSpace n → ℝ} (hb : ContDiff ℝ ∞ b) (hb0 : ∀ x ∈ Ω, 0 ≤ b x)
    (hforce : ∀ᵐ x ∂volume, x ∈ Ω → |f x| ≤ -euclideanLaplacian b x) :
    ∀ᵐ x ∂volume, x ∈ Ω →
      |dirichletValue Ω (weakDirichletLaplaceSolution i hR hstrip f) x| ≤ b x := by
  have hupper := weakDirichletLaplaceSolution_le_global_smooth_barrier hΩ hΩb i hR hstrip f hb hb0 (by
    filter_upwards [hforce] with x hx hxΩ
    exact (le_abs_self _).trans (hx hxΩ))
  have hlower := weakDirichletLaplaceSolution_le_global_smooth_barrier hΩ hΩb i hR hstrip (-f) hb hb0 (by
    filter_upwards [hforce, Lp.coeFn_neg f] with x hx hn hxΩ
    rw [hn, Pi.neg_apply]
    exact (neg_le_abs _).trans (hx hxΩ))
  have hneg : dirichletValue Ω (weakDirichletLaplaceSolution i hR hstrip (-f)) =
      -dirichletValue Ω (weakDirichletLaplaceSolution i hR hstrip f) := by
    rw [show weakDirichletLaplaceSolution i hR hstrip (-f) =
      -weakDirichletLaplaceSolution i hR hstrip f from map_neg (weakDirichletLaplaceInverse i hR hstrip) f,
      map_neg]
  rw [hneg] at hlower
  filter_upwards [hupper, hlower, Lp.coeFn_neg (dirichletValue Ω (weakDirichletLaplaceSolution i hR hstrip f))]
    with x hu hl hn hxΩ
  rw [hn, Pi.neg_apply] at hl
  exact abs_le.mpr ⟨by linarith [hl hxΩ], hu hxΩ⟩

lemma euclideanLaplacian_const_mul (c : ℝ) {w : CoordinateSpace n → ℝ}
    (hw : ContDiff ℝ ∞ w) (x : CoordinateSpace n) :
    euclideanLaplacian (fun y => c * w y) x = c * euclideanLaplacian w x := by
  have hd {f : CoordinateSpace n → ℝ} (hf : Differentiable ℝ f) (i : Fin n) (y : CoordinateSpace n) :
      coordinateDerivative i (fun z => c * f z) y = c * coordinateDerivative i f y := by
    unfold coordinateDerivative
    rw [((hf y).hasFDerivAt.const_mul c).fderiv]
    rfl
  have h1 (i : Fin n) : coordinateDerivative i (fun y => c * w y) =
      fun y => c * coordinateDerivative i w y :=
    funext (hd (hw.differentiable (by simp)) i)
  simp only [euclideanLaplacian, h1]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact hd ((smooth_coordinateDerivative hw i).differentiable (by simp)) i x

/-- A strictly subharmonic smooth defining function supplies an actual
boundary-decaying bound for the weak Dirichlet inverse. -/
theorem weakDirichletLaplaceSolution_defining_barrier {Ω : Set (CoordinateSpace n)}
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (i : Fin n) {R : ℝ} (hR : 0 ≤ R) (hstrip : ∀ x ∈ Ω, |x i| ≤ R)
    (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n)))
    {w : CoordinateSpace n → ℝ} (hw : ContDiff ℝ ∞ w) (hw0 : ∀ x ∈ Ω, w x ≤ 0)
    {a F : ℝ} (ha : 0 < a) (hF : 0 ≤ F)
    (hwlap : ∀ x ∈ Ω, a ≤ euclideanLaplacian w x)
    (hf : ∀ᵐ x ∂volume, x ∈ Ω → |f x| ≤ F) :
    ∀ᵐ x ∂volume, x ∈ Ω →
      |dirichletValue Ω (weakDirichletLaplaceSolution i hR hstrip f) x| ≤ -(F / a) * w x := by
  apply weakDirichletLaplaceSolution_abs_le_global_smooth_barrier hΩ hΩb i hR hstrip f
    (contDiff_const.mul hw) (fun x hx => mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (div_nonneg hF ha.le)) (hw0 x hx))
  filter_upwards [hf] with x hx hxΩ
  rw [euclideanLaplacian_const_mul _ hw]
  have hmul := mul_le_mul_of_nonneg_left (hwlap x hxΩ) (div_nonneg hF ha.le)
  have he : F / a * a = F := div_mul_cancel₀ F ha.ne'
  nlinarith [hx hxΩ]

end GaussianTilt.MomentMapLinearDirichlet
