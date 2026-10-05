import GaussianTilt.MomentMapClassicalDirichletUniformEllipticity
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli

/-! # Actual lower-order compactness for classical Dirichlet solutions -/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff NNReal
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

/-- Arzelà--Ascoli applied to an actual uniformly bounded Lipschitz family. -/
theorem exists_uniform_subsequence_of_lipschitzOn
    {X F : Type*} [MetricSpace X] [NormedAddCommGroup F] [ProperSpace F]
    {S : Set X} (hS : IsCompact S) {f : ℕ → X → F} {L : ℝ≥0} {B : ℝ}
    (hL : ∀ k, LipschitzOnWith L (f k) S) (hB : ∀ k, ∀ x ∈ S, ‖f k x‖ ≤ B) :
    ∃ j : ℕ → ℕ, StrictMono j ∧ ∃ g : X → F,
      ContinuousOn g S ∧ TendstoUniformlyOn (fun k => f (j k)) g atTop S := by
  classical
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let Fk : ℕ → BoundedContinuousFunction S F := fun k =>
    BoundedContinuousFunction.mkOfCompact ⟨fun x => f k x, (hL k).continuousOn.restrict⟩
  have heq : Equicontinuous (fun f : Set.range Fk => fun x : S => f.val x) := by
    intro x
    apply Metric.equicontinuousAt_iff.mpr
    intro ε hε
    let δ := ε/((L:ℝ)+1)
    have hden : 0 < (L:ℝ)+1 := by positivity
    refine ⟨δ,div_pos hε hden,?_⟩
    intro y hy f
    obtain ⟨k,hk⟩ := f.property
    rw [← hk]
    have hdist := (hL k).dist_le_mul x x.property y y.property
    change dist (Fk k x) (Fk k y) < ε
    apply hdist.trans_lt
    have ht : ((L:ℝ)+1)*dist (x:X) (y:X) < ε := by
      have hh := (lt_div_iff₀ hden).mp hy
      simpa only [Subtype.dist_eq,dist_comm,mul_comm] using hh
    nlinarith [(show 0 ≤ dist (x:X) (y:X) from dist_nonneg)]
  have hcompact : IsCompact (closure (Set.range Fk)) :=
    BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0:F) B) (isCompact_closedBall _ _)
      (Set.range Fk) (by
        rintro f x ⟨k,rfl⟩
        simpa only [Metric.mem_closedBall,dist_zero_right] using hB k x x.property) heq
  obtain ⟨g,_,j,hj,hlim⟩ := hcompact.tendsto_subseq (fun k => subset_closure (mem_range_self k))
  have huni : TendstoUniformly (fun k => fun x : S => Fk (j k) x) g atTop :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hlim
  let u : X → F := fun x => if hx : x ∈ S then g ⟨x,hx⟩ else 0
  have he (x : X) (hx : x ∈ S) : u x = g ⟨x,hx⟩ := dif_pos hx
  have huc : ContinuousOn u S := by
    rw [continuousOn_iff_continuous_restrict]
    convert g.continuous using 1
    ext x
    exact he x x.property
  refine ⟨j,hj,u,huc,?_⟩
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.mp huni ε hε] with k hk
  intro x hx
  simpa only [he x hx] using hk ⟨x,hx⟩

/-- The actual coordinate differential is a continuous linear function of
its coordinate gradient, in the ordinary finite-dimensional coordinate norm. -/
def coordinateCovector : CoordinateSpace n →L[ℝ] (CoordinateSpace n →L[ℝ] ℝ) :=
  ∑ i : Fin n, (ContinuousLinearMap.proj i : CoordinateSpace n →L[ℝ] ℝ).smulRight
    (ContinuousLinearMap.proj i : CoordinateSpace n →L[ℝ] ℝ)

lemma coordinateCovector_apply (g v : CoordinateSpace n) :
    coordinateCovector g v = ∑ i, g i*v i := by
  simp [coordinateCovector]

lemma coordinateCovector_gradient (f : CoordinateSpace n → ℝ) (x : CoordinateSpace n) :
    coordinateCovector (coordinateGradient f x) = fderiv ℝ f x := by
  ext v
  rw [coordinateCovector_apply,fderiv_apply_eq_sum_coordinates]
  simp only [coordinateGradient,mul_comm]

lemma norm_fderiv_le_of_coordinate_bound {f : CoordinateSpace n → ℝ} {x : CoordinateSpace n}
    {G : ℝ} (hG : 0 ≤ G) (hg : ∀ i, |coordinateDerivative i f x| ≤ G) :
    ‖fderiv ℝ f x‖ ≤ (n:ℝ)*G := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Nat.cast_nonneg _) hG)
  intro v
  rw [Real.norm_eq_abs,fderiv_apply_eq_sum_coordinates]
  calc
    _ ≤ ∑ i, |v i*coordinateDerivative i f x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, (‖v‖*G) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul (norm_le_pi_norm v i) (hg i) (abs_nonneg _) (norm_nonneg _)
    _ = _ := by simp; ring

lemma lipschitzOn_coordinateGradient_of_hessian_bound {S : Set (CoordinateSpace n)}
    (hS : Convex ℝ S) {u : CoordinateSpace n → ℝ} (hu : ContDiff ℝ ∞ u)
    {K : ℝ≥0} (hH : ∀ x ∈ S, ∀ i j, |coordinateHessian u x i j| ≤ K) :
    LipschitzOnWith ((n:ℝ≥0)*K) (coordinateGradient u) S := by
  have hcoord (i : Fin n) : LipschitzOnWith ((n:ℝ≥0)*K) (coordinateDerivative i u) S := by
    apply hS.lipschitzOnWith_of_nnnorm_fderiv_le
      (fun x _ => (smooth_coordinateDerivative hu i).differentiable (by simp) x)
    intro x hx
    exact_mod_cast norm_fderiv_le_of_coordinate_bound K.coe_nonneg (fun j => hH x hx i j)
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  apply (dist_pi_le_iff (mul_nonneg (by positivity) dist_nonneg)).mpr
  intro i
  exact (hcoord i).dist_le_mul x hx y hy

end GaussianTilt.MomentMapRegularity
