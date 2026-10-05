import GaussianTilt.MomentMapClassicalDirichletC1Compactness

/-! # Actual local Hessian compactness and derivative identification -/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff NNReal
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

lemma lipschitzOn_hessian_of_third_bound {S : Set (CoordinateSpace n)} (hS : Convex ℝ S)
    {u : CoordinateSpace n → ℝ} (hu : ContDiff ℝ ∞ u) {K : ℝ≥0}
    (hT : ∀ x ∈ S, ∀ i j k, |coordinateThirdDerivative u x i j k| ≤ K) :
    LipschitzOnWith ((n:ℝ≥0)*K) (fun x => fun i j : Fin n => coordinateHessian u x i j) S := by
  have hcoord (i j : Fin n) : LipschitzOnWith ((n:ℝ≥0)*K) (fun x => coordinateHessian u x i j) S := by
    apply hS.lipschitzOnWith_of_nnnorm_fderiv_le
      (fun x _ => (smooth_coordinateHessian hu i j).differentiable (by simp) x)
    intro x hx
    exact_mod_cast norm_fderiv_le_of_coordinate_bound K.coe_nonneg (fun k => hT x hx i j k)
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  apply (dist_pi_le_iff (mul_nonneg (by positivity) dist_nonneg)).mpr
  intro i
  apply (dist_pi_le_iff (mul_nonneg (by positivity) dist_nonneg)).mpr
  intro j
  exact (hcoord i j).dist_le_mul x hx y hy

lemma tendstoUniformlyOn_subsequence {X F : Type*} [UniformSpace F]
    {S : Set X} {f : ℕ → X → F} {g : X → F}
    (h : TendstoUniformlyOn f g atTop S) {j : ℕ → ℕ} (hj : StrictMono j) :
    TendstoUniformlyOn (fun k => f (j k)) g atTop S :=
  fun V hV => hj.tendsto_atTop.eventually (h V hV)

/-- True local C² regularity and Hessian identification from local compact
third-derivative bounds and the already fixed C¹ limits. -/
theorem exists_local_hessian_subsequence
    {S : Set (CoordinateSpace n)} (hS : IsCompact S) (hSc : Convex ℝ S)
    {u : ℕ → CoordinateSpace n → ℝ} (hu : ∀ k, ContDiff ℝ ∞ (u k))
    {v : CoordinateSpace n → ℝ} {g : CoordinateSpace n → CoordinateSpace n}
    (hv : TendstoUniformlyOn u v atTop S)
    (hg : TendstoUniformlyOn (fun k => coordinateGradient (u k)) g atTop S)
    {K T : ℝ≥0}
    (hH : ∀ k, ∀ x ∈ S, ∀ i j, |coordinateHessian (u k) x i j| ≤ K)
    (hT : ∀ k, ∀ x ∈ S, ∀ i j l, |coordinateThirdDerivative (u k) x i j l| ≤ T) :
    ∃ j : ℕ → ℕ, StrictMono j ∧ ∃ H : CoordinateSpace n → Fin n → Fin n → ℝ,
      ContinuousOn H S ∧
      TendstoUniformlyOn (fun k => fun x => fun i l : Fin n => coordinateHessian (u (j k)) x i l) H atTop S ∧
      ContDiffOn ℝ 2 v (interior S) ∧ ∀ x ∈ interior S, coordinateHessian v x = H x := by
  have hLip (k : ℕ) := lipschitzOn_hessian_of_third_bound hSc (hu k) (hT k)
  have hnorm (k : ℕ) (x : CoordinateSpace n) (hx : x ∈ S) :
      ‖fun i l : Fin n => coordinateHessian (u k) x i l‖ ≤ K := by
    apply (pi_norm_le_iff_of_nonneg K.coe_nonneg).mpr
    intro i
    exact (pi_norm_le_iff_of_nonneg K.coe_nonneg).mpr (hH k x hx i)
  obtain ⟨j,hj,H,hHc,hHlim⟩ := exists_uniform_subsequence_of_lipschitzOn hS hLip hnorm
  have hvj := tendstoUniformlyOn_subsequence hv hj
  have hgj := tendstoUniformlyOn_subsequence hg hj
  have hgi (i : Fin n) : TendstoUniformlyOn (fun k => coordinateDerivative i (u (j k)))
      (fun x => g x i) atTop S :=
    (ContinuousLinearMap.proj i : CoordinateSpace n →L[ℝ] ℝ).uniformContinuous.comp_tendstoUniformlyOn hgj
  have hHi (i : Fin n) : TendstoUniformlyOn
      (fun k => coordinateGradient (coordinateDerivative i (u (j k))))
      (fun x => H x i) atTop S :=
    (ContinuousLinearMap.proj i : (Fin n → CoordinateSpace n) →L[ℝ] CoordinateSpace n).uniformContinuous.comp_tendstoUniformlyOn hHlim
  have hDi (i : Fin n) (x : CoordinateSpace n) (hx : x ∈ interior S) :
      HasFDerivAt (fun x => g x i) (coordinateCovector (H x i)) x :=
    hasFDerivAt_of_uniform_coordinateGradient_limit isOpen_interior
      (fun k => (smooth_coordinateDerivative (hu (j k)) i).differentiable (by simp) |>.differentiableOn)
      ((hgi i).mono interior_subset) ((hHi i).mono interior_subset) hx
  have hg1 : ContDiffOn ℝ 1 g (interior S) := by
    apply contDiffOn_pi.mpr
    intro i
    rw [show (1:WithTop ℕ∞) = 0+1 from rfl,contDiffOn_succ_iff_fderiv_of_isOpen isOpen_interior]
    refine ⟨fun x hx => (hDi i x hx).differentiableAt.differentiableWithinAt,by simp,?_⟩
    rw [contDiffOn_zero]
    exact ((coordinateCovector (n := n)).continuous.comp_continuousOn
      ((continuousOn_pi.mp hHc i).mono interior_subset)).congr (fun x hx => (hDi i x hx).fderiv)
  have hD (x : CoordinateSpace n) (hx : x ∈ interior S) : HasFDerivAt v (coordinateCovector (g x)) x :=
    hasFDerivAt_of_uniform_coordinateGradient_limit isOpen_interior
      (fun k => (hu (j k)).differentiable (by simp) |>.differentiableOn)
      (hvj.mono interior_subset) (hgj.mono interior_subset) hx
  have hv2 : ContDiffOn ℝ 2 v (interior S) := by
    rw [show (2:WithTop ℕ∞) = 1+1 from rfl,contDiffOn_succ_iff_fderiv_of_isOpen isOpen_interior]
    refine ⟨fun x hx => (hD x hx).differentiableAt.differentiableWithinAt,by simp,?_⟩
    exact ((coordinateCovector (n := n)).contDiff.comp_contDiffOn hg1).congr
      (fun x hx => (hD x hx).fderiv)
  refine ⟨j,hj,H,hHc,hHlim,hv2,?_⟩
  intro x hx
  ext i l
  have he : coordinateDerivative i v =ᶠ[𝓝 x] (fun y => g y i) := by
    filter_upwards [isOpen_interior.mem_nhds hx] with y hy
    exact congrFun (coordinateGradient_of_uniform_limit isOpen_interior
      (fun k => (hu (j k)).differentiable (by simp) |>.differentiableOn)
      (hvj.mono interior_subset) (hgj.mono interior_subset) hy) i
  change coordinateDerivative l (coordinateDerivative i v) x = H x i l
  rw [coordinateDerivative_congr_nhds he]
  change fderiv ℝ (fun y => g y i) x (Pi.single l 1) = _
  rw [(hDi i x hx).fderiv,coordinateCovector_apply]
  simp [Pi.single_apply]

end GaussianTilt.MomentMapRegularity
