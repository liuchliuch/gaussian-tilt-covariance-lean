import GaussianTilt.MomentMapSchauderLinearDifferences

/-! # Derived compact bounds for C¹ coefficient fields -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
open Matrix Set
open scoped ContDiff Matrix.Norms.Elementwise
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma continuous_matrix_of_contDiff_entries {A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, ContDiff ℝ 1 (fun x => A x i j)) : Continuous A :=
  continuous_pi (fun i => continuous_pi (fun j => (hA i j).continuous))

theorem exists_C1_matrix_bounds_on_compact_convex
    {A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, ContDiff ℝ 1 (fun x => A x i j))
    {S : Set (KernelSpace n)} (hS : IsCompact S) (hSc : Convex ℝ S)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ M D K : ℝ, 0 < M ∧ 0 < D ∧ 0 < K ∧
      (∀ x ∈ S, ∀ i j, |A x i j| ≤ M) ∧
      (∀ x ∈ S, ∀ i j, ‖fderiv ℝ (fun z => A z i j) x‖ ≤ D) ∧
      (∀ x ∈ S, ∀ y ∈ S, ∀ i j, |A x i j-A y i j| ≤ K*‖x-y‖^α) := by
  let DA : KernelSpace n → Matrix (Fin n) (Fin n) (KernelSpace n →L[ℝ] ℝ) :=
    fun x i j => fderiv ℝ (fun z => A z i j) x
  have hc : Continuous DA := continuous_pi (fun i => continuous_pi (fun j =>
    ((hA i j).fderiv_right (m := 0) (by norm_num)).continuous))
  obtain ⟨m, hm⟩ := hS.exists_bound_of_continuousOn (continuous_matrix_of_contDiff_entries hA).continuousOn
  obtain ⟨d, hd⟩ := hS.exists_bound_of_continuousOn hc.continuousOn
  let M := max m 1
  let D := max d 1
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hb : ∀ x ∈ S, ∀ i j, |A x i j| ≤ M := by
    intro x hx i j
    have hh := Matrix.norm_entry_le_entrywise_sup_norm (A x) (i := i) (j := j)
    rw [Real.norm_eq_abs] at hh
    exact hh.trans ((hm x hx).trans (le_max_left _ _))
  have hDb : ∀ x ∈ S, ∀ i j, ‖fderiv ℝ (fun z => A z i j) x‖ ≤ D := by
    intro x hx i j
    exact (Matrix.norm_entry_le_entrywise_sup_norm (DA x) (i := i) (j := j)).trans
      ((hd x hx).trans (le_max_left _ _))
  refine ⟨M, D, D+2*M, hM, hD, by positivity, hb, hDb, ?_⟩
  intro x hx y hy i j
  have hLip : ∀ z ∈ S, ∀ w ∈ S, ‖A z i j-A w i j‖ ≤ D*‖z-w‖ := by
    intro z hz w hw
    exact Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun p _ => (hA i j).differentiable le_rfl p) (fun p hp => hDb p hp i j) hSc hw hz
  have hh := holder_bound_of_sup_and_lipschitz hM.le hD.le hα hα1 zero_lt_one
    (fun z hz => by simpa only [Real.norm_eq_abs] using hb z hz i j) hLip x hx y hy
  simpa only [Real.norm_eq_abs, Real.one_rpow, mul_one] using hh

end GaussianTilt.MomentMapSchauder
