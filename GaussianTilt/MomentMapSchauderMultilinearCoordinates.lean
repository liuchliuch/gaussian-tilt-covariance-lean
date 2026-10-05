import GaussianTilt.MomentMapSchauderJetReconstruction

/-! # Finite-basis reconstruction of genuine multilinear Hölder fields -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1800000
open Set
open scoped ContDiff BigOperators
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

def multilinearCoordinates (d : ℕ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin d => KernelSpace n) ℝ →L[ℝ] ((Fin d → Fin n) → ℝ) :=
  ContinuousLinearMap.pi (fun q => ContinuousMultilinearMap.apply ℝ (fun _ : Fin d => KernelSpace n) ℝ
    (fun i => EuclideanSpace.basisFun (Fin n) ℝ (q i)))

lemma multilinearCoordinates_injective (d : ℕ) : Function.Injective (multilinearCoordinates (n := n) d) := by
  intro B C hBC
  have he : B.toMultilinearMap=C.toMultilinearMap :=
    Module.Basis.ext_multilinear (fun _ : Fin d => (EuclideanSpace.basisFun (Fin n) ℝ).toBasis)
      (fun q => congrFun hBC q)
  apply ContinuousMultilinearMap.ext
  intro v
  exact congrArg (fun M => M v) he

/-- A finite basis controls the actual multilinear operator norm. The
constant is derived from finite dimensionality and injectivity of the
explicit evaluation map, not assumed as a tensor norm comparison. -/
theorem exists_multilinear_coordinate_bound (d : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ B : ContinuousMultilinearMap ℝ (fun _ : Fin d => KernelSpace n) ℝ,
      ‖B‖ ≤ K*‖multilinearCoordinates d B‖ := by
  let L := multilinearCoordinates (n := n) d
  have hi : Function.Injective L := multilinearCoordinates_injective d
  letI : FiniteDimensional ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin d => KernelSpace n) ℝ) :=
    FiniteDimensional.of_injective L.toLinearMap hi
  obtain ⟨K, hK, hb⟩ := L.toLinearMap.injective_iff_antilipschitz.mp hi
  refine ⟨K, by exact_mod_cast hK, ?_⟩
  intro B
  simpa only [dist_zero_right, map_zero] using AntilipschitzWith.le_mul_dist hb B 0

/-- Actual multilinear-map Hölder control follows from the finitely many
canonical-basis coefficient fields. -/
theorem boundedHolderOn_multilinear_of_basis {E : Type*} [NormedAddCommGroup E]
    {α : ℝ} {S : Set E} (d : ℕ)
    {f : E → ContinuousMultilinearMap ℝ (fun _ : Fin d => KernelSpace n) ℝ}
    (hf : ∀ q : Fin d → Fin n, BoundedHolderOn α
      (fun x => f x (fun i => EuclideanSpace.basisFun (Fin n) ℝ (q i))) S) :
    BoundedHolderOn α f S := by
  obtain ⟨K, hK, hKb⟩ := exists_multilinear_coordinate_bound (n := n) d
  obtain ⟨C, hC, hb, hh⟩ := BoundedHolderOn.pi hf
  refine ⟨K*C, by positivity, ?_, ?_⟩
  · intro x hx
    exact (hKb (f x)).trans (mul_le_mul_of_nonneg_left (hb x hx) hK.le)
  · intro x hx y hy
    have he : multilinearCoordinates d (f x-f y)=multilinearCoordinates d (f x)-multilinearCoordinates d (f y) := map_sub _ _ _
    have hdiff := hKb (f x-f y)
    rw [he] at hdiff
    exact hdiff.trans ((mul_le_mul_of_nonneg_left (hh x hx y hy) hK.le).trans_eq (by ring))

/-- Finitely many local Hölder fields share one common positive radius.
This combines real local estimates; it does not impose a uniform modulus
on an infinite family of directions. -/
theorem exists_common_closedBall_holder {E F ι : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F] [Fintype ι]
    {α : ℝ} {f : ι → E → F} (a : E)
    (hf : ∀ i, ∃ r : ℝ, 0 < r ∧ BoundedHolderOn α (f i) (Metric.closedBall a r)) :
    ∃ r : ℝ, 0 < r ∧ ∀ i, BoundedHolderOn α (f i) (Metric.closedBall a r) := by
  classical
  choose r hr hh using hf
  let D := (∑ i, (r i)⁻¹)+1
  have hsum : 0 ≤ ∑ i, (r i)⁻¹ := Finset.sum_nonneg (fun i _ => inv_nonneg.mpr (hr i).le)
  have hD : 0 < D := by dsimp [D]; linarith
  refine ⟨D⁻¹, inv_pos.mpr hD, ?_⟩
  intro i
  have hi : (r i)⁻¹ ≤ D :=
    (Finset.single_le_sum (fun j _ => inv_nonneg.mpr (hr j).le) (Finset.mem_univ i)).trans
      (by dsimp [D]; linarith)
  have hi' : D⁻¹ ≤ r i := by
    simpa only [inv_inv] using (inv_le_inv₀ hD (inv_pos.mpr (hr i))).mpr hi
  exact (hh i).mono (Metric.closedBall_subset_closedBall hi')

end GaussianTilt.MomentMapSchauder
