import GaussianTilt.MomentMapHolderEllipticOperator

/-! # Actual zero-boundary jet supremum and coercive estimates -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 500000
open Set Matrix
open scoped Topology BoundedContinuousFunction ContDiff
namespace GaussianTilt.HolderSpace
open GaussianTilt.Letwin GaussianTilt.MomentMapRegularity
variable {n : ℕ}

def coefficientExtension {S : Set (Coord (n := n))} (α : ℝ)
    (A : Fin n → Fin n → Space S ℝ α) (x : Coord (n := n)) : Matrix (Fin n) (Fin n) ℝ :=
  fun i k => extendValue α (A i k) x

lemma coefficientExtension_mem {S : Set (Coord (n := n))} (α : ℝ)
    (A : Fin n → Fin n → Space S ℝ α) (x : S) :
    coefficientExtension α A x = fun i k => value S ℝ α (A i k) x := by
  ext i k
  exact extendValue_mem α (A i k) x.2

/-- The actual classical maximum/barrier principle supplies the C⁰ inverse
bound for the literal Hölder-jet operator. -/
theorem ellipticDirichletOperator_value_norm_le_barrier [NeZero n]
    {S : Set (Coord (n := n))} (hS : Convex ℝ S) (hSc : IsCompact S)
    {α : ℝ} (hα : 0 < α) (A : Fin n → Fin n → Space S ℝ α)
    (hA : ∀ x ∈ interior S, (coefficientExtension α A x).PosDef)
    {w : Coord → ℝ} (hwc : ContinuousOn w S)
    (hw : ∀ x ∈ interior S, ContDiffAt ℝ 2 w x)
    (hwlap : ∀ x ∈ interior S, 1 ≤ linearizedMA (coefficientExtension α A x) w x)
    (hwb : ∀ x ∈ frontier S, w x ≤ 0)
    {B : ℝ} (hB : 0 ≤ B) (hwB : ∀ x ∈ S, |w x| ≤ B)
    (j : zeroBoundary Coord ℝ hS α) :
    ‖value S ℝ α (jetValue Coord ℝ hS α j.1)‖ ≤ B * ‖ellipticDirichletOperator hS α A j‖ := by
  let u := extendValue α (jetValue Coord ℝ hS α j.1)
  let M := ‖ellipticDirichletOperator hS α A j‖
  have hu : ∀ x ∈ interior S, ContDiffAt ℝ 2 u x := fun x hx =>
    (jet_contDiffOn_two hS hα j.1).contDiffAt (isOpen_interior.mem_nhds hx)
  have hLu (x : Coord) (hx : x ∈ interior S) :
      |linearizedMA (coefficientExtension α A x) u x| ≤ M := by
    let z : S := ⟨x, interior_subset hx⟩
    have he := ellipticDirichletOperator_eq_actual hS hα A j z hx
    rw [← coefficientExtension_mem α A z] at he
    rw [← he]
    exact norm_value_apply_le S ℝ α (ellipticDirichletOperator hS α A j) z
  have hb := classical_dirichlet_barrier_bound hSc (continuousOn_extendValue α _) hwc
    hu hw hA (norm_nonneg _) hLu hwlap (fun x hx => zeroBoundary_value hS hSc.isClosed α j hx) hwb
  apply (BoundedContinuousFunction.norm_le (mul_nonneg hB (norm_nonneg _))).mpr
  intro x
  have huB := hb x x.2
  rw [extendValue_mem α _ x.2] at huB
  change |value S ℝ α (jetValue Coord ℝ hS α j.1) x| ≤ B * M
  have hwlow := (abs_le.mp (hwB x x.2)).1
  nlinarith [norm_nonneg (ellipticDirichletOperator hS α A j)]

/-- A genuine global Schauder estimate and the actual barrier estimate
combine into the coercive bound required by linear continuation. -/
theorem ellipticDirichletOperator_coercive_of_schauder_and_barrier [NeZero n]
    {S : Set (Coord (n := n))} (hS : Convex ℝ S) (hSc : IsCompact S)
    {α : ℝ} (hα : 0 < α) (A : Fin n → Fin n → Space S ℝ α)
    (hA : ∀ x ∈ interior S, (coefficientExtension α A x).PosDef)
    {w : Coord → ℝ} (hwc : ContinuousOn w S)
    (hw : ∀ x ∈ interior S, ContDiffAt ℝ 2 w x)
    (hwlap : ∀ x ∈ interior S, 1 ≤ linearizedMA (coefficientExtension α A x) w x)
    (hwb : ∀ x ∈ frontier S, w x ≤ 0)
    {B K : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K) (hwB : ∀ x ∈ S, |w x| ≤ B)
    (hschauder : ∀ j : zeroBoundary Coord ℝ hS α,
      ‖j‖ ≤ K * (‖value S ℝ α (jetValue Coord ℝ hS α j.1)‖ +
        ‖ellipticDirichletOperator hS α A j‖)) :
    ∀ j : zeroBoundary Coord ℝ hS α,
      ‖j‖ ≤ (K * (B + 1)) * ‖ellipticDirichletOperator hS α A j‖ := by
  intro j
  have hu := ellipticDirichletOperator_value_norm_le_barrier hS hSc hα A hA hwc hw hwlap hwb hB hwB j
  have hg := hschauder j
  nlinarith

end GaussianTilt.HolderSpace
