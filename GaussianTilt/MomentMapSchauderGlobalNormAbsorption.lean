import GaussianTilt.MomentMapHolderCompactSmallCover
import GaussianTilt.MomentMapSchauderGlobalJetNorm

/-! # Genuine global Schauder norm absorption from the compact local estimates

The cover radius precedes epsilon and every unknown jet. The data constant
is kept separate until after the small highest-order term is absorbed.
-/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 500000
open Set
open scoped BoundedContinuousFunction
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.HolderSpace GaussianTilt.MomentMapElliptic
variable {n : ℕ} {Γ : Type*}

theorem exists_global_jet_norm_of_local_small_hessian
    {S : Set (KernelSpace n)} (hS : Convex ℝ S) (hSc : IsCompact S)
    (hSi : (interior S).Nonempty) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (J : Γ → Jet (KernelSpace n) ℝ hS α) (P : Γ → Prop) (M : Γ → ℝ)
    (hM : ∀ g, P g → 0 ≤ M g)
    (hu : ∀ g, P g → ∀ x : S,
      |value S ℝ α (jetValue (KernelSpace n) ℝ hS α (J g)) x| ≤ M g)
    (hlocal : ∀ a ∈ S, ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ,
      0 ≤ C ∧ ∀ g, P g →
      (∀ x ∈ S, dist x a < r →
        ‖extendValue α (jetSecond (KernelSpace n) ℝ hS α (J g)) x‖ ≤ C*M g+ε*‖J g‖) ∧
      (∀ x ∈ S, dist x a < r → ∀ y ∈ S, dist y a < r →
        ‖extendValue α (jetSecond (KernelSpace n) ℝ hS α (J g)) x-
          extendValue α (jetSecond (KernelSpace n) ℝ hS α (J g)) y‖ ≤
            (C*M g+ε*‖J g‖)*dist x y^α)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g, P g → ‖J g‖ ≤ C*M g := by
  obtain ⟨B,hB,hnorm⟩ := exists_global_jet_norm_bound hS hSc hSi hα hα1
  let ε := (2*B)⁻¹
  have hε : 0 < ε := inv_pos.mpr (by positivity)
  have hBε : B*ε=1/2 := by dsimp only [ε]; field_simp
  obtain ⟨C,hC,hglobal⟩ := uniform_holder_small_highest_of_compact_local_bounds hSc hα.le
    (fun g => extendValue α (jetSecond (KernelSpace n) ℝ hS α (J g))) P M
    (fun g => ‖J g‖) hM (fun g _ => norm_nonneg (J g)) hlocal ε hε
  refine ⟨2*B*(1+C),by positivity,?_⟩
  intro g hg
  have hH : ‖jetSecond (KernelSpace n) ℝ hS α (J g)‖ ≤ C*M g+ε*‖J g‖ := by
    apply norm_le_of_value_bounds (add_nonneg (mul_nonneg hC (hM g hg))
      (mul_nonneg hε.le (norm_nonneg (J g))))
    · intro x
      have hh := (hglobal g hg).1 x x.2
      rwa [extendValue_mem α _ x.2] at hh
    · intro x y
      have hh := (hglobal g hg).2 x x.2 y y.2
      rwa [extendValue_mem α _ x.2,extendValue_mem α _ y.2] at hh
  have hstep := (hnorm (J g) (M g) (hM g hg) (hu g hg)).trans
    (mul_le_mul_of_nonneg_left (add_le_add_left hH (M g)) hB.le)
  have he : B*(M g+(C*M g+ε*‖J g‖)) = B*(1+C)*M g+(1/2)*‖J g‖ := by
    calc
      _ = B*(1+C)*M g+(B*ε)*‖J g‖ := by ring
      _ = _ := by rw [hBε]
  rw [he] at hstep
  nlinarith

end GaussianTilt.MomentMapSchauder
