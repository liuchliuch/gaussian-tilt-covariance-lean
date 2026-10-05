import GaussianTilt.MomentMapLinearDirichletBoundaryInteriorEnergyBridge
import GaussianTilt.MomentMapLinearDirichletFrozenExcessEnergy

/-! # Uniform all-center Campanato estimates from actual boundary and interior balls

The radius and constant are fixed before the field. Balls whose radius is
large compared with height are contained in an actual projected boundary
ball, so the interior starting scale never introduces a height singularity.
-/
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma upperBall_subset_projected_of_height_le (j : Fin n) (x : KernelSpace n)
    (hx : 0 ≤ x j) {η r : ℝ} (hη : 0 < η) (hh : η*x j ≤ r) :
    upperCampanatoBall j x r ⊆ upperCampanatoBall j
      (x-x j • EuclideanSpace.basisFun (Fin n) ℝ j) ((1+η⁻¹)*r) := by
  apply upperCampanatoBall_mono
  have hd : dist x (x-x j • EuclideanSpace.basisFun (Fin n) ℝ j) = x j := by
    rw [dist_eq_norm,sub_sub_cancel,norm_smul,Real.norm_eq_abs,abs_of_nonneg hx,
      (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.norm_eq_one,mul_one]
  rw [hd]
  have h := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hη.le)
  have he : η⁻¹*(η*x j)=x j := by field_simp
  rw [he] at h
  nlinarith

theorem exists_uniform_boundary_interior_campanato_cover_with_formulas
    {η R Cb Ci β : ℝ} (hη : 0 < η) (hR : 0 < R)
    (hCb : 0 ≤ Cb) (hCi : 0 ≤ Ci) :
    ∃ r₀ C : ℝ, r₀=R/(1+η⁻¹) ∧ C=max Ci (Cb*(1+η⁻¹)^((n:ℝ)+β)) ∧
      0 < r₀ ∧ 0 ≤ C ∧
      ∀ (j : Fin n) (W Z : Set (KernelSpace n)) (G : KernelSpace n → KernelSpace n),
      MemLp G 2 volume →
      (∀ x ∈ W, 0 ≤ x j) →
      (∀ x ∈ W, (x-x j • EuclideanSpace.basisFun (Fin n) ℝ j) ∈ Z) →
      (∀ z ∈ Z, ∀ s : ℝ, 0 < s → s ≤ R → ∃ p : KernelSpace n,
        (∫ y in upperCampanatoBall j z s, ‖G y-p‖^2) ≤ Cb*s^((n:ℝ)+β)) →
      (∀ x ∈ W, ∀ r : ℝ, 0 < r → r ≤ η*x j → ∃ p : KernelSpace n,
        (∫ y in Metric.ball x r, ‖G y-p‖^2) ≤ Ci*r^((n:ℝ)+β)) →
      ∀ x ∈ W, ∀ r : ℝ, 0 < r → r ≤ r₀ → ∃ p : KernelSpace n,
        (∫ y in upperCampanatoBall j x r, ‖G y-p‖^2) ≤ C*r^((n:ℝ)+β) := by
  let L := 1+η⁻¹
  have hL : 0 < L := by dsimp [L]; positivity
  let C := max Ci (Cb*L^((n:ℝ)+β))
  have hC : 0 ≤ C := hCi.trans (le_max_left _ _)
  refine ⟨R/L,C,rfl,rfl,div_pos hR hL,hC,?_⟩
  intro j W Z G hG hW hZ hb hi x hx r hr hrr
  by_cases hh : r ≤ η*x j
  · obtain ⟨p,hp⟩ := hi x hx r hr hh
    refine ⟨p,?_⟩
    have hm := fieldExcess_mono_set hG (show volume (Metric.ball x r) < ∞ from measure_ball_lt_top)
      (show upperCampanatoBall j x r ⊆ Metric.ball x r from inter_subset_left) p
    exact hm.trans (hp.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg hr.le _)))
  · have hs : L*r ≤ R := by nlinarith [(le_div_iff₀ hL).mp hrr]
    obtain ⟨p,hp⟩ := hb _ (hZ x hx) (L*r) (mul_pos hL hr) hs
    refine ⟨p,?_⟩
    have hsub := upperBall_subset_projected_of_height_le j x (hW x hx) hη (lt_of_not_ge hh).le
    have hm := fieldExcess_mono_set hG
      (upperCampanatoBall_finite j (x-x j • EuclideanSpace.basisFun (Fin n) ℝ j) (L*r)).lt_top hsub p
    have he : Cb*(L*r)^((n:ℝ)+β) = (Cb*L^((n:ℝ)+β))*r^((n:ℝ)+β) := by
      rw [Real.mul_rpow hL.le hr.le]
      ring
    rw [he] at hp
    exact hm.trans (hp.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (Real.rpow_nonneg hr.le _)))

/-- Explicit radius and constant version, convenient when both comparison
constants carry a common solution-energy factor. -/
theorem boundary_interior_campanato_cover_explicit
    {η R Cb Ci β : ℝ} (hη : 0 < η) (hR : 0 < R) (hCb : 0 ≤ Cb) (hCi : 0 ≤ Ci)
    (j : Fin n) (W Z : Set (KernelSpace n)) (G : KernelSpace n → KernelSpace n)
    (hG : MemLp G 2 volume)
    (hW : ∀ x ∈ W, 0 ≤ x j)
    (hZ : ∀ x ∈ W, (x-x j • EuclideanSpace.basisFun (Fin n) ℝ j) ∈ Z)
    (hb : ∀ z ∈ Z, ∀ s : ℝ, 0 < s → s ≤ R → ∃ p : KernelSpace n,
      (∫ y in upperCampanatoBall j z s, ‖G y-p‖^2) ≤ Cb*s^((n:ℝ)+β))
    (hi : ∀ x ∈ W, ∀ r : ℝ, 0 < r → r ≤ η*x j → ∃ p : KernelSpace n,
      (∫ y in Metric.ball x r, ‖G y-p‖^2) ≤ Ci*r^((n:ℝ)+β)) :
    ∀ x ∈ W, ∀ r : ℝ, 0 < r → r ≤ R/(1+η⁻¹) → ∃ p : KernelSpace n,
      (∫ y in upperCampanatoBall j x r, ‖G y-p‖^2) ≤
        max Ci (Cb*(1+η⁻¹)^((n:ℝ)+β))*r^((n:ℝ)+β) := by
  obtain ⟨r₀,C,hr,hC,_,_,h⟩ := exists_uniform_boundary_interior_campanato_cover_with_formulas (n:=n) hη hR hCb hCi
  subst r₀; subst C
  exact h j W Z G hG hW hZ hb hi

end GaussianTilt.MomentMapLinearDirichlet
