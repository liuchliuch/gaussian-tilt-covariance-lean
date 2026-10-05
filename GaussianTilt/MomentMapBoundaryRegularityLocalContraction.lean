import GaussianTilt.MomentMapBoundaryRegularityLocalPositivity
import GaussianTilt.MomentMapBoundaryRegularityLocalOperations

/-! # Actual intrinsic-domain boundary quotient contraction -/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

theorem exists_local_flat_boundary_quotient_contraction [NeZero n] {lam Λ K : ℝ}
    (hlam : 0 < lam) (hΛ : 0 ≤ Λ) (hK : 0 ≤ K) :
    ∃ δ ε₀ : ℝ, 0 < δ ∧ δ ≤ 1/2 ∧ 0 < ε₀ ∧
      ∀ (j : Fin n) (v f : CoordinateSpace n → ℝ) (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ),
      LocalFlatEllipticSystem j v f A lam Λ K ε₀ →
      (∀ y, ‖(coordinateEquiv n).symm y‖ ≤ 1 → 0 ≤ y j → 0 ≤ v y ∧ v y ≤ y j) →
      ∃ a b : ℝ, 0 ≤ a ∧ a ≤ b ∧ b ≤ 1 ∧ b-a ≤ 1-δ ∧
        ∀ x, ‖(coordinateEquiv n).symm x‖ ≤ 1/8 → 0 ≤ x j → a*x j ≤ v x ∧ v x ≤ b*x j := by
  obtain ⟨δ,ε₀,hδ,hδ1,hε,hpos⟩ := exists_local_flat_boundary_positivity (n := n) hlam hΛ hK
  refine ⟨δ,ε₀,hδ,hδ1,hε,?_⟩
  intro j v f A hs hrange
  by_cases hcorn : 1/8 ≤ v (Pi.single j (1/4))
  · have hlower := hpos j v f A hs (fun y hy hj => (hrange y hy hj).1) hcorn
    refine ⟨δ,1,hδ.le,by linarith,le_rfl,le_rfl,?_⟩
    intro x hx hj
    exact ⟨hlower x hx hj,by simpa only [one_mul] using (hrange x (by linarith) hj).2⟩
  · let w := fun y : CoordinateSpace n => (-1:ℝ)*(v y-y j)
    let g := fun y : CoordinateSpace n => (-1:ℝ)*f y
    have hws : LocalFlatEllipticSystem j w g A lam Λ K ε₀ := by
      simpa only [one_mul,abs_neg,abs_one] using hs.affine_shift_scale (-1) 1
    have hn (y : CoordinateSpace n) (hy : ‖(coordinateEquiv n).symm y‖ ≤ 1) (hj : 0 ≤ y j) : 0 ≤ w y := by
      have hh := (hrange y hy hj).2
      dsimp only [w]
      linarith
    have hwcorn : 1/8 ≤ w (Pi.single j (1/4)) := by
      dsimp only [w]
      simp only [Pi.single_eq_same]
      linarith
    have hlower := hpos j w g A hws hn hwcorn
    refine ⟨0,1-δ,le_rfl,by linarith,by linarith,by simp,?_⟩
    intro x hx hj
    have hl := hlower x hx hj
    change δ*x j ≤ (-1:ℝ)*(v x-x j) at hl
    exact ⟨by simpa only [zero_mul] using (hrange x (by linarith) hj).1,by nlinarith⟩

theorem exists_local_flat_boundary_slope_contraction [NeZero n] {lam Λ K : ℝ}
    (hlam : 0 < lam) (hΛ : 0 ≤ Λ) (hK : 0 ≤ K) :
    ∃ δ ε₀ : ℝ, 0 < δ ∧ δ ≤ 1/2 ∧ 0 < ε₀ ∧
      ∀ (j : Fin n) (u f : CoordinateSpace n → ℝ) (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
        (M a b : ℝ), 0 ≤ M → a ≤ b → LocalFlatEllipticSystem j u f A lam Λ K M →
      (∀ y, ‖(coordinateEquiv n).symm y‖ ≤ 1 → 0 ≤ y j → a*y j ≤ u y ∧ u y ≤ b*y j) →
      ∃ a' b' : ℝ, a ≤ a' ∧ a' ≤ b' ∧ b' ≤ b ∧ b'-a' ≤ (1-δ)*(b-a)+M/ε₀ ∧
        ∀ x, ‖(coordinateEquiv n).symm x‖ ≤ 1/8 → 0 ≤ x j → a'*x j ≤ u x ∧ u x ≤ b'*x j := by
  obtain ⟨δ,ε₀,hδ,hδ1,hε,hcontract⟩ := exists_local_flat_boundary_quotient_contraction (n := n) hlam hΛ hK
  refine ⟨δ,ε₀,hδ,hδ1,hε,?_⟩
  intro j u f A M a b hM hab hs hrange
  by_cases hsmall : b-a ≤ M/ε₀
  · refine ⟨a,b,le_rfl,hab,le_rfl,by nlinarith,?_⟩
    intro x hx hj
    exact hrange x (by linarith) hj
  · let W := b-a
    have hW : 0 < W := lt_of_le_of_lt (div_nonneg hM hε.le) (lt_of_not_ge hsmall)
    have hMW : M/W ≤ ε₀ := by
      apply (div_le_iff₀ hW).mpr
      have hh := (div_lt_iff₀ hε).mp (lt_of_not_ge hsmall)
      dsimp only [W]
      linarith
    let v := fun y => W⁻¹*(u y-a*y j)
    let g := fun y => W⁻¹*f y
    have hvSys : LocalFlatEllipticSystem j v g A lam Λ K ε₀ := by
      apply (hs.affine_shift_scale W⁻¹ a).mono_forcing
      rw [abs_of_pos (inv_pos.mpr hW)]
      simpa only [div_eq_mul_inv,mul_comm] using hMW
    have hvbound (y : CoordinateSpace n) (hy : ‖(coordinateEquiv n).symm y‖ ≤ 1) (hj : 0 ≤ y j) :
        0 ≤ v y ∧ v y ≤ y j := by
      have h := hrange y hy hj
      have he : W*v y=u y-a*y j := by dsimp only [v]; field_simp
      have hWj : W*y j=b*y j-a*y j := by dsimp only [W]; ring
      constructor <;> nlinarith
    obtain ⟨α,β,hα,hαβ,hβ,hwidth,hbound⟩ := hcontract j v g A hvSys hvbound
    refine ⟨a+W*α,a+W*β,by nlinarith,by nlinarith,?_,?_,?_⟩
    · dsimp only [W]
      nlinarith
    · have hh := mul_le_mul_of_nonneg_left hwidth hW.le
      have hnon := div_nonneg hM hε.le
      dsimp only [W] at hh ⊢
      nlinarith
    · intro x hx hj
      have hb := hbound x hx hj
      have he : W*v x=u x-a*x j := by dsimp only [v]; field_simp
      have hlo := mul_le_mul_of_nonneg_left hb.1 hW.le
      have hup := mul_le_mul_of_nonneg_left hb.2 hW.le
      constructor <;> nlinarith

end GaussianTilt.MomentMapRegularity
