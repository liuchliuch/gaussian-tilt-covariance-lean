import GaussianTilt.MomentMapBoundaryRegularityQuotientScaling
import GaussianTilt.MomentMapBoundaryRegularityLocalContraction

/-!
# Genuine local-domain boundary quotient Hölder decay

The oscillation is the literal supremum minus infimum over source points.
Only interior smoothness and closed-half-ball continuity are assumed.
Its contraction comes from the proved elliptic equation, Harnack, and Hopf
barriers. The forcing is retained through the geometric iteration.
-/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

theorem exists_local_flat_boundary_quotient_holder [NeZero n] {lam Λ K : ℝ}
    (hlam : 0 < lam) (hΛ : 0 ≤ Λ) (hK : 0 ≤ K) :
    ∃ α ε₀ : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 < ε₀ ∧
      ∀ (j : Fin n) (u f : CoordinateSpace n → ℝ) (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
        (M B : ℝ),
      0 ≤ M → 0 ≤ B → LocalFlatEllipticSystem j u f A lam Λ K M →
      (∀ x, ‖(coordinateEquiv n).symm x‖ ≤ 1 → 0 ≤ x j → |u x| ≤ B*x j) →
      ∀ r ∈ Ioc (0:ℝ) 1,
        boundaryQuotientOscillation u j r ≤ 8*(2*B+M/ε₀)*r^α := by
  obtain ⟨δ,ε₀,hδ,hδ1,hε,hcontract⟩ := exists_local_flat_boundary_slope_contraction (n := n) hlam hΛ hK
  let q := 1-δ
  have hq : (1/2:ℝ) ≤ q := by dsimp [q]; linarith
  have hq1 : q < 1 := by dsimp [q]; linarith
  let α := oscillationExponent (1/8) q
  have hα : 0 < α := oscillationExponent_pos (by norm_num) (by norm_num) (by linarith) hq1
  have hα1 : α ≤ 1 := oscillationExponent_le_one (by norm_num) (by norm_num) (by linarith)
  refine ⟨α,ε₀,hα,hα1,hε,?_⟩
  intro j u f A M B hM hB hs hb
  have hstep : ∀ r ∈ Ioc (0:ℝ) 1,
      boundaryQuotientOscillation u j (r/8) ≤ q*boundaryQuotientOscillation u j r+(M/ε₀)*r := by
    intro r hr
    have hsr := hs.rescale hr.1 hr.2
    let v := flatRescaledSolution u r
    let g := flatRescaledForcing f r
    let Ar := fun y => A (r • y)
    have hvb := flatRescaledSolution_quotient_bound hr.1 hr.2 hb
    let a := sInf (boundaryQuotientValues v j 1)
    let b := sSup (boundaryQuotientValues v j 1)
    have hbd := boundaryQuotientValues_bounded (r := 1) le_rfl hvb
    have hab : a ≤ b := csInf_le_csSup hbd.1 hbd.2 (boundaryQuotientValues_nonempty v j zero_lt_one)
    have hrange := boundaryQuotient_ball_bounds (r := 1) le_rfl hvb
    obtain ⟨a',b',_,_,_,hwidth,hbounds⟩ := hcontract j v g Ar
      (r*M) a b (mul_nonneg hr.1.le hM) hab hsr hrange
    have ho := (boundaryQuotientOscillation_le_interval (by norm_num : (0:ℝ)<1/8) hbounds).trans hwidth
    change boundaryQuotientOscillation (flatRescaledSolution u r) j (1/8) ≤
      q*boundaryQuotientOscillation (flatRescaledSolution u r) j 1+(r*M)/ε₀ at ho
    rw [boundaryQuotientOscillation_rescale u j hr.1, boundaryQuotientOscillation_rescale u j hr.1, mul_one] at ho
    convert ho using 1 <;> ring
  have hit := eighth_scale_forced_oscillation_holder hq hq1 (div_nonneg hM hε.le)
    (boundaryQuotientOscillation_nonneg zero_lt_one le_rfl hb)
    (boundaryQuotientOscillation_mono hb) hstep
  have hω1 : boundaryQuotientOscillation u j 1 ≤ 2*B := by
    have hh := boundaryQuotientOscillation_le_interval (u := u) (j := j) zero_lt_one
      (a := -B) (b := B) (fun x hx hj => by
        have hbound := abs_le.mp (hb x hx hj)
        exact ⟨by nlinarith [hbound.1],hbound.2⟩)
    nlinarith
  intro r hr
  exact (hit.2.2 r hr).trans (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hr.1.le _))

end GaussianTilt.MomentMapRegularity
