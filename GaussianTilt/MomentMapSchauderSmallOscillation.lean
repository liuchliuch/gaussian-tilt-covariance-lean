import GaussianTilt.MomentMapSchauderEuclideanFreezing
import GaussianTilt.MomentMapSchauderAbsorption

/-!
# A genuine small-oscillation variable-coefficient Schauder estimate

The proved constant-coefficient theorem and actual Hessian interpolation give
strict improvement of every admissible Hessian Hölder constant. Geometric
iteration absorbs the initial constant, without assuming it is a minimal
seminorm. Thus the final estimate is independent of the initial C²,α bound.
-/
noncomputable section
open Matrix Set MeasureTheory
open scoped BigOperators ContDiff
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

set_option maxHeartbeats 2400000 in
/-- Actual compact-support variable-coefficient a-priori Schauder estimate
when the coefficient oscillation is small around one elliptic matrix. The
constant is uniform over all admissible matrices and potentials. An initial
finite C²,α modulus is absorbed completely from the final estimate. -/
theorem exists_small_oscillation_schauder [NeZero n]
    {α lam Λ K : ℝ} (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam) (hΛ : 0 ≤ Λ) (hK : 0 ≤ K) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧
      ∀ A₀ : Matrix (Fin n) (Fin n) ℝ, A₀.PosDef →
      (∀ v : KernelSpace n, lam * ‖v‖ ^ 2 ≤ euclideanQuadratic A₀ v) →
      (∀ v : KernelSpace n, euclideanQuadratic A₀ v ≤ Λ * ‖v‖ ^ 2) →
      ∀ A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ,
      (∀ x i j, |A₀ i j - A x i j| ≤ ε) →
      (∀ x y i j, |A x i j - A y i j| ≤ K * ‖x - y‖ ^ α) →
      ∀ u : KernelSpace n → ℝ, ContDiff ℝ 2 u → HasCompactSupport u →
      (∃ Q : ℝ, 0 ≤ Q ∧ ∀ x y, ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ Q * ‖x - y‖ ^ α) →
      ∀ U F H : ℝ, 0 ≤ U → 0 ≤ F → 0 ≤ H → (∀ x, |u x| ≤ U) →
      (∀ x, |euclideanEllipticOperator (A x) u x| ≤ F) →
      (∀ x y, |euclideanEllipticOperator (A x) u x - euclideanEllipticOperator (A y) u y| ≤ H * ‖x - y‖ ^ α) →
      (∀ x, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ C * (U + F + H)) ∧
      (∀ x y, ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ C * (U + F + H) * ‖x - y‖ ^ α) := by
  obtain ⟨C₀, hC₀, hbase⟩ := exists_compact_constant_elliptic_schauder (n := n) hα hα1 hlam hΛ
  let N : ℝ := (n : ℝ)^2
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hN : 0 < N := by dsimp [N]; positivity
  let ε : ℝ := min 1 (8 * C₀ * N)⁻¹
  have hε : 0 < ε := lt_min zero_lt_one (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have heps : C₀ * N * ε ≤ 1 / 8 := by
    have hh := mul_le_mul_of_nonneg_left (min_le_right (1 : ℝ) (8 * C₀ * N)⁻¹)
      (mul_nonneg hC₀.le hN.le)
    apply hh.trans_eq
    field_simp
  let d : ℝ := 8 * C₀ * N * (K + 1)
  have hd : 0 < d := by dsimp [d]; positivity
  let ρ : ℝ := (d⁻¹) ^ α⁻¹
  have hρ : 0 < ρ := Real.rpow_pos_of_pos (inv_pos.mpr hd) _
  have hρpow : ρ ^ α = d⁻¹ := by
    dsimp [ρ]
    rw [← Real.rpow_mul (inv_nonneg.mpr hd.le), inv_mul_cancel₀ hα.ne', Real.rpow_one]
  have hcoeff : C₀ * N * ε + 2 * C₀ * N * (ε + K) * ρ ^ α ≤ 1 / 2 := by
    have he : 2 * C₀ * N * (1 + K) * ρ ^ α = 1 / 4 := by
      rw [hρpow]
      dsimp [d]
      field_simp
      ring
    have hb := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (show ε + K ≤ 1 + K by linarith) (by positivity : 0 ≤ 2 * C₀ * N))
      (Real.rpow_nonneg hρ.le α)
    linarith
  let B : ℝ := C₀ + 4 * C₀ * N * (ε + K) / ρ ^ 2
  have hB : 0 < B := by dsimp [B]; positivity
  let C : ℝ := 2 * B + 4 / ρ ^ 2 + 4 * B * ρ ^ α + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hCq : 2 * B ≤ C := by
    have hh : 0 ≤ 4 / ρ ^ 2 + 4 * B * ρ ^ α + 1 := by positivity
    dsimp [C]
    linarith
  have hCs : 4 / ρ ^ 2 + 4 * B * ρ ^ α ≤ C := by dsimp [C]; linarith
  refine ⟨ε, C, hε, hC, ?_⟩
  intro A₀ hA₀ hlower hupper A hA hAH u hu huc hinit U F H hU hF hH hub hfb hfh
  let T : ℝ := U + F + H
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have himprove : ∀ q : ℝ, 0 ≤ q →
      (∀ x y, ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ q * ‖x - y‖ ^ α) →
      ∀ x y, ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ (q / 2 + B * T) * ‖x - y‖ ^ α := by
    intro q hq hqbound
    let M : ℝ := 4 * U / ρ ^ 2 + 2 * q * ρ ^ α
    have hM : 0 ≤ M := by dsimp [M]; positivity
    have hsup : ∀ x, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ M := by
      intro x
      exact hessian_interpolation_on_closedBall hu hρ hU hq hα.le
        (fun y _ => hub y) (fun y _ z _ => hqbound y z)
    have hF₀ : ∀ x, |euclideanEllipticOperator A₀ u x| ≤ F + N * ε * M := by
      intro x
      rw [euclideanEllipticOperator_freeze A₀ A u x]
      exact (abs_add_le _ _).trans (add_le_add (hfb x)
        (euclideanFreezingResidual_abs_bound hε.le hM hA hsup x))
    have hH₀ : ∀ x y, |euclideanEllipticOperator A₀ u x - euclideanEllipticOperator A₀ u y| ≤
        (H + N * (ε * q + K * M)) * ‖x - y‖ ^ α := by
      intro x y
      rw [euclideanEllipticOperator_freeze A₀ A u x, euclideanEllipticOperator_freeze A₀ A u y]
      have he : (euclideanEllipticOperator (A x) u x + euclideanFreezingResidual A₀ A u x) -
          (euclideanEllipticOperator (A y) u y + euclideanFreezingResidual A₀ A u y) =
          (euclideanEllipticOperator (A x) u x - euclideanEllipticOperator (A y) u y) +
          (euclideanFreezingResidual A₀ A u x - euclideanFreezingResidual A₀ A u y) := by ring
      rw [he]
      exact (abs_add_le _ _).trans ((add_le_add (hfh x y)
        (euclideanFreezingResidual_holder_bound hε.le hM hK hq hA hAH hsup hqbound x y)).trans_eq (by dsimp [N]; ring))
    obtain ⟨_, hHolder⟩ := hbase A₀ hA₀ hlower hupper u hu huc U (F + N * ε * M)
      (H + N * (ε * q + K * M)) hU (by positivity) (by positivity) hub hF₀ hH₀
    have hdata : C₀ * (U + (F + N * ε * M) + (H + N * (ε * q + K * M))) ≤ q / 2 + B * T := by
      let cU : ℝ := 4 * C₀ * N * (ε + K) / ρ ^ 2
      let cQ : ℝ := C₀ * N * ε + 2 * C₀ * N * (ε + K) * ρ ^ α
      have hcU : 0 ≤ cU := by dsimp [cU]; positivity
      have hUT : U ≤ T := by dsimp [T]; linarith
      have hqmul : cQ * q ≤ q / 2 := by
        exact (mul_le_mul_of_nonneg_right hcoeff hq).trans_eq (by ring)
      calc
        _ = C₀ * T + cU * U + cQ * q := by dsimp [M, cU, cQ, T]; ring
        _ ≤ C₀ * T + cU * T + q / 2 :=
          add_le_add (add_le_add_left (mul_le_mul_of_nonneg_left hUT hcU) _) hqmul
        _ = _ := by dsimp [cU, B]; ring
    intro x y
    exact (hHolder x y).trans (mul_le_mul_of_nonneg_right hdata (Real.rpow_nonneg (norm_nonneg _) _))
  obtain ⟨Q, hQ, hQbound⟩ := hinit
  have hfinal : ∀ x y, ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤
      (2 * B * T) * ‖x - y‖ ^ α := by
    have hh := holder_bound_of_half_improvement (f := fun x => fderiv ℝ (fderiv ℝ u) x)
      (α := α) (S := Set.univ) hQ (mul_nonneg hB.le hT)
      (fun x _ y _ => hQbound x y)
      (fun q hq hqb x _ y _ => himprove q hq (fun a b => hqb a (mem_univ a) b (mem_univ b)) x y)
    intro x y
    simpa only [mul_assoc] using hh x (mem_univ x) y (mem_univ y)
  constructor
  · intro x
    have hh := hessian_interpolation_on_closedBall hu (x := x) hρ hU
      (show 0 ≤ 2 * B * T by positivity) hα.le
      (fun y _ => hub y) (fun y _ z _ => hfinal y z)
    apply hh.trans
    have hUT : U ≤ T := by dsimp [T]; linarith
    have hmul := mul_le_mul_of_nonneg_left hUT (show 0 ≤ 4 / ρ ^ 2 by positivity)
    have hCmul := mul_le_mul_of_nonneg_right hCs hT
    change _ ≤ C * T
    calc
      _ = (4 / ρ ^ 2) * U + (4 * B * ρ ^ α) * T := by ring
      _ ≤ (4 / ρ ^ 2) * T + (4 * B * ρ ^ α) * T := add_le_add_right hmul _
      _ = (4 / ρ ^ 2 + 4 * B * ρ ^ α) * T := by ring
      _ ≤ C * T := hCmul
  · intro x y
    apply (hfinal x y).trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCq hT)
      (Real.rpow_nonneg (norm_nonneg _) _)

end GaussianTilt.MomentMapSchauder
