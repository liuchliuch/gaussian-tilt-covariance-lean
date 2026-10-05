import GaussianTilt.MomentMapCampanatoHolderJets

/-! # Genuine one-sided quadratic coefficient extraction on half-balls -/
noncomputable section
open Set
open scoped Topology Gradient NNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

lemma halfBall_shifted_ball (j : Fin n) {r : ℝ} (hr : 0 < r)
    {h : E n} (hh : ‖h‖ ≤ r / 4) :
    ‖(r / 2) • (EuclideanSpace.basisFun (Fin n) ℝ j) + h‖ ≤ r ∧
      0 ≤ ((r / 2) • (EuclideanSpace.basisFun (Fin n) ℝ j) + h) j := by
  have hb : ‖EuclideanSpace.basisFun (Fin n) ℝ j‖ = 1 := by simp [EuclideanSpace.basisFun_apply]
  have hc : ‖(r / 2) • (EuclideanSpace.basisFun (Fin n) ℝ j)‖ = r / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (half_pos hr), hb, mul_one]
  have hj : |h j| ≤ ‖h‖ := PiLp.norm_apply_le h j
  constructor
  · have ht := norm_add_le ((r / 2) • (EuclideanSpace.basisFun (Fin n) ℝ j)) h
    rw [hc] at ht
    linarith
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    have he : (EuclideanSpace.basisFun (Fin n) ℝ j) j = 1 := by simp [EuclideanSpace.basisFun_apply]
    rw [he, mul_one]
    linarith [neg_abs_le (h j)]

/-- A half-ball has a genuine interior ball. Recentring the quadratic and
using the proved full-ball extraction controls its Hessian at the boundary. -/
theorem quadraticJet_halfBall_coefficients (j : Fin n)
    (a : ℝ) (p : E n) (H : E n →L[ℝ] E n)
    (hH : ∀ v w, inner ℝ (H v) w = inner ℝ v (H w))
    {r ε : ℝ} (hr : 0 < r) (hε : 0 ≤ ε)
    (hb : ∀ x : E n, ‖x‖ ≤ r → 0 ≤ x j → |quadraticJet a p 0 H x| ≤ ε) :
    |a| ≤ ε ∧ ‖p‖ ≤ 36 * ε / r ∧ ‖H‖ ≤ 64 * ε / r ^ 2 := by
  let c : E n := (r / 2) • (EuclideanSpace.basisFun (Fin n) ℝ j)
  have hc : ‖c‖ = r / 2 := by
    dsimp [c]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (half_pos hr)]
    simp [EuclideanSpace.basisFun_apply]
  have hball : ∀ h : E n, ‖h‖ ≤ r / 4 →
      |quadraticJet (quadraticJet a p 0 H c) (p + H c) 0 H h| ≤ ε := by
    intro h hh
    have hinc := halfBall_shifted_ball j hr hh
    have he := quadraticJet_recenter a p c 0 h H hH
    simp only [sub_zero] at he
    rw [← he]
    exact hb (c + h) hinc.1 hinc.2
  have hHb := quadraticJet_hessian_norm_bound _ _ H hH (by positivity : 0 < r / 4) hε hball
  have hpb := quadraticJet_gradient_norm_bound _ _ H (by positivity : 0 < r / 4) hε hball
  have hHfinal : ‖H‖ ≤ 64 * ε / r ^ 2 := by
    convert hHb using 1 <;> field_simp <;> ring
  refine ⟨?_, ?_, hHfinal⟩
  · simpa only [quadraticJet, sub_self, map_zero, inner_zero_right, inner_zero_left, add_zero, mul_zero] using
      hb 0 (by simpa using hr.le) (by simp)
  · have hp : ‖p‖ ≤ ‖p + H c‖ + ‖H c‖ := by
      have he : p = (p + H c) - H c := by abel
      calc
        ‖p‖ = ‖(p + H c) - H c‖ := congrArg norm he
        _ ≤ _ := norm_sub_le _ _
    have hhop := H.le_opNorm c
    rw [hc] at hhop
    have hHmul := mul_le_mul_of_nonneg_right hHfinal (half_pos hr).le
    have hnum : ε / (r / 4) + (64 * ε / r ^ 2) * (r / 2) = 36 * ε / r := by field_simp; ring
    apply hp.trans
    apply (add_le_add hpb (hhop.trans hHmul)).trans_eq
    exact hnum

/-- Two actual approximations on a half-ball have coherent true
coefficients. This does not use a false full-ball estimate after odd reflection. -/
theorem quadraticJet_halfBall_coherence (j : Fin n) {f : E n → ℝ}
    (a b : ℝ) (p q : E n) (H K : E n →L[ℝ] E n)
    (hH : ∀ v w, inner ℝ (H v) w = inner ℝ v (H w))
    (hK : ∀ v w, inner ℝ (K v) w = inner ℝ v (K w))
    {r ε η : ℝ} (hr : 0 < r) (hε : 0 ≤ ε) (hη : 0 ≤ η)
    (ha : ∀ x : E n, ‖x‖ ≤ r → 0 ≤ x j → |f x - quadraticJet a p 0 H x| ≤ ε)
    (hb : ∀ x : E n, ‖x‖ ≤ r → 0 ≤ x j → |f x - quadraticJet b q 0 K x| ≤ η) :
    |a - b| ≤ ε + η ∧ ‖p - q‖ ≤ 36 * (ε + η) / r ∧ ‖H - K‖ ≤ 64 * (ε + η) / r ^ 2 := by
  have hs : ∀ v w, inner ℝ ((H - K) v) w = inner ℝ v ((H - K) w) := by
    intro v w
    simp only [ContinuousLinearMap.sub_apply, inner_sub_left, inner_sub_right, hH, hK]
  apply quadraticJet_halfBall_coefficients j (a - b) (p - q) (H - K) hs hr (add_nonneg hε hη)
  intro x hx hxj
  rw [← quadraticJet_sub]
  calc
    _ ≤ |quadraticJet a p 0 H x - f x| + |f x - quadraticJet b q 0 K x| := abs_sub_le _ _ _
    _ ≤ ε + η := by rw [abs_sub_comm (quadraticJet a p 0 H x)]; exact add_le_add (ha x hx hxj) (hb x hx hxj)

end GaussianTilt.MomentMapRegularity
