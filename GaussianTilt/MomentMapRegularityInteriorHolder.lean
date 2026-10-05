import GaussianTilt.MomentMapRegularityInteriorUniform
import GaussianTilt.MomentMapRegularityHolderIteration

/-!
# Interior Hölder regularity from literal Alexandrov bounds

The actual reflected-section contraction is iterated on every line. Its
power modulus controls supporting remainders, which in turn control all
components of the genuine gradient. No regularity or engulfing conclusion
is used as an input to the final local theorem.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators Gradient NNReal ENNReal
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}

/-- The actual two-sided directional gradient oscillation at radius `r`. -/
def directionalGradientOscillation (φ : E n → ℝ) (x v : E n) (r : ℝ) : ℝ :=
  inner ℝ (gradient φ (x + r • v) - gradient φ (x + (-r) • v)) v

lemma directional_gradient_monotone {φ : E n → ℝ} (hc : ConvexOn ℝ univ φ)
    (hd : Differentiable ℝ φ) (x v : E n) :
    Monotone (fun t : ℝ => inner ℝ (gradient φ (x + t • v)) v) := by
  intro s t hst
  rcases eq_or_lt_of_le hst with he | hlt
  · rw [he]
  · exact supportsAt_directional_mono (supportsAt_gradient hc (hd _))
      (supportsAt_gradient hc (hd _)) hlt

lemma directionalGradientOscillation_nonneg {φ : E n → ℝ}
    (hc : ConvexOn ℝ univ φ) (hd : Differentiable ℝ φ) (x v : E n)
    {r : ℝ} (hr : 0 ≤ r) : 0 ≤ directionalGradientOscillation φ x v r := by
  have hh := directional_gradient_monotone hc hd x v (show -r ≤ r by linarith)
  simpa only [directionalGradientOscillation, inner_sub_left, sub_nonneg] using hh

lemma directionalGradientOscillation_monotone {φ : E n → ℝ}
    (hc : ConvexOn ℝ univ φ) (hd : Differentiable ℝ φ) (x v : E n) :
    Monotone (directionalGradientOscillation φ x v) := by
  intro r s hrs
  have hright := directional_gradient_monotone hc hd x v hrs
  have hleft := directional_gradient_monotone hc hd x v (neg_le_neg hrs)
  dsimp [directionalGradientOscillation]
  rw [inner_sub_left, inner_sub_left]
  linarith

lemma directionalGradientOscillation_le_lipschitz {φ : E n → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L φ) (hc : ConvexOn ℝ univ φ) (hd : Differentiable ℝ φ)
    (x v : E n) (r : ℝ) (hv : ‖v‖ = 1) :
    directionalGradientOscillation φ x v r ≤ 2 * (L : ℝ) := by
  have hp := supportsAt_norm_le hL (supportsAt_gradient hc (hd (x + r • v)))
  have hq := supportsAt_norm_le hL (supportsAt_gradient hc (hd (x + (-r) • v)))
  calc
    _ ≤ ‖gradient φ (x + r • v) - gradient φ (x + (-r) • v)‖ * ‖v‖ := real_inner_le_norm _ _
    _ ≤ 2 * (L : ℝ) := by rw [hv, mul_one]; exact (norm_sub_le _ _).trans (by linarith)

/-- Actual uniform power decay of the directional gradient oscillation.
The exponent and constant are shared by all centers in a neighborhood and
all unit directions; their existence follows from the literal local mass
bounds and the proved reflected-section contraction. -/
theorem local_directional_oscillation_holder [NeZero n] {φ : E n → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L φ) (hc : StrictConvexOn ℝ univ φ)
    (hd : Differentiable ℝ φ) (x₀ : E n) {lam Lam : ℝ}
    (hlam : 0 < lam) (hLam : 0 < Lam)
    (hmass : ∀ A : Set (E n), IsCompact A → A ⊆ Metric.closedBall x₀ 2 →
      ENNReal.ofReal lam * volume A ≤ volume (subgradientImage φ A) ∧
      volume (subgradientImage φ A) ≤ ENNReal.ofReal Lam * volume A) :
    ∃ R C α : ℝ, 0 < R ∧ 0 < C ∧ 0 < α ∧ α ≤ 1 ∧
      ∀ x ∈ Metric.closedBall x₀ (1 / 2), ∀ v : E n, ‖v‖ = 1 →
        ∀ r : ℝ, 0 < r → r ≤ R → directionalGradientOscillation φ x v r ≤ C * r ^ α := by
  obtain ⟨R, hR, hRquarter, hcontract⟩ := uniform_directional_support_contraction hL hc x₀ hlam hLam hmass
  let θ := sectionBalanceFactor n lam Lam
  let q := 1 - θ / 8
  let α := oscillationExponent (θ / 4) q
  have hθ : 0 < θ := sectionBalanceFactor_pos hlam hLam
  have hθ1 : θ ≤ 1 := (sectionBalanceFactor_le_half n lam Lam).trans (by norm_num)
  have ha : 0 < θ / 4 := by positivity
  have ha1 : θ / 4 < 1 := by linarith
  have hq : 0 < q := by dsimp [q]; linarith
  have hq1 : q < 1 := by dsimp [q]; linarith
  have hα : 0 < α := oscillationExponent_pos ha ha1 hq hq1
  have hα1 : α ≤ 1 := oscillationExponent_le_one ha ha1 (by dsimp [q]; linarith)
  let C := q⁻¹ * (2 * (L : ℝ) + 1) / R ^ α
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨R, C, α, hR, hC, hα, hα1, ?_⟩
  intro x hx v hv r hr hrR
  have hstep : ∀ t ∈ Ioc 0 R, directionalGradientOscillation φ x v ((θ / 4) * t) ≤
      q * directionalGradientOscillation φ x v t := by
    intro t ht
    have hh := hcontract x hx v hv t ht.1 ht.2
      (gradient φ (x + (-t) • v)) (gradient φ (x + (-(θ * t / 4)) • v))
      (gradient φ (x + (θ * t / 4) • v)) (gradient φ (x + t • v))
      (supportsAt_gradient hc.convexOn (hd _)) (supportsAt_gradient hc.convexOn (hd _))
      (supportsAt_gradient hc.convexOn (hd _)) (supportsAt_gradient hc.convexOn (hd _))
    simpa only [directionalGradientOscillation, show θ / 4 * t = θ * t / 4 by ring] using hh
  have hiter := oscillation_holder_of_geometric_decay ha ha1 hq hq1 hR
    (directionalGradientOscillation_nonneg hc.convexOn hd x v hR.le)
    ((directionalGradientOscillation_monotone hc.convexOn hd x v).monotoneOn (Ioc 0 R)) hstep hr hrR
  have hinit : directionalGradientOscillation φ x v R ≤ 2 * (L : ℝ) + 1 :=
    (directionalGradientOscillation_le_lipschitz hL hc.convexOn hd x v R hv).trans (by linarith)
  calc
    directionalGradientOscillation φ x v r ≤ q⁻¹ * directionalGradientOscillation φ x v R * (r / R) ^ α := hiter
    _ ≤ q⁻¹ * (2 * (L : ℝ) + 1) * (r / R) ^ α :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hinit (inv_nonneg.mpr hq.le)) (Real.rpow_nonneg (by positivity) _)
    _ = C * r ^ α := by rw [Real.div_rpow hr.le hR.le]; dsimp [C]; ring

/-- Directional slope power decay bounds the actual supporting remainder.
This is obtained by two supporting planes, without integrating a derivative. -/
theorem supportResidual_le_of_directional_oscillation {φ : E n → ℝ}
    (hc : ConvexOn ℝ univ φ) (hd : Differentiable ℝ φ) {x : E n} {R C α : ℝ}
    (hC : 0 ≤ C) (hα : 0 < α)
    (hosc : ∀ v : E n, ‖v‖ = 1 → ∀ r : ℝ, 0 < r → r ≤ R →
      directionalGradientOscillation φ x v r ≤ C * r ^ α)
    {y : E n} (hy : ‖y - x‖ ≤ R) :
    supportResidual φ (gradient φ x) x y ≤ C * ‖y - x‖ ^ (1 + α) := by
  by_cases he : y = x
  · subst y
    rw [supportResidual_self, sub_self, norm_zero, Real.zero_rpow (by linarith : 1 + α ≠ 0), mul_zero]
  let d := ‖y - x‖
  have hdpos : 0 < d := norm_pos_iff.mpr (sub_ne_zero.mpr he)
  let v := d⁻¹ • (y - x)
  have hv : ‖v‖ = 1 := by
    simp only [v, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hdpos)]
    exact inv_mul_cancel₀ hdpos.ne'
  have hyline : x + d • v = y := by
    dsimp [v]
    rw [smul_smul, mul_inv_cancel₀ hdpos.ne', one_smul]
    module
  have hcenter := directional_gradient_monotone hc hd x v (show -d ≤ 0 by linarith)
  simp only [zero_smul, add_zero] at hcenter
  have hosc' := hosc v hv d hdpos hy
  have hsupport := supportsAt_gradient hc (hd y) x
  have hid : y - x = d • v := by rw [← hyline, add_sub_cancel_left]
  have hu : supportResidual φ (gradient φ x) x y ≤ d * directionalGradientOscillation φ x v d := by
    dsimp [supportResidual, directionalGradientOscillation]
    rw [hyline, hid, inner_smul_right, inner_sub_left]
    have heinner : inner ℝ (gradient φ y) (x - y) = -d * inner ℝ (gradient φ y) v := by
      rw [show x - y = -(y - x) by module, inner_neg_right, hid, inner_smul_right]
      ring
    rw [heinner] at hsupport
    have hm := mul_le_mul_of_nonneg_left hcenter hdpos.le
    nlinarith
  calc
    supportResidual φ (gradient φ x) x y ≤ d * directionalGradientOscillation φ x v d := hu
    _ ≤ d * (C * d ^ α) := mul_le_mul_of_nonneg_left hosc' hdpos.le
    _ = C * ‖y - x‖ ^ (1 + α) := by
      rw [show 1 + α = α + 1 by ring, Real.rpow_add_one hdpos.ne' α]
      dsimp [d]
      ring

/-- A supporting-remainder power bound controls the whole difference of
supporting slopes. The test point is displaced in the direction of the
slope difference, so this recovers transverse as well as tangential control. -/
theorem support_difference_le_of_remainder_power {φ : E n → ℝ} {x y p q : E n}
    (hp : SupportsAt φ p x) (hq : SupportsAt φ q y) {R C α : ℝ}
    (hC : 0 ≤ C) (hα : 0 < α) (hyx : y ≠ x) (hxy : 2 * ‖y - x‖ ≤ R)
    (hrem : ∀ z : E n, ‖z - x‖ ≤ R →
      supportResidual φ p x z ≤ C * ‖z - x‖ ^ (1 + α)) :
    ‖q - p‖ ≤ (C * (2 : ℝ) ^ (1 + α)) * ‖y - x‖ ^ α := by
  by_cases hqp : q = p
  · subst q
    rw [sub_self, norm_zero]
    positivity
  let d := ‖y - x‖
  have hd : 0 < d := norm_pos_iff.mpr (sub_ne_zero.mpr hyx)
  let a := q - p
  have ha : 0 < ‖a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hqp)
  let z := y + (d / ‖a‖) • a
  have hzy : ‖z - y‖ = d := by
    dsimp [z]
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hd ha), div_mul_cancel₀ _ ha.ne']
  have hzx : ‖z - x‖ ≤ 2 * d := by
    calc
      ‖z - x‖ ≤ ‖z - y‖ + ‖y - x‖ := norm_sub_le_norm_sub_add_norm_sub z y x
      _ = 2 * d := by rw [hzy]; dsimp [d]; ring
  have hzR : ‖z - x‖ ≤ R := hzx.trans hxy
  have hupper := hrem z hzR
  have hs := hq z
  have hlow := hp y
  have he : inner ℝ a (z - y) = d * ‖a‖ := by
    dsimp [z]
    rw [add_sub_cancel_left, inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have hlower : d * ‖a‖ ≤ supportResidual φ p x z := by
    have hei : inner ℝ p (z - x) = inner ℝ p (z - y) + inner ℝ p (y - x) := by
      rw [← inner_add_right]
      congr 1
      module
    dsimp [a] at he
    rw [inner_sub_left] at he
    dsimp [supportResidual]
    rw [hei]
    linarith
  have hpow := Real.rpow_le_rpow (norm_nonneg _) hzx (by linarith : 0 ≤ 1 + α)
  have hfinal : d * ‖a‖ ≤ C * (2 * d) ^ (1 + α) :=
    hlower.trans (hupper.trans (mul_le_mul_of_nonneg_left hpow hC))
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hd.le] at hfinal
  have hdpow : d ^ (1 + α) = d ^ α * d := by
    rw [show 1 + α = α + 1 by ring, Real.rpow_add_one hd.ne' α]
  rw [hdpow] at hfinal
  apply (mul_le_mul_left hd).mp
  change d * ‖a‖ ≤ d * ((C * 2 ^ (1 + α)) * d ^ α)
  convert hfinal using 1 <;> ring

/-- Interior C¹,α for finite globally Lipschitz strictly convex Alexandrov
potentials with actual locally bounded positive Monge--Ampère density.
Both the differentiability and the gradient Hölder modulus are derived. -/
theorem local_holder_gradient_of_local_subgradientImage_bounds {φ : E n → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L φ) (hc : StrictConvexOn ℝ univ φ)
    (hmass : ∀ B : Set (E n), IsCompact B →
      ∃ lam Lam : ℝ, 0 < lam ∧ 0 < Lam ∧
        ∀ A : Set (E n), IsCompact A → A ⊆ B →
          ENNReal.ofReal lam * volume A ≤ volume (subgradientImage φ A) ∧
          volume (subgradientImage φ A) ≤ ENNReal.ofReal Lam * volume A) :
    ∀ x₀ : E n, ∃ ε C α : ℝ, 0 < ε ∧ 0 < C ∧ 0 < α ∧ α ≤ 1 ∧
      ∀ y ∈ Metric.ball x₀ ε, ∀ z ∈ Metric.ball x₀ ε,
        ‖gradient φ y - gradient φ z‖ ≤ C * ‖y - z‖ ^ α := by
  by_cases hn : n = 0
  · subst n
    intro x₀
    refine ⟨1, 1, 1, zero_lt_one, zero_lt_one, zero_lt_one, le_rfl, ?_⟩
    intro y hy z hz
    have he : y = z := Subsingleton.elim _ _
    simp [he]
  letI : NeZero n := ⟨hn⟩
  have hC1 := contDiff_one_of_local_subgradientImage_bounds hL hc hmass
  have hd : Differentiable ℝ φ := hC1.differentiable (by norm_num)
  intro x₀
  obtain ⟨lam, Lam, hlam, hLam, hbounds⟩ := hmass (Metric.closedBall x₀ 2) (isCompact_closedBall x₀ 2)
  obtain ⟨R, C, α, hR, hC, hα, hα1, hosc⟩ :=
    local_directional_oscillation_holder hL hc hd x₀ hlam hLam hbounds
  let ε := min (R / 4) (1 / 8)
  have hε : 0 < ε := lt_min (by positivity) (by norm_num)
  have hεR : ε ≤ R / 4 := min_le_left _ _
  have hεsmall : ε ≤ 1 / 8 := min_le_right _ _
  refine ⟨ε, C * (2 : ℝ) ^ (1 + α), α, hε, by positivity, hα, hα1, ?_⟩
  intro y hy z hz
  by_cases he : z = y
  · subst z
    simp only [sub_self, norm_zero, Real.zero_rpow hα.ne', mul_zero, le_refl]
  have hy0 : dist y x₀ < ε := hy
  have hz0 : dist z x₀ < ε := hz
  have hyn : y ∈ Metric.closedBall x₀ (1 / 2) := by
    rw [Metric.mem_closedBall]
    linarith
  have hdist : ‖z - y‖ < 2 * ε := by
    rw [← dist_eq_norm]
    have hh := dist_triangle z x₀ y
    rw [dist_comm x₀ y] at hh
    linarith
  have hxy : 2 * ‖z - y‖ ≤ R := by linarith
  have hh := support_difference_le_of_remainder_power
    (supportsAt_gradient hc.convexOn (hd y)) (supportsAt_gradient hc.convexOn (hd z))
    hC.le hα he hxy (fun w hw => supportResidual_le_of_directional_oscillation
      hc.convexOn hd hC.le hα (hosc y hyn) hw)
  simpa only [norm_sub_rev] using hh

/-- The source of the actual moment transport has a locally Hölder
gradient. Strict convexity and both Alexandrov density bounds are proved
from the transport identity, not assumed as hidden regularity inputs. -/
theorem local_holder_gradient_of_target_density {φ V : E n → ℝ}
    {L : ℝ≥0} (hL : LipschitzWith L φ) (hc : ConvexOn ℝ univ φ)
    {K : Set (E n)} (hK : IsOpen K) (hKc : Convex ℝ K)
    (hKb : Bornology.IsBounded K) (hV : ContinuousOn V (closure K))
    (hmap : (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x)))).map
      (gradient φ) = volume.withDensity (fun x => ENNReal.ofReal
        (K.indicator (fun y => Real.exp (-V y)) x))) :
    ∀ x₀ : E n, ∃ ε C α : ℝ, 0 < ε ∧ 0 < C ∧ 0 < α ∧ α ≤ 1 ∧
      ∀ y ∈ Metric.ball x₀ ε, ∀ z ∈ Metric.ball x₀ ε,
        ‖gradient φ y - gradient φ z‖ ≤ C * ‖y - z‖ ^ α := by
  apply local_holder_gradient_of_local_subgradientImage_bounds hL
    (strictConvexOn_of_target_density hL hc hK hKc hKb hV hmap)
  intro B hB
  exact local_subgradientImage_volume_bounds hL hc hK hKc hKb hV hmap hB

end GaussianTilt.MomentMapRegularity
