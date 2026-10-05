import GaussianTilt.MomentMapSchauderBoundaryVariableDrift
import GaussianTilt.MomentMapHolderHalfBallInterpolation

/-! # Genuine interior interpolation for arbitrary closed compatible jets -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option maxHeartbeats 1800000
open Set Filter InnerProductSpace
open scoped ContDiff Topology
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapRegularity GaussianTilt.HolderSpace
variable {n : ℕ}

/-- The true closed-jet FTC Taylor polynomial gives the usual full-ball
interpolation bounds at every point in an interior ball. -/
theorem interior_jet_derivative_interpolation {S : Set (KernelSpace n)}
    (hS : Convex ℝ S) (hSc : IsClosed S) (hint : (interior S).Nonempty)
    {a : KernelSpace n} {R α U r : ℝ} (hR : 0 < R) (hα : 0 < α) (hU : 0 ≤ U)
    (hball : Metric.closedBall a R ⊆ S) (J : Jet (KernelSpace n) ℝ hS α)
    (hu : ∀ y : S, |value S ℝ α (jetValue (KernelSpace n) ℝ hS α J) y| ≤ U)
    (hr : 0 < r) (hrR : r ≤ R/2) (x : S) (hx : ‖(x : KernelSpace n)-a‖ ≤ R/2) :
    ‖value S (KernelSpace n →L[ℝ] ℝ) α (jetFirst (KernelSpace n) ℝ hS α J) x‖ ≤
      U/r+‖jetSecond (KernelSpace n) ℝ hS α J‖*r^α*r ∧
    ‖value S (KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ) α (jetSecond (KernelSpace n) ℝ hS α J) x‖ ≤
      4*U/r^2+4*‖jetSecond (KernelSpace n) ℝ hS α J‖*r^α := by
  let b := value S ℝ α (jetValue (KernelSpace n) ℝ hS α J) x
  let D := value S (KernelSpace n →L[ℝ] ℝ) α (jetFirst (KernelSpace n) ℝ hS α J) x
  let B := value S (KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ) α (jetSecond (KernelSpace n) ℝ hS α J) x
  let T := continuousLinearMapOfBilin B
  let p := (toDual ℝ (KernelSpace n)).symm D
  let Q := ‖jetSecond (KernelSpace n) ℝ hS α J‖
  have hQ : 0 ≤ Q := norm_nonneg _
  have hsym (v w : KernelSpace n) : inner ℝ (T v) w=inner ℝ v (T w) := by
    rw [real_inner_comm (T w) v]
    simp only [T,continuousLinearMapOfBilin_apply]
    exact jet_second_symmetric_closed hS hSc hint hα J x v w
  have hpoly (h : KernelSpace n) (hh : ‖h‖ ≤ r) : |quadraticJet b p 0 T h| ≤ U+Q*r^α*r^2 := by
    have hyS : (x : KernelSpace n)+h ∈ S := by
      apply hball
      rw [Metric.mem_closedBall,dist_eq_norm]
      have he : (x : KernelSpace n)+h-a=((x : KernelSpace n)-a)+h := by abel
      rw [he]
      exact (norm_add_le _ _).trans (by linarith)
    let y : S := ⟨(x : KernelSpace n)+h,hyS⟩
    let uy := value S ℝ α (jetValue (KernelSpace n) ℝ hS α J) y
    have hyx : (y : KernelSpace n)-x=h := by dsimp [y]; abel
    have ht := jet_quadratic_remainder_norm hS hα.le J x y
    rw [hyx] at ht
    have hpD : inner ℝ p h=D h := toDual_symm_apply
    have hTB : inner ℝ (T h) h=B h h := continuousLinearMapOfBilin_apply _ _ _
    have ht' : |uy-quadraticJet b p 0 T h| ≤ Q*‖h‖^α*‖h‖^2 := by
      simp only [quadraticJet,sub_zero,hpD,hTB]
      convert ht using 1 <;> dsimp only [b,D,B,Q,uy] <;> congr 1 <;> ring
    have hpw := Real.rpow_le_rpow (norm_nonneg h) hh hα.le
    have hsq := (sq_le_sq₀ (norm_nonneg h) hr.le).mpr hh
    have htR : Q*‖h‖^α*‖h‖^2 ≤ Q*r^α*r^2 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpw hQ) hsq (sq_nonneg _) (by positivity)
    have hv := abs_sub_le (quadraticJet b p 0 T h) uy 0
    simp only [sub_zero,abs_sub_comm (quadraticJet b p 0 T h) uy] at hv
    exact hv.trans (by linarith [ht'.trans htR,hu y])
  have hp := quadraticJet_gradient_norm_bound b p T hr (by positivity : 0 ≤ U+Q*r^α*r^2) hpoly
  have hT := quadraticJet_hessian_norm_bound b p T hsym hr (by positivity : 0 ≤ U+Q*r^α*r^2) hpoly
  rw [show ‖p‖=‖D‖ from (toDual ℝ (KernelSpace n)).symm.norm_map D] at hp
  rw [show ‖T‖=‖B‖ from norm_continuousLinearMapOfBilin_real B] at hT
  exact ⟨hp.trans_eq (by dsimp only [Q]; field_simp <;> ring),hT.trans_eq (by dsimp only [Q]; field_simp <;> ring)⟩

/-- An explicit positive interpolation radius is chosen before the
unknown jet, making the highest Hölder norm arbitrarily small. -/
theorem interior_jet_derivatives_small_highest {R α ε : ℝ} (hR : 0 < R) (hα : 0 < α) (hε : 0 < ε) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (S : Set (KernelSpace n)) (hS : Convex ℝ S) (hSc : IsClosed S)
      (hint : (interior S).Nonempty) (a : KernelSpace n), Metric.closedBall a R ⊆ S →
      ∀ (J : Jet (KernelSpace n) ℝ hS α) (U : ℝ), 0 ≤ U →
      (∀ y : S, |value S ℝ α (jetValue (KernelSpace n) ℝ hS α J) y| ≤ U) →
      ∀ x : S, ‖(x : KernelSpace n)-a‖ ≤ R/2 →
      ‖value S (KernelSpace n →L[ℝ] ℝ) α (jetFirst (KernelSpace n) ℝ hS α J) x‖ ≤
        L*U+ε*‖jetSecond (KernelSpace n) ℝ hS α J‖ ∧
      ‖value S (KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ) α (jetSecond (KernelSpace n) ℝ hS α J) x‖ ≤
        L*U+ε*‖jetSecond (KernelSpace n) ℝ hS α J‖ := by
  have hc : ContinuousAt (fun r : ℝ => (4:ℝ)*r^α) 0 :=
    continuous_const.continuousAt.mul (Real.continuous_rpow_const hα.le).continuousAt
  have he : ∀ᶠ r : ℝ in 𝓝 0, (4:ℝ)*r^α < ε :=
    hc.eventually (eventually_lt_nhds (by simpa [Real.zero_rpow hα.ne'] using hε))
  have hrsmall : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r ∧ r ≤ R/2 ∧ r ≤ 1 ∧ (4:ℝ)*r^α ≤ ε := by
    filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds he,
      nhdsWithin_le_nhds (eventually_lt_nhds (half_pos hR)),
      nhdsWithin_le_nhds (eventually_lt_nhds (show (0:ℝ)<1 by norm_num))] with r hr he hrR hr1
    exact ⟨hr,hrR.le,hr1.le,he.le⟩
  obtain ⟨r,hr,hrR,hr1,h4⟩ := hrsmall.exists
  let L := max (1/r) (4/r^2)
  have hL : 0 ≤ L := (by positivity : 0 ≤ (1:ℝ)/r).trans (le_max_left _ _)
  refine ⟨L,hL,?_⟩
  intro S hS hSc hint a hball J U hU hu x hx
  have hh := interior_jet_derivative_interpolation hS hSc hint hR hα hU hball J hu hr hrR x hx
  let Q := ‖jetSecond (KernelSpace n) ℝ hS α J‖
  have hQ : 0 ≤ Q := norm_nonneg _
  have h1 : r^α*r ≤ ε := by
    have ht := mul_le_mul_of_nonneg_left hr1 (Real.rpow_nonneg hr.le α)
    nlinarith [Real.rpow_nonneg hr.le α]
  constructor
  · apply hh.1.trans
    have hb : U/r ≤ L*U := by convert mul_le_mul_of_nonneg_right (le_max_left (1/r) (4/r^2)) hU using 1 <;> ring
    have hq : Q*r^α*r ≤ ε*Q := by convert mul_le_mul_of_nonneg_right h1 hQ using 1 <;> ring
    exact add_le_add hb hq
  · apply hh.2.trans
    have hb : 4*U/r^2 ≤ L*U := by convert mul_le_mul_of_nonneg_right (le_max_right (1/r) (4/r^2)) hU using 1 <;> ring
    have hq : 4*Q*r^α ≤ ε*Q := by convert mul_le_mul_of_nonneg_right h4 hQ using 1 <;> ring
    exact add_le_add hb hq

end GaussianTilt.MomentMapSchauder
