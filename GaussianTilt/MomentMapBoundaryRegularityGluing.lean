import GaussianTilt.MomentMapBoundaryRegularityZeroBoundary

/-!
# Actual boundary/interior Hölder gluing

A boundary approach modulus and the genuine distance-weighted interior
derivative estimate give a global Hölder modulus with exponent α/(1+α).
Nearest boundary points and the interior comparison segments are constructed
from the actual compact domain.
-/
noncomputable section
open Set Filter Metric
open scoped Topology
namespace GaussianTilt.MomentMapRegularity
variable {n : ℕ}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma closedBall_half_boundaryDistance_subset_interior [NeZero n] {S : Set (E n)}
    (hS : IsCompact S) {x : E n} (hx : x ∈ S) (hd : 0 < Metric.infDist x (frontier S)) :
    Metric.closedBall x (Metric.infDist x (frontier S)/2) ⊆ interior S := by
  have hbig := closedBall_infDist_frontier_subset hS hx
  intro y hy
  have hyb : y ∈ Metric.ball x (Metric.infDist x (frontier S)) :=
    lt_of_le_of_lt hy (half_lt_self hd)
  apply mem_interior_iff_mem_nhds.mpr
  exact Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hyb)
    (fun z hz => hbig (Metric.ball_subset_closedBall hz))

lemma interior_difference_bound_of_boundary_scaled_derivative [NeZero n]
    {S : Set (E n)} (hS : IsCompact S) {f : E n → F} {D : E n → E n →L[ℝ] F}
    {K : ℝ} (hK : 0 ≤ K)
    (hf : ∀ z ∈ interior S, HasFDerivAt f (D z) z)
    (hD : ∀ z ∈ interior S, Metric.infDist z (frontier S)*‖D z‖ ≤ K)
    {x y : E n} (hx : x ∈ S) (hd : 0 < Metric.infDist x (frontier S))
    (hy : dist y x ≤ Metric.infDist x (frontier S)/2) :
    ‖f x-f y‖ ≤ (2*K/Metric.infDist x (frontier S))*dist x y := by
  let d := Metric.infDist x (frontier S)
  have hball : Metric.closedBall x (d/2) ⊆ interior S :=
    closedBall_half_boundaryDistance_subset_interior hS hx hd
  have hDb (z : E n) (hz : z ∈ Metric.closedBall x (d/2)) : ‖D z‖ ≤ 2*K/d := by
    have hdist : d ≤ Metric.infDist z (frontier S)+dist x z := Metric.infDist_le_infDist_add_dist
    have hzx : dist x z ≤ d/2 := by simpa only [Metric.mem_closedBall,dist_comm] using hz
    have hzdist : d/2 ≤ Metric.infDist z (frontier S) := by linarith
    have hm := mul_le_mul_of_nonneg_right hzdist (norm_nonneg (D z))
    have hh := hD z (hball hz)
    apply (le_div_iff₀ hd).mpr
    nlinarith
  have hh := (convex_closedBall x (d/2)).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z hz => (hf z (hball hz)).hasFDerivWithinAt) hDb
    (Metric.mem_closedBall_self (half_pos hd).le) hy
  simpa only [norm_sub_rev,dist_eq_norm] using hh

def boundaryInteriorHolderExponent (α : ℝ) : ℝ := α/(1+α)

lemma boundaryInteriorHolderExponent_pos {α : ℝ} (hα : 0 < α) :
    0 < boundaryInteriorHolderExponent α := by unfold boundaryInteriorHolderExponent; positivity

lemma boundaryInteriorHolderExponent_le_one {α : ℝ} (hα : 0 ≤ α) :
    boundaryInteriorHolderExponent α ≤ 1 := by
  unfold boundaryInteriorHolderExponent
  apply (div_le_one (by positivity : 0 < 1+α)).mpr
  linarith

lemma boundary_interpolation_powers {α h : ℝ} (hα : 0 < α) (hh : 0 < h) :
    let t := h^((1+α)⁻¹)
    0 < t ∧ t^α=h^(boundaryInteriorHolderExponent α) ∧ h/t=h^(boundaryInteriorHolderExponent α) := by
  dsimp only
  refine ⟨Real.rpow_pos_of_pos hh _,?_,?_⟩
  · rw [← Real.rpow_mul hh.le]
    congr 1
    unfold boundaryInteriorHolderExponent
    ring
  · have he : boundaryInteriorHolderExponent α=1-(1+α)⁻¹ := by
      unfold boundaryInteriorHolderExponent
      field_simp
      <;> ring
    rw [he,Real.rpow_sub hh,Real.rpow_one]

/-- Global boundary/interior interpolation for the actual function and
actual derivative on a compact domain. All constants are explicit and
independent of the function once the input estimates are uniform. -/
theorem holder_of_boundary_approach_and_scaled_interior_derivative [NeZero n]
    {S : Set (E n)} (hS : IsCompact S) {f : E n → F} {D : E n → E n →L[ℝ] F}
    {α L K B : ℝ} (hα : 0 < α) (hL : 0 ≤ L) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hf : ∀ z ∈ interior S, HasFDerivAt f (D z) z)
    (hD : ∀ z ∈ interior S, Metric.infDist z (frontier S)*‖D z‖ ≤ K)
    (hbound : ∀ z ∈ S, ‖f z‖ ≤ B)
    (hboundary : ∀ x ∈ S, ∀ z ∈ frontier S, ‖f x-f z‖ ≤ L*(dist x z)^α) :
    ∀ x ∈ S, ∀ y ∈ S, ‖f x-f y‖ ≤
      (2*B+K+L*((2:ℝ)^α+(3:ℝ)^α))*(dist x y)^(boundaryInteriorHolderExponent α) := by
  intro x hx y hy
  let β := boundaryInteriorHolderExponent α
  have hβ : 0 < β := boundaryInteriorHolderExponent_pos hα
  have hconst : 0 ≤ 2*B+K+L*((2:ℝ)^α+(3:ℝ)^α) := by positivity
  by_cases hxy : x=y
  · subst y
    simp only [sub_self,norm_zero]
    positivity
  let h := dist x y
  have hh : 0 < h := dist_pos.mpr hxy
  by_cases hh1 : h ≤ 1
  · let t := h^((1+α)⁻¹)
    obtain ⟨ht,hpow,hquot⟩ := boundary_interpolation_powers hα hh
    change 0 < t at ht
    change t^α=h^β at hpow
    change h/t=h^β at hquot
    have he : (1+α)⁻¹ ≤ (1:ℝ) := by
      apply (inv_le_one₀ (by positivity : 0 < 1+α)).mpr
      linarith
    have hht : h ≤ t := Real.self_le_rpow_of_le_one hh.le hh1 he
    let d := Metric.infDist x (frontier S)
    by_cases hd : d ≤ 2*t
    · have hfront : (frontier S).Nonempty := nonempty_frontier_iff.mpr ⟨⟨x,hx⟩,hS.ne_univ⟩
      obtain ⟨z,hz,hzdist⟩ := isClosed_frontier.exists_infDist_eq_dist hfront x
      have hdx : dist x z=d := hzdist.symm
      have hdy : dist y z ≤ 3*t := by
        have htri := dist_triangle y x z
        rw [dist_comm y x,hdx] at htri
        change dist y z ≤ h+d at htri
        linarith
      have hxb := hboundary x hx z hz
      have hyb := hboundary y hy z hz
      have hxpow : (dist x z)^α ≤ (2*t)^α := Real.rpow_le_rpow dist_nonneg (by rw [hdx]; exact hd) hα.le
      have hypow : (dist y z)^α ≤ (3*t)^α := Real.rpow_le_rpow dist_nonneg hdy hα.le
      have htri := norm_add_le (f x-f z) (f z-f y)
      rw [sub_add_sub_cancel,norm_sub_rev (f z) (f y)] at htri
      have hb : ‖f x-f y‖ ≤ L*((2*t)^α+(3*t)^α) := by
        nlinarith [mul_le_mul_of_nonneg_left hxpow hL,mul_le_mul_of_nonneg_left hypow hL]
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) ht.le,
        Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) ht.le,hpow] at hb
      change ‖f x-f y‖ ≤ (2*B+K+L*(2^α+3^α))*h^β
      have hn : 0 ≤ (2*B+K)*h^β := by positivity
      nlinarith
    · have hdt : 2*t < d := lt_of_not_ge hd
      have hd0 : 0 < d := by linarith
      have hyball : dist y x ≤ d/2 := by rw [dist_comm]; change h ≤ d/2; linarith
      have hi := interior_difference_bound_of_boundary_scaled_derivative hS hK hf hD hx hd0 hyball
      have hcoef : 2*K/d ≤ K/t := by
        apply (div_le_div_iff₀ hd0 ht).mpr
        nlinarith [mul_le_mul_of_nonneg_left hdt.le hK]
      have hm := mul_le_mul_of_nonneg_right hcoef hh.le
      have hb : ‖f x-f y‖ ≤ K*h^β := by
        have heq : (K/t)*h=K*(h/t) := by ring
        rw [heq,hquot] at hm
        exact hi.trans hm
      change ‖f x-f y‖ ≤ (2*B+K+L*(2^α+3^α))*h^β
      have hn : 0 ≤ (2*B+L*(2^α+3^α))*h^β := by positivity
      nlinarith
  · have hhlarge : 1 ≤ h := (lt_of_not_ge hh1).le
    have hp : 1 ≤ h^β := Real.one_le_rpow hhlarge hβ.le
    have hb : ‖f x-f y‖ ≤ 2*B := by
      have ht := norm_sub_le (f x) (f y)
      linarith [hbound x hx,hbound y hy]
    have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ 2*B by positivity)
    have hn : 0 ≤ (K+L*(2^α+3^α))*h^β := by positivity
    change ‖f x-f y‖ ≤ (2*B+K+L*(2^α+3^α))*h^β
    nlinarith

/-- A local boundary approach estimate becomes global by the genuine
uniform value bound; no large-distance boundary regularity is assumed. -/
lemma boundary_approach_global_of_local {S : Set (E n)} (hS : IsClosed S) {f : E n → F}
    {α L B r₀ : ℝ} (hα : 0 < α) (hL : 0 ≤ L) (hB : 0 ≤ B) (hr₀ : 0 < r₀)
    (hbound : ∀ x ∈ S, ‖f x‖ ≤ B)
    (hlocal : ∀ x ∈ S, ∀ z ∈ frontier S, dist x z ≤ r₀ → ‖f x-f z‖ ≤ L*(dist x z)^α) :
    ∀ x ∈ S, ∀ z ∈ frontier S, ‖f x-f z‖ ≤ max L (2*B/r₀^α)*(dist x z)^α := by
  intro x hx z hz
  by_cases hdist : dist x z ≤ r₀
  · exact (hlocal x hx z hz hdist).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg dist_nonneg α))
  · have hfar : r₀ ≤ dist x z := (lt_of_not_ge hdist).le
    have hp := Real.rpow_le_rpow hr₀.le hfar hα.le
    have hp0 : 0 < r₀^α := Real.rpow_pos_of_pos hr₀ α
    have hv : ‖f x-f z‖ ≤ 2*B := by
      have hh := norm_sub_le (f x) (f z)
      linarith [hbound x hx,hbound z (hS.frontier_subset hz)]
    have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ 2*B/r₀^α by positivity)
    have he : (2*B/r₀^α)*r₀^α=2*B := div_mul_cancel₀ _ hp0.ne'
    rw [he] at hm
    exact (hv.trans hm).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg dist_nonneg α))

/-- The distance weight is derived from actual interior balls of radius at
most one. This is the scale restriction supplied by the Calabi estimate. -/
lemma boundary_scaled_derivative_of_interior_ball_bounds [NeZero n]
    {S : Set (E n)} (hS : IsCompact S) {D : E n → E n →L[ℝ] F} {K : ℝ} (hK : 0 ≤ K)
    (hball : ∀ x ∈ interior S, ∀ r : ℝ, 0 < r → r ≤ 1 →
      Metric.closedBall x r ⊆ interior S → r*‖D x‖ ≤ K) :
    ∀ x ∈ interior S, Metric.infDist x (frontier S)*‖D x‖ ≤ 2*max (Metric.diam S) 1*K := by
  intro x hx
  have hfront : (frontier S).Nonempty := nonempty_frontier_iff.mpr
    ⟨⟨x,interior_subset hx⟩,hS.ne_univ⟩
  let d := Metric.infDist x (frontier S)
  have hd : 0 < d := (isClosed_frontier.notMem_iff_infDist_pos hfront).mp (fun hz => hz.2 hx)
  obtain ⟨z,hz⟩ := hfront
  have hdiam : d ≤ Metric.diam S :=
    (Metric.infDist_le_dist_of_mem hz).trans
      (Metric.dist_le_diam_of_mem hS.isBounded (interior_subset hx) (hS.isClosed.frontier_subset hz))
  let r := min (d/2) 1
  have hr : 0 < r := lt_min (half_pos hd) zero_lt_one
  have hr1 : r ≤ 1 := min_le_right _ _
  have hinside : Metric.closedBall x r ⊆ interior S :=
    (Metric.closedBall_subset_closedBall (min_le_left _ _)).trans
      (closedBall_half_boundaryDistance_subset_interior hS (interior_subset hx) hd)
  have hb := hball x hx r hr hr1 hinside
  have hmax : 1 ≤ max (Metric.diam S) 1 := le_max_right _ _
  have hmaxD : d ≤ max (Metric.diam S) 1 := hdiam.trans (le_max_left _ _)
  change d*‖D x‖ ≤ _
  by_cases hd1 : d/2 ≤ 1
  · dsimp only [r] at hb
    rw [min_eq_left hd1] at hb
    nlinarith [mul_le_mul_of_nonneg_right hmax hK]
  · dsimp only [r] at hb
    rw [min_eq_right (lt_of_not_ge hd1).le,one_mul] at hb
    have hmul := mul_le_mul hmaxD hb (norm_nonneg _) (by positivity : 0 ≤ max (Metric.diam S) 1)
    nlinarith [mul_nonneg (show 0 ≤ max (Metric.diam S) 1 from by positivity) hK]

/-- The final gluing interface directly accepts local boundary approach
and the genuine radius-restricted interior derivative estimates. -/
theorem holder_of_local_boundary_approach_and_interior_ball_derivative [NeZero n]
    {S : Set (E n)} (hS : IsCompact S) {f : E n → F} {D : E n → E n →L[ℝ] F}
    {α L K B r₀ : ℝ} (hα : 0 < α) (hL : 0 ≤ L) (hK : 0 ≤ K) (hB : 0 ≤ B) (hr₀ : 0 < r₀)
    (hf : ∀ z ∈ interior S, HasFDerivAt f (D z) z)
    (hD : ∀ x ∈ interior S, ∀ r : ℝ, 0 < r → r ≤ 1 →
      Metric.closedBall x r ⊆ interior S → r*‖D x‖ ≤ K)
    (hbound : ∀ z ∈ S, ‖f z‖ ≤ B)
    (hboundary : ∀ x ∈ S, ∀ z ∈ frontier S, dist x z ≤ r₀ → ‖f x-f z‖ ≤ L*(dist x z)^α) :
    ∀ x ∈ S, ∀ y ∈ S, ‖f x-f y‖ ≤
      (2*B+2*max (Metric.diam S) 1*K+max L (2*B/r₀^α)*((2:ℝ)^α+(3:ℝ)^α))*
        (dist x y)^(boundaryInteriorHolderExponent α) := by
  exact holder_of_boundary_approach_and_scaled_interior_derivative hS hα
    (le_trans hL (le_max_left _ _)) (by positivity) hB hf
    (boundary_scaled_derivative_of_interior_ball_bounds hS hK hD) hbound
    (boundary_approach_global_of_local hS.isClosed hα hL hB hr₀ hbound hboundary)

end GaussianTilt.MomentMapRegularity
