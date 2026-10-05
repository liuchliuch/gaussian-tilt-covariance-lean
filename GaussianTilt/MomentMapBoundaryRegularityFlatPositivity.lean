import GaussianTilt.MomentMapBoundaryRegularityTangentGeometry

/-!
# Genuine flat-boundary positivity propagation

Interior Harnack supplies the inner tangent-sphere lower bound. The
constructed exponential barrier supplies linear growth all the way to the
flat boundary. Constants are fixed before the coefficients and solution.
-/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

theorem exists_flat_boundary_positivity [NeZero n] {lam Λ K : ℝ}
    (hlam : 0 < lam) (hΛ : 0 ≤ Λ) (hK : 0 ≤ K) :
    ∃ δ ε₀ : ℝ, 0 < δ ∧ δ ≤ 1/2 ∧ 0 < ε₀ ∧
      ∀ (j : Fin n) (v f : CoordinateSpace n → ℝ) (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ),
      ContDiff ℝ ∞ v → Differentiable ℝ f → (∀ i k, Differentiable ℝ (fun y => A y i k)) →
      (∀ y, ‖(coordinateEquiv n).symm y‖ ≤ 1 → 0 ≤ y j → 0 ≤ v y) →
      (∀ y ∈ flatHalfBall j, (A y).PosDef) →
      (∀ y ∈ flatHalfBall j, ∀ w : CoordinateSpace n,
        lam*‖(coordinateEquiv n).symm w‖^2 ≤ w ⬝ᵥ (A y *ᵥ w) ∧
        w ⬝ᵥ (A y *ᵥ w) ≤ Λ*‖(coordinateEquiv n).symm w‖^2) →
      (∀ y ∈ flatHalfBall j, ∀ k a b, y j*|matrixCoordinateDerivative A k y a b| ≤ K) →
      (∀ y ∈ flatHalfBall j, |f y| ≤ ε₀) →
      (∀ y ∈ flatHalfBall j, ∀ k, y j*|coordinateDerivative k f y| ≤ ε₀) →
      (∀ y ∈ flatHalfBall j, linearizedMA (A y) v y = f y) →
      1/8 ≤ v (Pi.single j (1/4)) →
      ∀ x, ‖(coordinateEquiv n).symm x‖ ≤ 1/8 → 0 ≤ x j → δ*x j ≤ v x := by
  obtain ⟨C,hC,hcore⟩ := exists_flat_core_harnack (n := n) hlam hΛ hK
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  let m := 1/(16*C)
  let a := 64*(2*(n:ℝ)*Λ+1)/lam
  let E := Real.exp (-a*(1/8:ℝ)^2)
  let ε₀ := min (1/(2048*C)) (m*a*E)
  let δ := min (1/2:ℝ) (min m (m*a*(1/8)*E))
  have hm : 0 < m := by dsimp [m]; positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have hE : 0 < E := Real.exp_pos _
  have hε : 0 < ε₀ := by dsimp [ε₀]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδm : δ ≤ m := (min_le_right _ _).trans (min_le_left _ _)
  have hδB : δ ≤ m*a*(1/8)*E := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ,ε₀,hδ,min_le_left _ _,hε,?_⟩
  intro j v f A hv hf hAd hn hA hEll hDA hfb hDfb hP hcorn x hx hxt
  have hcorebound (y : CoordinateSpace n) (hy : y ∈ flatInteriorCore j) : m ≤ v y := by
    have hh := hcore j v f A hv hf hAd (fun z hz => hn z hz.1.le hz.2.le)
      hA hEll hDA ε₀ hε.le hfb hDfb hP y hy
    have he := min_le_left (1/(2048*C)) (m*a*E)
    change ε₀ ≤ 1/(2048*C) at he
    have he' := (le_div_iff₀ (show 0 < 2048*C by positivity)).mp he
    apply (div_le_iff₀ (show 0 < 16*C by positivity)).mpr
    nlinarith
  have hxt1 : x j ≤ 1/8 := (le_abs_self _).trans ((abs_coordinate_le_euclidean_norm x j).trans hx)
  by_cases htlarge : 1/16 ≤ x j
  · have hxcore : x ∈ flatInteriorCore j := ⟨by linarith,htlarge⟩
    have hb := hcorebound x hxcore
    have hm1 := mul_le_mul_of_nonneg_right hδm hxt
    nlinarith [mul_nonneg hm.le (sub_nonneg.mpr hxt1)]
  · let z := x-x j • (Pi.single j 1 : CoordinateSpace n)
    have hz := flat_normal_projection j hx
    change z j=0 ∧ ‖(coordinateEquiv n).symm z‖ ≤ 1/4 ∧
      ‖(coordinateEquiv n).symm x-(coordinateEquiv n).symm (flatTangentCenter j z)‖ = |x j-1/8| at hz
    have hinside (y : CoordinateSpace n)
        (hy : y ∈ interior (coordinateClosedAnnulus (flatTangentCenter j z) (1/16) (1/8))) :
        y ∈ flatHalfBall j := flat_tangent_annulus_interior j hz.1 hz.2.1 hy
    have hsize : 2*((n:ℝ)*Λ)+1 ≤ 4*a*lam*(1/16:ℝ)^2 := by
      dsimp [a]
      field_simp
      <;> nlinarith
    have hbar := hopf_annulus_lower_bound (flatTangentCenter j z)
      (show 0 ≤ (1/16:ℝ) by norm_num) ha hlam.le hm.le hsize
      hv.continuous.continuousOn (fun _ _ => (contDiff_infty.mp hv 2).contDiffAt)
      (fun y hy => hA y (hinside y hy))
      (fun y hy => (hEll y (hinside y hy) (y-flatTangentCenter j z)).1)
      (fun y hy => trace_le_of_upper_ellipticity (fun w => by
        have hw := (hEll y (hinside y hy) w).2
        rw [← coordinate_square_sum_eq_norm] at hw
        simpa only [dotProduct, pow_two] using hw))
      (fun y hy => by
        rw [hP y (hinside y hy)]
        exact (le_abs_self _).trans ((hfb y (hinside y hy)).trans (min_le_right _ _)))
      (fun y hy => hcorebound y (flat_tangent_inner_sphere_core j hz.1 hz.2.1 hy))
      (fun y hy => by
        have hyb := flat_tangent_sphere_outer j hz.1 hz.2.1 hy.le
        exact hn y (by linarith [hyb.1]) hyb.2) x
    have hxd : ‖(coordinateEquiv n).symm x-(coordinateEquiv n).symm (flatTangentCenter j z)‖ = 1/8-x j := by
      rw [hz.2.2, abs_of_nonpos (by linarith : x j-1/8 ≤ 0)]
      ring
    have hxann : x ∈ coordinateClosedAnnulus (flatTangentCenter j z) (1/16) (1/8) := by
      constructor <;> rw [hxd] <;> linarith
    have hvbar := hbar hxann
    rw [hopfExponentialBarrier_eq_norm,hxd] at hvbar
    have hg := hopf_exponential_normal_growth ha.le (show 0 ≤ (1/8:ℝ) by norm_num) hxt hxt1
    have hmg := mul_le_mul_of_nonneg_left hg hm.le
    have hδt := mul_le_mul_of_nonneg_right hδB hxt
    dsimp only [E] at hδt
    nlinarith

end GaussianTilt.MomentMapRegularity
