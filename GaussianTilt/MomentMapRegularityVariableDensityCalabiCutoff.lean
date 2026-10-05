import GaussianTilt.MomentMapRegularityConstantDensityCalabiBall
import GaussianTilt.MomentMapRegularityVariableDensityCalabiEstimate

/-! # Actual cutoff maximum estimates with linear and constant forcing errors -/
noncomputable section
open Matrix Filter Set
open scoped BigOperators Topology ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

/-- The actual cutoff maximum calculation with lower-order energy errors. -/
theorem forced_calabi_cutoff_bound_at_max {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef)
    {η F : CoordinateSpace n → ℝ} {x : CoordinateSpace n}
    (hη : ContDiffAt ℝ 2 η x) (hF : ContDiffAt ℝ 2 F x)
    {c B₀ B₁ B₂ a b : ℝ} (hc : 0 < c) (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hηx : 0 < η x) (hηB : η x ≤ B₀) (hFx : 1 ≤ F x)
    (hLF : c*(F x)^2 ≤ linearizedMA A F x+a*F x+b)
    (hLη : -B₁ ≤ linearizedMA A η x)
    (hΓ : coordinateGradient η x ⬝ᵥ (A *ᵥ coordinateGradient η x) ≤ B₂)
    (hmax : IsLocalMax (fun y => (η y)^2*F y) x) :
    (η x)^2*F x ≤ (2*B₀*B₁+6*B₂+(a+b)*B₀^2)/c := by
  have hFpos : 0 < F x := lt_of_lt_of_le zero_lt_one hFx
  have hAs : A.IsSymm := by
    simpa only [Matrix.IsSymm, Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hA.isHermitian
  have hnon := linearizedMA_nonpos_at_max hA ((hη.pow 2).mul hF) hmax
  rw [linearized_cutoff_energy_at_max hAs hη hF hηx.ne' hmax] at hnon
  have hbF : b ≤ b*F x := le_mul_of_one_le_right hb hFx
  have hforced : c*(F x)^2 ≤ linearizedMA A F x+(a+b)*F x := by nlinarith
  have h1 := mul_le_mul_of_nonneg_left hforced (sq_nonneg (η x))
  have h2 := mul_le_mul_of_nonneg_left hLη (show 0 ≤ 2*η x*F x by positivity)
  have h3 := mul_le_mul_of_nonneg_left hΓ (show 0 ≤ 6*F x by positivity)
  have h4 := mul_le_mul_of_nonneg_right hηB (show 0 ≤ 2*B₁*F x by positivity)
  have hsq := pow_le_pow_left₀ hηx.le hηB 2
  have h5 := mul_le_mul_of_nonneg_right hsq (show 0 ≤ (a+b)*F x by positivity)
  have hprod : (c*(η x)^2*F x-(2*B₀*B₁+6*B₂+(a+b)*B₀^2))*F x ≤ 0 := by nlinarith
  have hle := (mul_le_mul_right hFpos).mp (show
      (c*(η x)^2*F x-(2*B₀*B₁+6*B₂+(a+b)*B₀^2))*F x ≤ 0*F x by simpa using hprod)
  apply (le_div_iff₀ hc).mpr
  nlinarith

/-- Compact maximization with all lower-order forcing errors kept in the
constant. No maximum-attainment or energy bound is assumed. -/
theorem forced_calabi_cutoff_bound_on_compact
    {S : Set (CoordinateSpace n)} (hS : IsCompact S)
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    {η F : CoordinateSpace n → ℝ} (hη : ContDiff ℝ 2 η) (hF : ContDiff ℝ 2 F)
    (hAz : ∀ y ∈ interior S, (A y).PosSemidef)
    (hzero : ∀ y ∈ frontier S, η y = 0) (hηpos : ∀ y ∈ interior S, 0 < η y)
    {c B₀ B₁ B₂ a b : ℝ} (hc : 0 < c) (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hηB : ∀ y ∈ interior S, η y ≤ B₀)
    (hLF : ∀ y ∈ interior S, c*(F y)^2 ≤ linearizedMA (A y) F y+a*F y+b)
    (hLη : ∀ y ∈ interior S, -B₁ ≤ linearizedMA (A y) η y)
    (hΓ : ∀ y ∈ interior S, coordinateGradient η y ⬝ᵥ (A y *ᵥ coordinateGradient η y) ≤ B₂) :
    ∀ x ∈ S, (η x)^2*F x ≤ B₀^2+(2*B₀*B₁+6*B₂+(a+b)*B₀^2)/c := by
  intro x hx
  have hbound0 : 0 ≤ (2*B₀*B₁+6*B₂+(a+b)*B₀^2)/c := by positivity
  by_cases hFx : (η x)^2*F x ≤ 0
  · exact hFx.trans (by positivity)
  have hFx : 0 < (η x)^2*F x := lt_of_not_ge hFx
  obtain ⟨z, hz, hmax⟩ := hS.exists_isMaxOn ⟨x, hx⟩ ((hη.continuous.pow 2).mul hF.continuous).continuousOn
  have hxz : (η x)^2*F x ≤ (η z)^2*F z := hmax hx
  have hzi : z ∈ interior S := by
    by_contra hnot
    have hzb : z ∈ frontier S := ⟨subset_closure hz, hnot⟩
    rw [hzero z hzb] at hxz
    norm_num at hxz
    exact hFx.not_ge hxz
  have hFz : 0 < F z := by
    have hh : 0 < (η z)^2*F z := hFx.trans_le hxz
    exact (mul_pos_iff_of_pos_left (sq_pos_of_pos (hηpos z hzi))).mp hh
  by_cases hlarge : 1 ≤ F z
  · have hbound := forced_calabi_cutoff_bound_at_max (hAz z hzi) hη.contDiffAt hF.contDiffAt
      hc hB₀ hB₁ hB₂ ha hb (hηpos z hzi) (hηB z hzi) hlarge (hLF z hzi) (hLη z hzi) (hΓ z hzi)
      (hmax.isLocalMax (mem_interior_iff_mem_nhds.mp hzi))
    exact hxz.trans (hbound.trans (le_add_of_nonneg_left (sq_nonneg B₀)))
  · have hsmall : F z ≤ 1 := (lt_of_not_ge hlarge).le
    have hs := mul_le_mul_of_nonneg_left hsmall (sq_nonneg (η z))
    have hsq := pow_le_pow_left₀ (hηpos z hzi).le (hηB z hzi) 2
    apply hxz.trans
    nlinarith

/-- The explicit Euclidean-ball estimate with actual linear and constant energy errors. -/
theorem forced_calabi_ball_center_bound
    {F : CoordinateSpace n → ℝ} (hF : ContDiff ℝ 2 F)
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    (c : CoordinateSpace n) {R κ Λ a b : ℝ} (hR : 0 < R) (hκ : 0 < κ) (hΛ : 0 ≤ Λ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ∀ y, ‖(coordinateEquiv n).symm y - (coordinateEquiv n).symm c‖ < R → (A y).PosSemidef)
    (hEll : ∀ y, ‖(coordinateEquiv n).symm y - (coordinateEquiv n).symm c‖ < R →
      ∀ v : CoordinateSpace n, v ⬝ᵥ (A y *ᵥ v) ≤ Λ * ‖(coordinateEquiv n).symm v‖^2)
    (hLF : ∀ y, ‖(coordinateEquiv n).symm y - (coordinateEquiv n).symm c‖ < R →
      κ * (F y)^2 ≤ linearizedMA (A y) F y+a*F y+b) :
    F c ≤ 1+((4*(n : ℝ)+24)*Λ)/(κ*R^2)+(a+b)/κ := by
  let e := coordinateEquiv n
  let S := e '' Metric.closedBall (e.symm c) R
  let η := calabiBallCutoff c R
  have hS : IsCompact S := (isCompact_closedBall _ _).image e.continuous
  have hSi : interior S = e '' Metric.ball (e.symm c) R := by
    change interior (e.toHomeomorph '' Metric.closedBall (e.symm c) R) = _
    rw [← e.toHomeomorph.image_interior, interior_closedBall _ hR.ne']
    rfl
  have hSf : frontier S = e '' Metric.sphere (e.symm c) R := by
    change frontier (e.toHomeomorph '' Metric.closedBall (e.symm c) R) = _
    rw [← e.toHomeomorph.image_frontier, frontier_closedBall _ hR.ne']
    rfl
  have hnear {y : CoordinateSpace n} (hy : y ∈ interior S) : ‖e.symm y - e.symm c‖ < R := by
    rw [hSi] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    simpa only [e.symm_apply_apply, Metric.mem_ball, dist_eq_norm] using hz
  have hzero : ∀ y ∈ frontier S, η y = 0 := by
    intro y hy
    rw [hSf] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    have hnorm : ‖z-e.symm c‖ = R := by simpa only [Metric.mem_sphere, dist_eq_norm] using hz
    dsimp only [η]
    rw [calabiBallCutoff_eq_norm]
    change R^2 - ‖e.symm (e z) - e.symm c‖^2 = 0
    rw [e.symm_apply_apply, hnorm, sub_self]
  have hηpos : ∀ y ∈ interior S, 0 < η y := by
    intro y hy
    dsimp only [η]
    rw [calabiBallCutoff_eq_norm]
    have hh := hnear hy
    nlinarith [norm_nonneg (e.symm y - e.symm c)]
  have hηB : ∀ y ∈ interior S, η y ≤ R^2 := by
    intro y _
    dsimp only [η]
    rw [calabiBallCutoff_eq_norm]
    exact sub_le_self _ (sq_nonneg _)
  have htr {y : CoordinateSpace n} (hy : y ∈ interior S) : trace (A y) ≤ (n : ℝ) * Λ := by
    have hdiag (i : Fin n) : A y i i ≤ Λ := by
      have hh := hEll y (hnear hy) (Pi.single i 1)
      simpa [Matrix.mulVec_single_one, single_dotProduct, Matrix.col, e, coordinateEquiv,
        EuclideanSpace.norm_eq, PiLp.norm_sq_eq_of_L2, EuclideanSpace.norm_sq_eq] using hh
    calc
      trace (A y) ≤ ∑ _i : Fin n, Λ := Finset.sum_le_sum (fun i _ => hdiag i)
      _ = _ := by simp
  have hLη : ∀ y ∈ interior S, -(2 * (n : ℝ) * Λ) ≤ linearizedMA (A y) η y := by
    intro y hy
    rw [linearizedMA_calabiBallCutoff]
    nlinarith [htr hy]
  have hΓ : ∀ y ∈ interior S,
      coordinateGradient η y ⬝ᵥ (A y *ᵥ coordinateGradient η y) ≤ 4 * Λ * R^2 := by
    intro y hy
    rw [coordinateGradient_calabiBallCutoff]
    simp only [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    have he := hEll y (hnear hy) (y-c)
    have hsq : ‖e.symm (y-c)‖^2 ≤ R^2 := by
      rw [map_sub]
      have hh := hnear hy
      nlinarith [norm_nonneg (e.symm y - e.symm c)]
    have hh := mul_le_mul_of_nonneg_left hsq hΛ
    nlinarith
  have hbound := forced_calabi_cutoff_bound_on_compact hS
    (contDiff_infty.mp (contDiff_calabiBallCutoff c R) 2) hF
    (fun y hy => hA y (hnear hy)) hzero hηpos hκ (sq_nonneg R)
    (by positivity : 0 ≤ 2 * (n : ℝ) * Λ) (by positivity : 0 ≤ 4 * Λ * R^2) ha hb
    hηB (fun y hy => hLF y (hnear hy)) hLη hΓ c
    (show c ∈ S from ⟨e.symm c, Metric.mem_closedBall_self hR.le, e.apply_symm_apply c⟩)
  have hηc : calabiBallCutoff c R c = R^2 := by simp [calabiBallCutoff, matrixQuadratic]
  rw [hηc] at hbound
  have hh : (((R^2)^2)*F c-(R^2)^2)*κ ≤
      2*R^2*(2*(n : ℝ)*Λ)+6*(4*Λ*R^2)+(a+b)*(R^2)^2 :=
    (le_div_iff₀ hκ).mp (by linarith [hbound])
  have he : 1+((4*(n : ℝ)+24)*Λ)/(κ*R^2)+(a+b)/κ =
      (κ*R^2+(4*(n : ℝ)+24)*Λ+(a+b)*R^2)/(κ*R^2) := by
    field_simp
  rw [he]
  apply (le_div_iff₀ (mul_pos hκ (sq_pos_of_pos hR))).mpr
  apply (mul_le_mul_right (sq_pos_of_pos hR)).mp
  nlinarith

end GaussianTilt.MomentMapRegularity
