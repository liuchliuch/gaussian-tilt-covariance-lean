import GaussianTilt.MomentMapRegularityConstantDensityCalabiSymmetry

/-!
# Genuine cutoff maximum estimates for the Calabi differential inequality

All product/gradient identities are differentiated from the actual cutoff
and energy. Compact maximization removes the boundary without assuming
maximum attainment for a singular logarithmic quantity.
-/
noncomputable section
open Matrix Filter Set
open scoped BigOperators Topology ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

lemma coordinateHessian_mul_at {f g : CoordinateSpace n → ℝ} {x : CoordinateSpace n}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    coordinateHessian (fun y => f y * g y) x =
      f x • coordinateHessian g x + g x • coordinateHessian f x +
      vecMulVec (coordinateGradient f x) (coordinateGradient g x) +
      vecMulVec (coordinateGradient g x) (coordinateGradient f x) := by
  ext i j
  have he : coordinateDerivative i (fun y => f y * g y) =ᶠ[𝓝 x]
      (fun y => coordinateDerivative i f y * g y + f y * coordinateDerivative i g y) := by
    filter_upwards [hf.eventually (by simp), hg.eventually (by simp)] with y hyf hyg
    exact coordinateDerivative_mul_at (hyf.differentiableAt (by norm_num))
      (hyg.differentiableAt (by norm_num)) i
  change coordinateDerivative j (coordinateDerivative i (fun y => f y * g y)) x = _
  rw [coordinateDerivative_congr_nhds he j]
  have hfd := hf.differentiableAt (by norm_num)
  have hgd := hg.differentiableAt (by norm_num)
  have hfi := (contDiffAt_coordinateDerivative hf (m := 1) (by norm_num) i).differentiableAt le_rfl
  have hgi := (contDiffAt_coordinateDerivative hg (m := 1) (by norm_num) i).differentiableAt le_rfl
  rw [coordinateDerivative_add_at (hfi.fun_mul hgd) (hfd.fun_mul hgi),
    coordinateDerivative_mul_at hfi hgd, coordinateDerivative_mul_at hfd hgi]
  change _ = f x * coordinateHessian g x i j + g x * coordinateHessian f x i j +
    coordinateDerivative i f x * coordinateDerivative j g x + coordinateDerivative i g x * coordinateDerivative j f x
  change coordinateHessian f x i j * g x + coordinateDerivative i f x * coordinateDerivative j g x +
    (coordinateDerivative j f x * coordinateDerivative i g x + f x * coordinateHessian g x i j) = _
  ring

lemma linearizedMA_mul_at {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    {f g : CoordinateSpace n → ℝ} {x : CoordinateSpace n}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    linearizedMA A (fun y => f y * g y) x =
      f x * linearizedMA A g x + g x * linearizedMA A f x +
      2 * (coordinateGradient f x ⬝ᵥ (A *ᵥ coordinateGradient g x)) := by
  unfold linearizedMA
  rw [coordinateHessian_mul_at hf hg]
  simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul,
    Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, smul_eq_mul]
  rw [← symmetric_dot_mulVec A hA, dotProduct_comm (A *ᵥ coordinateGradient g x)]
  ring

lemma coordinateGradient_sq_at {f : CoordinateSpace n → ℝ} {x : CoordinateSpace n}
    (hf : DifferentiableAt ℝ f x) :
    coordinateGradient (fun y => (f y)^2) x = (2 * f x) • coordinateGradient f x := by
  ext i
  change coordinateDerivative i (fun y => (f y)^2) x = _
  simp only [pow_two]
  rw [coordinateDerivative_mul_at hf hf]
  change _ = 2 * f x * coordinateDerivative i f x
  ring

/-- At the maximum of the actual cutoff energy, its first derivative fixes
the cross term exactly. -/
lemma cutoff_energy_stationarity {η F : CoordinateSpace n → ℝ} {x : CoordinateSpace n}
    (hη : DifferentiableAt ℝ η x) (hF : DifferentiableAt ℝ F x) (hηx : η x ≠ 0)
    (hmax : IsLocalMax (fun y => (η y)^2 * F y) x) :
    coordinateGradient F x = -(2 * F x / η x) • coordinateGradient η x := by
  have hz := hmax.fderiv_eq_zero
  ext i
  have hi : coordinateDerivative i (fun y => (η y)^2 * F y) x = 0 := by
    simp [coordinateDerivative, hz]
  rw [coordinateDerivative_mul_at (f := fun y => (η y)^2) (hη.pow 2) hF] at hi
  have hηi : coordinateDerivative i (fun y => (η y)^2) x = 2 * η x * coordinateDerivative i η x := by
    exact congrFun (coordinateGradient_sq_at hη) i
  rw [hηi] at hi
  change coordinateDerivative i F x = -(2 * F x / η x) * coordinateDerivative i η x
  have hfac : η x * (2 * coordinateDerivative i η x * F x + η x * coordinateDerivative i F x) = 0 := by
    nlinarith [hi]
  have hzero := (mul_eq_zero.mp hfac).resolve_left hηx
  field_simp
  nlinarith

/-- Exact local product calculation for the cutoff maximum. -/
lemma linearized_cutoff_energy_at_max {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    {η F : CoordinateSpace n → ℝ} {x : CoordinateSpace n}
    (hη : ContDiffAt ℝ 2 η x) (hF : ContDiffAt ℝ 2 F x) (hηx : η x ≠ 0)
    (hmax : IsLocalMax (fun y => (η y)^2 * F y) x) :
    linearizedMA A (fun y => (η y)^2 * F y) x =
      (η x)^2 * linearizedMA A F x + 2 * η x * F x * linearizedMA A η x -
      6 * F x * (coordinateGradient η x ⬝ᵥ (A *ᵥ coordinateGradient η x)) := by
  rw [linearizedMA_mul_at hA (hη.pow 2) hF]
  have hη2 : linearizedMA A (fun y => (η y)^2) x =
      2 * η x * linearizedMA A η x + 2 * (coordinateGradient η x ⬝ᵥ (A *ᵥ coordinateGradient η x)) := by
    have he : (fun y => (η y)^2) = fun y => η y * η y := by funext y; ring
    rw [he, linearizedMA_mul_at hA hη hη]
    ring
  rw [hη2, coordinateGradient_sq_at (hη.differentiableAt (by norm_num)),
    cutoff_energy_stationarity (hη.differentiableAt (by norm_num)) (hF.differentiableAt (by norm_num)) hηx hmax]
  simp only [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  field_simp
  ring

/-- A genuine local maximum bound from a quadratic differential inequality,
with fully explicit cutoff constants. -/
theorem calabi_cutoff_bound_at_max {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef)
    {η F : CoordinateSpace n → ℝ} {x : CoordinateSpace n}
    (hη : ContDiffAt ℝ 2 η x) (hF : ContDiffAt ℝ 2 F x)
    {c B₀ B₁ B₂ : ℝ} (hc : 0 < c) (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hηx : 0 < η x) (hηB : η x ≤ B₀) (hFx : 0 < F x)
    (hLF : c * (F x)^2 ≤ linearizedMA A F x)
    (hLη : -B₁ ≤ linearizedMA A η x)
    (hΓ : coordinateGradient η x ⬝ᵥ (A *ᵥ coordinateGradient η x) ≤ B₂)
    (hmax : IsLocalMax (fun y => (η y)^2 * F y) x) :
    (η x)^2 * F x ≤ (2 * B₀ * B₁ + 6 * B₂) / c := by
  have hAs : A.IsSymm := by
    simpa only [Matrix.IsSymm, Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hA.isHermitian
  have hnon := linearizedMA_nonpos_at_max hA ((hη.pow 2).mul hF) hmax
  rw [linearized_cutoff_energy_at_max hAs hη hF hηx.ne' hmax] at hnon
  have h1 := mul_le_mul_of_nonneg_left hLF (sq_nonneg (η x))
  have h2 := mul_le_mul_of_nonneg_left hLη (show 0 ≤ 2 * η x * F x by positivity)
  have h3 := mul_le_mul_of_nonneg_left hΓ (show 0 ≤ 6 * F x by positivity)
  have h4 := mul_le_mul_of_nonneg_right hηB (show 0 ≤ 2 * B₁ * F x by positivity)
  apply (le_div_iff₀ hc).mpr
  have hprod : (c * (η x)^2 * F x - (2 * B₀ * B₁ + 6 * B₂)) * F x ≤ 0 := by nlinarith
  have hle := (mul_le_mul_right hFx).mp (show
      (c * (η x)^2 * F x - (2 * B₀ * B₁ + 6 * B₂)) * F x ≤ 0 * F x by simpa using hprod)
  nlinarith

/-- Compact maximization supplies the cutoff bound throughout the domain;
maximum attainment is a conclusion of compactness, not an extra premise. -/
theorem calabi_cutoff_bound_on_compact
    {S : Set (CoordinateSpace n)} (hS : IsCompact S)
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ}
    {η F : CoordinateSpace n → ℝ} (hη : ContDiff ℝ 2 η) (hF : ContDiff ℝ 2 F)
    (hAz : ∀ y ∈ interior S, (A y).PosSemidef)
    (hzero : ∀ y ∈ frontier S, η y = 0)
    (hηpos : ∀ y ∈ interior S, 0 < η y)
    {c B₀ B₁ B₂ : ℝ} (hc : 0 < c) (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hηB : ∀ y ∈ interior S, η y ≤ B₀)
    (hLF : ∀ y ∈ interior S, c * (F y)^2 ≤ linearizedMA (A y) F y)
    (hLη : ∀ y ∈ interior S, -B₁ ≤ linearizedMA (A y) η y)
    (hΓ : ∀ y ∈ interior S, coordinateGradient η y ⬝ᵥ (A y *ᵥ coordinateGradient η y) ≤ B₂) :
    ∀ x ∈ S, (η x)^2 * F x ≤ (2 * B₀ * B₁ + 6 * B₂) / c := by
  intro x hx
  have hbound0 : 0 ≤ (2 * B₀ * B₁ + 6 * B₂) / c := by positivity
  by_cases hFx : (η x)^2 * F x ≤ 0
  · exact hFx.trans hbound0
  have hFx : 0 < (η x)^2 * F x := lt_of_not_ge hFx
  obtain ⟨z, hz, hmax⟩ := hS.exists_isMaxOn ⟨x, hx⟩ ((hη.continuous.pow 2).mul hF.continuous).continuousOn
  have hxz : (η x)^2 * F x ≤ (η z)^2 * F z := hmax hx
  have hzi : z ∈ interior S := by
    by_contra hnot
    have hzb : z ∈ frontier S := ⟨subset_closure hz, hnot⟩
    rw [hzero z hzb] at hxz
    norm_num at hxz
    exact hFx.not_ge hxz
  have hFz : 0 < F z := by
    have hh : 0 < (η z)^2 * F z := hFx.trans_le hxz
    exact (mul_pos_iff_of_pos_left (sq_pos_of_pos (hηpos z hzi))).mp hh
  exact hxz.trans (calabi_cutoff_bound_at_max (hAz z hzi) hη.contDiffAt hF.contDiffAt
    hc hB₀ hB₁ hB₂ (hηpos z hzi) (hηB z hzi) hFz (hLF z hzi) (hLη z hzi) (hΓ z hzi)
    (hmax.isLocalMax (mem_interior_iff_mem_nhds.mp hzi)))

end GaussianTilt.MomentMapRegularity
