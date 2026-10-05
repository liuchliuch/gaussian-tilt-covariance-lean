import GaussianTilt.MomentMapSchauderCoefficientExtension
import GaussianTilt.MomentMapSchauderCutoffHolder

/-! # Scale-uniform coefficient extension on nested balls

Although the cutoff Hölder constant grows like r⁻α, the coefficient
oscillation shrinks like rᵅ. Their product is radius-independent.
-/
noncomputable section
open Matrix Set
open scoped ContDiff
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma cutoffCoefficient_isSymm {A₀ : Matrix (Fin n) (Fin n) ℝ}
    {A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ} {χ : KernelSpace n → ℝ}
    {S : Set (KernelSpace n)} (hA₀ : A₀.IsSymm)
    (hA : ∀ x ∈ S, (A x).IsSymm) (hχ : ∀ x ∉ S, χ x=0) (x : KernelSpace n) :
    (cutoffCoefficient A₀ A χ x).IsSymm := by
  by_cases hx : x ∈ S
  · exact hA₀.add (((hA x hx).sub hA₀).smul (χ x))
  · rw [cutoffCoefficient_eq_of_zero (hχ x hx)]; exact hA₀

lemma cutoffCoefficient_abs_bound {A₀ : Matrix (Fin n) (Fin n) ℝ}
    {A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ} {χ : KernelSpace n → ℝ}
    {M δ : ℝ} (hA₀ : ∀ i j, |A₀ i j| ≤ M)
    (hclose : ∀ x i j, |A₀ i j-cutoffCoefficient A₀ A χ x i j| ≤ δ) :
    ∀ x i j, |cutoffCoefficient A₀ A χ x i j| ≤ M+δ := by
  intro x i j
  have he : cutoffCoefficient A₀ A χ x i j = A₀ i j-(A₀ i j-cutoffCoefficient A₀ A χ x i j) := by ring
  rw [he]
  exact (abs_sub _ _).trans (add_le_add (hA₀ i j) (hclose x i j))

lemma scaled_coefficient_holder_algebra {r : ℝ} (hr : 0 < r) (K B α : ℝ) :
    K*(4*r)^α*((B+2)*(2*r)^(-α)) = K*(B+2)*2^α := by
  have hp : (4*r : ℝ)=2*(2*r) := by ring
  rw [hp, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity : 0 ≤ 2*r),
    Real.rpow_neg (by positivity : 0 ≤ 2*r)]
  have hn : (2*r)^α ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos (by positivity) α)
  field_simp

/-- One fixed constant controls the Hölder seminorm of every constructed
coefficient extension, independently of its ball radius. -/
theorem exists_scaled_coefficient_extension_bound {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ B : ℝ, 0 < B ∧ ∀ a : KernelSpace n, ∀ r K : ℝ, 0 < r → 0 ≤ K →
      ∀ A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ,
      (∀ x ∈ Metric.closedBall a (4*r), ∀ y ∈ Metric.closedBall a (4*r), ∀ i j,
        |A x i j-A y i j| ≤ K*‖x-y‖^α) →
      let Ā := cutoffCoefficient (A a) A (scaledInteriorCutoff a (2*r))
      (∀ x i j, |A a i j-Ā x i j| ≤ K*(4*r)^α) ∧
      (∀ x y i j, |Ā x i j-Ā y i j| ≤ (K*B)*‖x-y‖^α) ∧
      (∀ x ∈ Metric.closedBall a (2*r), Ā x=A x) := by
  obtain ⟨B₁, B₂, B₃, hB₁, hB₂, hB₃, hb⟩ :=
    exists_scaled_cutoff_jet_holder_bounds (E := KernelSpace n) hα hα1
  refine ⟨1+(B₁+2)*2^α, by positivity, ?_⟩
  intro a r K hr hK A hAH
  dsimp only
  let ψ := scaledInteriorCutoff a (2*r)
  have hψb : ∀ x, |ψ x| ≤ 1 := by
    intro x
    rw [abs_of_nonneg (scaledInteriorCutoff_nonneg a x (2*r))]
    exact scaledInteriorCutoff_le_one a x (2*r)
  have hψh := (hb a (2*r) (by positivity)).2.2.1
  have hψz : ∀ x ∉ Metric.closedBall a (4*r), ψ x=0 := by
    intro x hx
    apply scaledInteriorCutoff_zero (by positivity)
    have hn : 4*r < ‖x-a‖ := by simpa only [Metric.mem_closedBall, dist_eq_norm, not_le] using hx
    linarith
  have hclose : ∀ x ∈ Metric.closedBall a (4*r), ∀ i j, |A a i j-A x i j| ≤ K*(4*r)^α := by
    intro x hx i j
    have hh := hAH a (Metric.mem_closedBall_self (by positivity)) x hx i j
    have hn : ‖a-x‖ ≤ 4*r := by simpa only [norm_sub_rev, Metric.mem_closedBall, dist_eq_norm] using hx
    exact hh.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hn hα) hK)
  refine ⟨cutoffCoefficient_close (by positivity) hψb hψz hclose, ?_, ?_⟩
  · intro x y i j
    have hh := cutoffCoefficient_holder (χ := ψ) (by positivity) hK (by positivity)
      hψb hψh hψz hclose hAH x y i j
    convert hh using 1
    rw [scaled_coefficient_holder_algebra hr]
    ring
  · intro x hx
    exact cutoffCoefficient_eq_of_one (scaledInteriorCutoff_one (by positivity)
      (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx))

/-- A positive radius can be chosen to meet any prescribed coefficient
oscillation threshold, with no lower bound assumed for the original scale. -/
theorem exists_small_holder_radius {α K R ε : ℝ}
    (hα : 0 < α) (hK : 0 ≤ K) (hR : 0 < R) (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ 4*r ≤ R ∧ K*(4*r)^α ≤ ε := by
  let t : ℝ := (ε/(K+1)) ^ α⁻¹
  have ht : 0 < t := Real.rpow_pos_of_pos (by positivity) _
  have htp : t^α=ε/(K+1) := by
    dsimp [t]
    rw [← Real.rpow_mul (by positivity : 0 ≤ ε/(K+1)), inv_mul_cancel₀ hα.ne', Real.rpow_one]
  let r : ℝ := min R t / 4
  have hr : 0 < r := by dsimp [r]; exact div_pos (lt_min hR ht) (by norm_num)
  have h4 : 4*r=min R t := by dsimp [r]; ring
  refine ⟨r, hr, by rw [h4]; exact min_le_left _ _, ?_⟩
  have hb := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity : 0 ≤ 4*r)
    (show 4*r ≤ t by rw [h4]; exact min_le_right _ _) hα.le) hK
  rw [htp] at hb
  apply hb.trans
  have hk : K/(K+1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  calc
    K*(ε/(K+1)) = ε*(K/(K+1)) := by ring
    _ ≤ ε*1 := mul_le_mul_of_nonneg_left hk hε.le
    _ = ε := mul_one _

end GaussianTilt.MomentMapSchauder
