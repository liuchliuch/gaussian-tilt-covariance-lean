import GaussianTilt.MomentMapSchauderLocalizedEstimate
import GaussianTilt.MomentMapSchauderScaledCoefficients

/-! # Interior Schauder control from step-uniform first-jet data

The coefficient field is genuinely local. A constructed extension and two
scaled cutoffs discharge every global hypothesis of the compact estimate.
The final radius and constant are uniform over the potential and over its
initial second-derivative bounds.
-/
noncomputable section
open Matrix Set
open scoped ContDiff
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

set_option maxHeartbeats 1200000 in
theorem exists_interior_first_jet_schauder [NeZero n]
    {α lam Λ K M R : ℝ} (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam)
    (hΛ : 0 ≤ Λ) (hK : 0 ≤ K) (hM : 0 ≤ M) (hR : 0 < R) :
    ∃ r C : ℝ, 0 < r ∧ 4*r ≤ R ∧ 0 < C ∧
      ∀ a : KernelSpace n, ∀ A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ,
      (A a).PosDef →
      (∀ v : KernelSpace n, lam*‖v‖^2 ≤ euclideanQuadratic (A a) v) →
      (∀ v : KernelSpace n, euclideanQuadratic (A a) v ≤ Λ*‖v‖^2) →
      (∀ i j, |A a i j| ≤ M) →
      (∀ x ∈ Metric.closedBall a R, (A x).IsSymm) →
      (∀ x ∈ Metric.closedBall a R, ∀ y ∈ Metric.closedBall a R, ∀ i j,
        |A x i j-A y i j| ≤ K*‖x-y‖^α) →
      ∀ u f : KernelSpace n → ℝ, ContDiff ℝ 2 u →
      ∀ U D J HU HD HJ F H : ℝ,
      0 ≤ U → 0 ≤ D → 0 ≤ J → 0 ≤ HU → 0 ≤ HD → 0 ≤ HJ → 0 ≤ F → 0 ≤ H →
      (∀ x ∈ Metric.closedBall a R, |u x| ≤ U) →
      (∀ x ∈ Metric.closedBall a R, ‖fderiv ℝ u x‖ ≤ D) →
      (∀ x ∈ Metric.closedBall a R, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ J) →
      (∀ x ∈ Metric.closedBall a R, ∀ y ∈ Metric.closedBall a R, |u x-u y| ≤ HU*‖x-y‖^α) →
      (∀ x ∈ Metric.closedBall a R, ∀ y ∈ Metric.closedBall a R,
        ‖fderiv ℝ u x-fderiv ℝ u y‖ ≤ HD*‖x-y‖^α) →
      (∀ x ∈ Metric.closedBall a R, ∀ y ∈ Metric.closedBall a R,
        ‖fderiv ℝ (fderiv ℝ u) x-fderiv ℝ (fderiv ℝ u) y‖ ≤ HJ*‖x-y‖^α) →
      (∀ x ∈ Metric.closedBall a R, |f x| ≤ F) →
      (∀ x ∈ Metric.closedBall a R, ∀ y ∈ Metric.closedBall a R, |f x-f y| ≤ H*‖x-y‖^α) →
      (∀ x ∈ Metric.closedBall a R, euclideanEllipticOperator (A x) u x=f x) →
      (∀ x ∈ Metric.ball a r, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ C*(U+D+HU+HD+F+H)) ∧
      (∀ x ∈ Metric.ball a r, ∀ y ∈ Metric.ball a r,
        ‖fderiv ℝ (fderiv ℝ u) x-fderiv ℝ (fderiv ℝ u) y‖ ≤ C*(U+D+HU+HD+F+H)*‖x-y‖^α) := by
  obtain ⟨B, hB, hext⟩ := exists_scaled_coefficient_extension_bound (n := n) hα.le hα1.le
  have hKB : 0 ≤ K*B := mul_nonneg hK hB.le
  obtain ⟨ε, C₀, hε, hC₀, hbase⟩ := exists_localized_small_oscillation_schauder
    (n := n) hα hα1 hlam hΛ hKB
  obtain ⟨r, hr, hrR, hosc⟩ := exists_small_holder_radius hα hK hR (lt_min hε zero_lt_one)
  obtain ⟨B₁, B₂, B₃, hB₁, hB₂, hB₃, hcut⟩ :=
    exists_scaled_cutoff_jet_holder_bounds (E := KernelSpace n) hα.le hα1.le
  let C₁ := B₁/r
  let C₂ := B₂/r^2
  let L₀ := (B₁+2)*r^(-α)
  let L₁ := (B₂+2*B₁)*r^(-1-α)
  let L₂ := (B₃+2*B₂)*r^(-2-α)
  have hC₁ : 0 ≤ C₁ := by dsimp [C₁]; positivity
  have hC₂ : 0 ≤ C₂ := by dsimp [C₂]; positivity
  have hL₀ : 0 ≤ L₀ := by dsimp [L₀]; positivity
  have hL₁ : 0 ≤ L₁ := by dsimp [L₁]; positivity
  have hL₂ : 0 ≤ L₂ := by dsimp [L₂]; positivity
  let P := C₂+2*C₁
  let Q := C₂+L₂+2*(C₁+L₁)
  let C := C₀*(1+(1+(n : ℝ)^2*(M+1)*P)+(1+L₀+(n : ℝ)^2*((M+1)*Q+(K*B)*P)))
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨r, C, hr, hrR, hC, ?_⟩
  intro a A hAa hlow hupp hAab hAs hAH u f hu U D J HU HD HJ F H
    hU hD hJ hHU hHD hHJ hF hH hub hDu hD2u huH hDuH hD2uH hfb hfH heq
  let ψ := scaledInteriorCutoff a (2*r)
  let χ := scaledInteriorCutoff a r
  let Ā := cutoffCoefficient (A a) A ψ
  have hsub₄ : Metric.closedBall a (4*r) ⊆ Metric.closedBall a R := Metric.closedBall_subset_closedBall hrR
  have hsub₂ : Metric.closedBall a (2*r) ⊆ Metric.closedBall a R :=
    Metric.closedBall_subset_closedBall (by linarith)
  have he := hext a r K hr hK A (fun x hx y hy => hAH x (hsub₄ hx) y (hsub₄ hy))
  have hc : ∀ x i j, |A a i j-Ā x i j| ≤ ε := fun x i j =>
    (he.1 x i j).trans (hosc.trans (min_le_left _ _))
  have hb : ∀ x i j, |Ā x i j| ≤ M+1 := by
    intro x i j
    exact (cutoffCoefficient_abs_bound hAab he.1 x i j).trans
      (add_le_add_left (hosc.trans (min_le_right _ _)) M)
  have hs : ∀ x, (Ā x).IsSymm := cutoffCoefficient_isSymm (hAs a (Metric.mem_closedBall_self hR.le))
    (fun x hx => hAs x (hsub₄ hx)) (fun x hx => by
      apply scaledInteriorCutoff_zero (by positivity)
      have hn : 4*r < ‖x-a‖ := by simpa only [Metric.mem_closedBall, dist_eq_norm, not_le] using hx
      linarith)
  have hχb : ∀ x, |χ x| ≤ 1 := fun x => by
    rw [abs_of_nonneg (scaledInteriorCutoff_nonneg a x r)]
    exact scaledInteriorCutoff_le_one a x r
  have hcut' := hcut a r hr
  have heqbar : ∀ x ∈ Metric.closedBall a (2*r), euclideanEllipticOperator (Ā x) u x=f x := by
    intro x hx
    change euclideanEllipticOperator (cutoffCoefficient (A a) A ψ x) u x=f x
    rw [he.2.2 x hx]
    exact heq x (hsub₂ hx)
  have hloc := hbase (A a) hAa hlow hupp Ā hs hc he.2.1 χ u f hu
    (contDiff_infty.mp (scaledInteriorCutoff_contDiff a r) 2) (scaledInteriorCutoff_compact a hr)
    (Metric.closedBall a (2*r)) (Metric.ball a r) Metric.isOpen_ball
    (tsupport_scaledInteriorCutoff_subset a hr)
    (fun x hx => scaledInteriorCutoff_one hr (Metric.mem_closedBall.mp (Metric.ball_subset_closedBall hx)))
    (M+1) 1 C₁ C₂ L₀ L₁ L₂ U D J HU HD HJ F H
    (by positivity) zero_le_one hC₁ hC₂ hL₀ hL₁ hL₂ hU hD hJ hHU hHD hHJ hF hH
    hb hχb hcut'.1 hcut'.2.1 hcut'.2.2.1 hcut'.2.2.2.1 hcut'.2.2.2.2
    (fun x hx => hub x (hsub₂ hx)) (fun x hx => hDu x (hsub₂ hx))
    (fun x hx => hD2u x (hsub₂ hx))
    (fun x hx y hy => huH x (hsub₂ hx) y (hsub₂ hy))
    (fun x hx y hy => hDuH x (hsub₂ hx) y (hsub₂ hy))
    (fun x hx y hy => hD2uH x (hsub₂ hx) y (hsub₂ hy))
    (fun x hx => hfb x (hsub₂ hx)) (fun x hx y hy => hfH x (hsub₂ hx) y (hsub₂ hy))
    heqbar
  dsimp only at hloc
  let T := U+D+HU+HD+F+H
  have hUT : U ≤ T := by dsimp [T]; linarith
  have hDT : D ≤ T := by dsimp [T]; linarith
  have hHUT : HU ≤ T := by dsimp [T]; linarith
  have hHDT : HD ≤ T := by dsimp [T]; linarith
  have hFT : F ≤ T := by dsimp [T]; linarith
  have hHT : H ≤ T := by dsimp [T]; linarith
  have hrest : C₂*U+2*(C₁*D) ≤ P*T := by
    dsimp [P]
    calc
      _ ≤ C₂*T+2*(C₁*T) := add_le_add (mul_le_mul_of_nonneg_left hUT hC₂)
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hDT hC₁) (by norm_num))
      _ = _ := by ring
  have hrestH : C₂*HU+U*L₂+2*(C₁*HD+D*L₁) ≤ Q*T := by
    dsimp [Q]
    calc
      _ ≤ C₂*T+T*L₂+2*(C₁*T+T*L₁) := by gcongr
      _ = _ := by ring
  have hbound : C₀*(1*U+(1*F+(n : ℝ)^2*(M+1)*(C₂*U+2*(C₁*D)))+
      (1*H+F*L₀+(n : ℝ)^2*((M+1)*(C₂*HU+U*L₂+2*(C₁*HD+D*L₁))+(K*B)*(C₂*U+2*(C₁*D))))) ≤ C*T := by
    calc
      _ ≤ C₀*(T+(T+(n : ℝ)^2*(M+1)*(P*T))+
        (T+T*L₀+(n : ℝ)^2*((M+1)*(Q*T)+(K*B)*(P*T)))) := by
          simp only [one_mul]
          gcongr
      _ = C*T := by dsimp [C]; ring
  constructor
  · intro x hx
    exact (hloc.1 x hx).trans hbound
  · intro x hx y hy
    exact (hloc.2 x hx y hy).trans (mul_le_mul_of_nonneg_right hbound (Real.rpow_nonneg (norm_nonneg _) α))

end GaussianTilt.MomentMapSchauder
