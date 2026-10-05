import GaussianTilt.MomentMapSchauderGlobalChartJetEquation
import GaussianTilt.MomentMapSchauderGlobalFlattenedEllipticity
import GaussianTilt.MomentMapSchauderBoundaryVariableDrift
import GaussianTilt.MomentMapHolderJetEmbedding

/-! # Actual curved-chart a priori bounds with a freely small source-jet term -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 3200000
open Set Filter Matrix
open scoped Topology ContDiff
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapLinearDirichlet GaussianTilt.HolderSpace
variable {n : ℕ}

/-- Compact coefficient families, the genuine smooth inverse chart and
an arbitrary zero-boundary jet produce actual flattened derivative
fields satisfying uniform Schauder bounds. All constants and the radius
are chosen before the test jet and forcing. -/
theorem exists_boundary_target_fields_small_highest [NeZero n]
    {I : Type*} [TopologicalSpace I] {P : Set I} (hP : IsCompact P)
    {S O : Set (KernelSpace n)} (hS : Convex ℝ S) (hSc : IsClosed S) (hO : IsOpen O)
    {α M K : ℝ} (hα : 0 < α) (hα1 : α < 1) (hM : 0 ≤ M) (hK : 0 ≤ K)
    {w : KernelSpace n → ℝ} (hw : ContDiff ℝ ∞ w) (a : KernelSpace n) (q : Fin n)
    (hq : fderiv ℝ w a (EuclideanSpace.basisFun (Fin n) ℝ q)≠0)
    {s : ℝ} (hs : 0 < s) (ψ : KernelSpace n → KernelSpace n) (hψ : ContDiff ℝ ∞ ψ) (hψ0 : ψ 0=a)
    (hmap : MapsTo ψ (flatClosedPatch q 1) S)
    (hmapi : MapsTo ψ (interior (flatClosedPatch q 1)) (interior S))
    (hplane : ∀ z ∈ flatClosedPatch q 1, z q=0 → ψ z ∈ frontier S)
    (hsource : ∀ z ∈ Metric.closedBall (0 : KernelSpace n) 1, ψ z ∈ O)
    (hright : ∀ z ∈ Metric.closedBall (0 : KernelSpace n) 1, scaledFlatteningMap w a q s (ψ z)=z)
    (hleft : ∀ x ∈ O, ‖scaledFlatteningMap w a q s x‖ ≤ 1 → ψ (scaledFlatteningMap w a q s x)=x)
    (A : I → KernelSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hAt : ContinuousOn (fun t => A t a) P)
    (hA0 : ∀ t ∈ P, (A t a).PosDef)
    (hAs : ∀ t ∈ P, ∀ x ∈ S, (A t x).IsSymm)
    (hAb : ∀ t ∈ P, ∀ x ∈ S, ∀ i k, |A t x i k| ≤ M)
    (hAH : ∀ t ∈ P, ∀ x ∈ S, ∀ y ∈ S, ∀ i k, |A t x i k-A t y i k| ≤ K*‖x-y‖^α) :
    ∃ ρ : ℝ, 0 < ρ ∧ 4*ρ ≤ 1 ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ t ∈ P, ∀ J : zeroBoundary (KernelSpace n) ℝ hS α,
      ∀ (f : KernelSpace n → ℝ) (U F H : ℝ), 0 ≤ U → 0 ≤ F → 0 ≤ H →
      (∀ x : S, |value S ℝ α (jetValue (KernelSpace n) ℝ hS α J.1) x| ≤ U) →
      (∀ x ∈ S, |f x| ≤ F) →
      (∀ x ∈ S, ∀ y ∈ S, |f x-f y| ≤ H*‖x-y‖^α) →
      (∀ x ∈ interior S, euclideanEllipticOperator (A t x)
        (extendValue α (jetValue (KernelSpace n) ℝ hS α J.1)) x=f x) →
      ∃ V : Jet (KernelSpace n) ℝ (convex_flatClosedPatch q 1) α,
        (∀ z : flatClosedPatch q 1,
          value (flatClosedPatch q 1) ℝ α (jetValue (KernelSpace n) ℝ (convex_flatClosedPatch q 1) α V) z=
            extendValue α (jetValue (KernelSpace n) ℝ hS α J.1) (ψ z)) ∧
        (∀ z ∈ flatClosedPatch q ρ,
          ‖flatJetFirst q 1 α V z‖ ≤ C*(U+F+H)+ε*‖J‖ ∧
          ‖flatJetSecond q 1 α V z‖ ≤ C*(U+F+H)+ε*‖J‖) ∧
        (∀ z ∈ flatClosedPatch q ρ, ∀ y ∈ flatClosedPatch q ρ,
          ‖flatJetFirst q 1 α V z-flatJetFirst q 1 α V y‖ ≤ (C*(U+F+H)+ε*‖J‖)*‖z-y‖^α) ∧
        (∀ z ∈ flatClosedPatch q ρ, ∀ y ∈ flatClosedPatch q ρ,
          ‖flatJetSecond q 1 α V z-flatJetSecond q 1 α V y‖ ≤ (C*(U+F+H)+ε*‖J‖)*‖z-y‖^α) := by
  let T := flatClosedPatch q 1
  obtain ⟨Cc,hCc,hcomp⟩ := exists_jet_smooth_chart_composition hS (convex_flatClosedPatch q 1)
    (isCompact_flatClosedPatch q 1) (flatClosedPatch_nonempty_interior q zero_lt_one)
    hα hα1.le ψ hψ hmap hmapi
  obtain ⟨Lψ,hLψ1,hLψ⟩ := exists_smoothChartBounds (isCompact_flatClosedPatch q 1)
    (convex_flatClosedPatch q 1) hα.le hα1.le ψ hψ
  let W := Lψ^α
  have hW : 0 ≤ W := Real.rpow_nonneg hLψ.nonneg _
  obtain ⟨B,L,hB,hL,hfields⟩ := exists_uniform_flattened_field_bounds hw a q s hψ hmap
    (isCompact_flatClosedPatch q 1) (convex_flatClosedPatch q 1) hα.le hα1.le hM hK
  obtain ⟨lam,Λ,hlam,hΛ,hell⟩ := exists_uniform_flattenedPrincipal_ellipticity_at_zero hP hw a q hs ψ hψ0 hAt hA0 hq
  obtain ⟨ρ,hρ,hρ1,hest⟩ := exists_boundary_drift_jet_estimate_small_highest (n := n)
    hα hα1 hB.le zero_lt_one hlam hΛ.le hL.le hL.le
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro ε hε
  let η := ε/(Cc+1)
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨C0,hC0,hbase⟩ := hest q η hη
  obtain ⟨C1,hC1,hlower⟩ := halfBall_jet_lower_holder_small_highest_norm q zero_lt_one hα hα1.le hη
  let C := (C0+C1+1)*(1+W)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro t ht J f U F H hU hF hH hu hf hfH heq
  obtain ⟨V,hVnorm,hVu,_,_⟩ := hcomp J.1
  have hVzero : ∀ z : T, (z : KernelSpace n) q=0 →
      value T ℝ α (jetValue (KernelSpace n) ℝ (convex_flatClosedPatch q 1) α V) z=0 := by
    intro z hz
    rw [hVu z]
    exact zeroBoundary_value hS hSc α J (hplane z z.2 hz)
  have hVuB : ∀ z : T, |value T ℝ α (jetValue (KernelSpace n) ℝ (convex_flatClosedPatch q 1) α V) z| ≤ U := by
    intro z
    rw [hVu z,extendValue_mem α _ (hmap z.2)]
    exact hu ⟨ψ z,hmap z.2⟩
  have hfψB : ∀ z ∈ T, |f (ψ z)| ≤ F := fun z hz => hf _ (hmap hz)
  have hfψH : ∀ z ∈ T, ∀ y ∈ T, |f (ψ z)-f (ψ y)| ≤ (H*W)*‖z-y‖^α := by
    intro z hz y hy
    have hp := Real.rpow_le_rpow (norm_nonneg _) (hLψ.lipschitz z hz y hy) hα.le
    rw [Real.mul_rpow hLψ.nonneg (norm_nonneg _)] at hp
    exact (hfH _ (hmap hz) _ (hmap hy)).trans ((mul_le_mul_of_nonneg_left hp hH).trans_eq (by dsimp [W]; ring))
  obtain ⟨hBb,hBH,hLb,hLH⟩ := hfields (A t) (hAb t ht) (hAH t ht)
  have hbc : ContinuousOn (flattenedDrift w q s ψ (A t)) T := continuousOn_of_holder_bound_general hα hLH
  have hAc : ∀ i k, ContinuousOn (fun z => flattenedPrincipal w a q s ψ (A t) z i k) T := by
    intro i k
    apply continuousOn_of_holder_bound_general hα
    intro x hx y hy
    simpa only [Real.norm_eq_abs] using hBH x hx y hy i k
  have hfc : ContinuousOn (f ∘ ψ) T := by
    apply continuousOn_of_holder_bound_general hα
    intro x hx y hy
    simpa only [Real.norm_eq_abs,Function.comp_apply] using hfψH x hx y hy
  have hvEq := chart_jet_flattened_equation hS hO hα J.1 q V hw a s hmapi hsource hright hleft hVu
    (A t) f hAc hbc hfc heq
  have hhalf : flatClosedPatch q ((1:ℝ)/2) ⊆ T := fun z hz =>
    ⟨Metric.closedBall_subset_closedBall (by norm_num) hz.1,hz.2⟩
  have hsmall : flatClosedPatch q ρ ⊆ flatClosedPatch q ((1:ℝ)/2) := fun z hz =>
    ⟨Metric.closedBall_subset_closedBall (by linarith) hz.1,hz.2⟩
  have hvBounds := hbase V hVzero (flattenedPrincipal w a q s ψ (A t)) (flattenedDrift w q s ψ (A t)) (f ∘ ψ)
    (flattenedPrincipal_posDef_at_zero hw a q hs ψ hψ0 (A t) (hA0 t ht) hq)
    (fun v => (hell t ht v).1) (fun v => (hell t ht v).2)
    (fun z hz => flattenedPrincipal_isSymm w a q s ψ (A t) z (hAs t ht _ (hmap (hhalf hz))))
    (fun z hz y hy i k => hBH z (hhalf hz) y (hhalf hy) i k)
    (fun z hz => hLb z (hhalf hz)) (fun z hz y hy => hLH z (hhalf hz) y (hhalf hy))
    (fun z hz => hvEq z (hhalf hz)) U F (H*W) hU hF (mul_nonneg hH hW) hVuB
    (fun z hz => hfψB z (hhalf hz)) (fun z hz y hy => hfψH z (hhalf hz) y (hhalf hy))
  have hvLow := hlower V U hU hVuB
  dsimp only at hvLow
  have hN : ‖jetSecond (KernelSpace n) ℝ (convex_flatClosedPatch q 1) α V‖ ≤ Cc*‖J‖ :=
    (norm_jetSecond_le (convex_flatClosedPatch q 1) α V).trans hVnorm
  have hηC : η*Cc ≤ ε := by
    dsimp [η]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < Cc+1)).mpr
    nlinarith
  have hηN : η*‖jetSecond (KernelSpace n) ℝ (convex_flatClosedPatch q 1) α V‖ ≤ ε*‖J‖ :=
    (mul_le_mul_of_nonneg_left hN hη.le).trans (by nlinarith [mul_le_mul_of_nonneg_right hηC (norm_nonneg J)])
  have hC0C : C0*(U+F+H*W) ≤ C*(U+F+H) := by
    have hC00 : C0 ≤ C := by dsimp [C]; nlinarith
    have hC0W : C0*W ≤ C := by dsimp [C]; nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hC00 hU,mul_le_mul_of_nonneg_right hC00 hF,mul_le_mul_of_nonneg_right hC0W hH]
  have hC1C : C1*U ≤ C*(U+F+H) := by
    have hh : C1 ≤ C := by dsimp [C]; nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hh hU,mul_nonneg hC.le hF,mul_nonneg hC.le hH]
  have heH : C0*(U+F+H*W)+η*flatJetSecondNorm q 1 α V ≤ C*(U+F+H)+ε*‖J‖ := add_le_add hC0C hηN
  have heD : C1*U+η*‖jetSecond (KernelSpace n) ℝ (convex_flatClosedPatch q 1) α V‖ ≤ C*(U+F+H)+ε*‖J‖ := add_le_add hC1C hηN
  refine ⟨V,hVu,?_,?_,?_⟩
  · intro z hz
    exact ⟨((hvLow.1 z (hsmall hz)).1).trans heD,(hvBounds.1 z hz).trans heH⟩
  · intro z hz y hy
    exact (hvLow.2.2 z (hsmall hz) y (hsmall hy)).trans
      (mul_le_mul_of_nonneg_right heD (Real.rpow_nonneg (norm_nonneg _) α))
  · intro z hz y hy
    exact (hvBounds.2 z hz y hy).trans
      (mul_le_mul_of_nonneg_right heH (Real.rpow_nonneg (norm_nonneg _) α))

end GaussianTilt.MomentMapSchauder
