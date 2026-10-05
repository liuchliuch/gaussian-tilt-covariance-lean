import GaussianTilt.MomentMapLinearDirichletVariableBoundaryFullExponent
import GaussianTilt.MomentMapLinearDirichletVariableBoundaryCenters

noncomputable section
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 1000
open MeasureTheory Set Filter Matrix
open scoped Topology BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapSchauder
variable {n : ℕ}

/-- All boundary centers in a fixed smaller disk have the actual normal-
mean excess bound, with constants selected before the center and solution.
The weak equation and all L² classes are genuinely translated. -/
theorem exists_variable_boundary_center_full_exponent [NeZero n]
    {lam Λ D β R₀ : ℝ} (hlam : 0 < lam) (hΛ : 0 ≤ Λ) (hD : 0 ≤ D)
    (hβ : 0 < β) (hβ1 : β < 1) (hR₀ : 0 < R₀) :
    ∃ r₀ C N : ℝ, 0 < r₀ ∧ r₀ ≤ R₀/2 ∧ 0 < C ∧ 0 < N ∧
      ∀ (j : Fin n) (Ω : Set (CoordinateSpace n)), (Ω ⊆ {x | 0 < x j}) →
      ∀ u : dirichletSobolev Ω, coordinateHalfBall j R₀ ⊆ Ω →
      ∀ a : KernelSpace n, ‖a‖ ≤ R₀/4 → a j=0 →
      ∀ M : ℝ, 0≤M →
      (∀r:ℝ,0<r → r≤R₀/2 →
        (∫x in upperCampanatoBall j a r,‖euclideanWeakGradient u.1 x‖^2)≤M*r^n) →
      ∀ (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
        (B : Matrix (Fin n) (Fin n) ℝ), B.PosDef →
      (∀ v : KernelSpace n, lam*‖v‖^2 ≤ euclideanQuadratic B v) →
      (∀ v : KernelSpace n, euclideanQuadratic B v ≤ Λ*‖v‖^2) →
      ∀ hAm : ∀ i k, AEStronglyMeasurable (fun x => A x i k) volume,
      ∀ KA : ℝ, ∀ hKA : 0 ≤ KA,
      ∀ hAb : ∀ i k, ∀ᵐ x ∂volume, |A x i k| ≤ KA,
      (∀ i k, ∀ᵐ x ∂volume, x ∈ coordinateHalfBall j R₀ →
        |B i k-A x i k| ≤ D*‖(dirichletCoordinateEquiv n).symm x-a‖^β) →
      ∀ F H : ℝ, 0 ≤ F → 0 ≤ H →
      ∀ (f : Lp ℝ 2 (volume : Measure (CoordinateSpace n)))
        (G : Fin n → Lp ℝ 2 (volume : Measure (CoordinateSpace n))) (c : Fin n → ℝ),
      (∀ᵐ x ∂volume, x ∈ coordinateHalfBall j R₀ → |f x| ≤ F) →
      (∀ k, ∀ᵐ x ∂volume, x ∈ coordinateHalfBall j R₀ →
        |G k x-c k| ≤ H*‖(dirichletCoordinateEquiv n).symm x-a‖^β) →
      (∀ v : dirichletSobolev (coordinateHalfBall j R₀),
        variableJetEnergy A hAm hKA hAb u.1 v.1=variableScalarVectorLoad (coordinateHalfBall j R₀) f G v) →
      ∀ r : ℝ, 0 < r → r ≤ r₀ →
      (∫ x in upperCampanatoBall j a r,
        ‖euclideanWeakGradient u.1 x-normalMean (volume.restrict (upperCampanatoBall j a r)) j
          (euclideanWeakGradient u.1) • EuclideanSpace.basisFun (Fin n) ℝ j‖^2) ≤
        C*(M+N*(2*F+(n:ℝ)*H)^2)*r^((n:ℝ)+2*β) := by
  obtain ⟨r₀,θ,C,N,hr₀,hr₀R,hθ,hθ2,hC,hN,hBound⟩ :=
    exists_variable_halfBall_full_exponent_all_radii (n := n) hlam hΛ hD hβ hβ1 (half_pos hR₀)
  refine ⟨r₀,C,N,hr₀,hr₀R,hC,hN,?_⟩
  intro j Ω hΩ u hDomain a ha haj M hM hEnergy A B hB hlo hhi hAm KA hKA hAb hDb F H hF hH f G c hf hG heq
  let b := dirichletCoordinateEquiv n a
  let Ω' := (fun x : CoordinateSpace n=>x+b) ⁻¹' Ω
  let u' : dirichletSobolev Ω' := ⟨volumeTranslateJet b u.1,volumeTranslateJet_mem_dirichlet b u⟩
  have hmap : ∀ x ∈ coordinateHalfBall j (R₀/2), x+b ∈ coordinateHalfBall j R₀ :=
    fun x hx=>coordinateHalfBall_translate_mem j a haj (by linarith) hx
  have hΩ' : Ω' ⊆ {x | 0 < x j} := by
    intro x hx
    have hh := hΩ hx
    change 0 < x j+a j at hh
    simpa only [haj,add_zero] using hh
  have hDomain' : coordinateHalfBall j (R₀/2) ⊆ Ω' := fun x hx=>hDomain (hmap x hx)
  have hshift : (fun x : CoordinateSpace n=>x-b) ⁻¹' coordinateHalfBall j (R₀/2) ⊆ coordinateHalfBall j R₀ := by
    intro x hx
    have hh := hmap (x-b) hx
    simpa only [sub_add_cancel] using hh
  have hμ := measurePreserving_add_right (volume : Measure (CoordinateSpace n)) b
  have hnorm (x : CoordinateSpace n) : (dirichletCoordinateEquiv n).symm (x+b)-a=(dirichletCoordinateEquiv n).symm x := by
    dsimp [b]
    rw [map_add,ContinuousLinearEquiv.symm_apply_apply,add_sub_cancel_right]
  have hDb' : ∀ i k,∀ᵐ x∂volume,x∈coordinateHalfBall j (R₀/2) →
      |B i k-A (x+b) i k|≤D*‖(dirichletCoordinateEquiv n).symm x‖^β := by
    intro i k
    filter_upwards [hμ.quasiMeasurePreserving.ae (hDb i k)] with x hx hxr
    simpa only [hnorm] using hx (hmap x hxr)
  have hf' : ∀ᵐ x∂volume,x∈coordinateHalfBall j (R₀/2) → |volumeTranslate b f x|≤F := by
    filter_upwards [hμ.quasiMeasurePreserving.ae hf,volumeTranslate_ae b f] with x hx htrans hxr
    rw [htrans]
    exact hx (hmap x hxr)
  have hG' : ∀ k,∀ᵐ x∂volume,x∈coordinateHalfBall j (R₀/2) →
      |volumeTranslate b (G k) x-c k|≤H*‖(dirichletCoordinateEquiv n).symm x‖^β := by
    intro k
    filter_upwards [hμ.quasiMeasurePreserving.ae (hG k),volumeTranslate_ae b (G k)] with x hx htrans hxr
    rw [htrans]
    simpa only [hnorm] using hx (hmap x hxr)
  have heq' := weak_scalar_vector_equation_translate b hshift A hAm hKA hAb u.1 f G heq
  have hEnergy' : ∀r:ℝ,0<r → r≤R₀/2 → halfBallGradientEnergy u'.1 j r≤M*r^n := by
    intro r hr hrR
    have ht:=euclideanWeakGradient_translate_upper_error u.1 j a haj r (0:KernelSpace n)
    simp only [sub_zero] at ht
    change (∫x in upperCampanatoBall j 0 r,‖euclideanWeakGradient (volumeTranslateJet b u.1) x‖^2)≤M*r^n
    rw [ht]
    exact hEnergy r hr hrR
  have hh := hBound j Ω' hΩ' u' hDomain' M hM hEnergy' (fun x=>A (x+b)) B hB hlo hhi
    (translated_coefficient_measurable hAm b) KA hKA (translated_coefficient_bound hAb b) hDb'
    F H hF hH (volumeTranslate b f) (fun k=>volumeTranslate b (G k)) c hf' hG' heq'
  intro r hr hrr₀
  have hb := hh r hr hrr₀
  exact (translated_halfBall_excess_bounds_original_mean u.1 j a haj hr).trans hb

end GaussianTilt.MomentMapLinearDirichlet
