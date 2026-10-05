import GaussianTilt.MomentMapLinearDirichletTangentialDifferenceCaccioppoli

/-! # Actual H¹ tangential derivatives from uniform quotient energies

A bounded sequence of the constructed tangential cutoff quotients has
strongly convergent L² values. Genuine Hilbert weak compactness in the
closed Dirichlet graph then constructs the higher weak derivative jet.
-/
noncomputable section
set_option maxHeartbeats 2500000
open MeasureTheory Set Filter Matrix
open scoped Topology ContDiff BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin
variable {n : ℕ}

/-- The quotient energy estimate produces an actual higher H₀¹ jet. The
limit value is literally the cutoff times the original weak derivative. -/
theorem exists_tangential_cutoff_derivative_of_quotient_load_bound
    {U : Set (CoordinateSpace n)} (q i : Fin n) (hi : i≠q)
    (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hAm : ∀ p k, AEStronglyMeasurable (fun x=>A x p k) volume)
    {K lam : ℝ} (hK : 0≤K) (hAb : ∀ p k, ∀ᵐ x ∂volume, |A x p k|≤K) (hlam : 0<lam)
    (hell : ∀ᵐ x ∂volume, ∀ z : Fin n→ℝ, lam*(∑ k,(z k)^2)≤z ⬝ᵥ (A x *ᵥ z))
    (a : smoothCompactCore n) (ha : tsupport a.1 ∩ {x : CoordinateSpace n | 0<x q}⊆U)
    {B D L : ℝ} (hB : 0≤B) (hD : 0≤D) (hL : 0≤L)
    (hb : ∀ x, |a.1 x|≤B) (hd : ∀ k x, |coordinateDerivative k a.1 x|≤D)
    (u : dirichletSobolev {x : CoordinateSpace n | 0<x q})
    {ε : ℝ} (hε : 0<ε)
    (hload : ∀ h : ℝ, 0 < |h| → |h| < ε → ∀ v : dirichletSobolev U,
      |variableJetEnergy A hAm hK hAb (volumeDifferenceJet i h u.1) v.1|≤L*jetGradientNorm v.1) :
    ∃ v : dirichletSobolev U,
      dirichletValue U v=smoothCoreL2Multiply a (u.1 i.succ) ∧
      ‖v‖≤cutoffEnergyBound n lam K B D L ‖u.1 i.succ‖ := by
  let h : ℕ→ℝ := fun k=>ε/((k:ℝ)+2)
  have hhpos (k : ℕ) : 0<h k := div_pos hε (by positivity)
  have hhsmall (k : ℕ) : |h k|<ε := by
    rw [abs_of_pos (hhpos k)]
    dsimp [h]
    apply (div_lt_iff₀ (by positivity : 0<(k:ℝ)+2)).mpr
    nlinarith [Nat.cast_nonneg (α:=ℝ) k]
  let w : ℕ→dirichletSobolev {x : CoordinateSpace n | 0<x q} :=
    fun k=>⟨volumeDifferenceJet i (h k) u.1,volumeDifferenceJet_mem_halfspace q i hi (h k) u⟩
  let v : ℕ→dirichletSobolev U := fun k=>dirichletSmoothMultiply a ha (w k)
  have hbnd (k : ℕ) : ‖v k‖≤cutoffEnergyBound n lam K B D L ‖u.1 i.succ‖ := by
    apply norm_cutoff_jet_le_of_weak_load_bound A hAm hK hAb hlam hell a ha
      hB hD hL (norm_nonneg _) hb hd (w k)
    · exact norm_dirichletDifferenceQuotient_le u i (h k)
    · exact hload (h k) (by rw [abs_of_pos (hhpos k)]; exact hhpos k) (hhsmall k)
  have ht : Tendsto h atTop (𝓝 (0:ℝ)) := by
    have hden : Tendsto (fun k : ℕ=>(k:ℝ)+2) atTop atTop :=
      tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
    simpa only [mul_zero] using (tendsto_inv_atTop_zero.comp hden).const_mul ε
  have ht' : Tendsto h atTop (𝓝[≠] (0:ℝ)) := tendsto_nhdsWithin_iff.mpr
    ⟨ht,Eventually.of_forall (fun k=>ne_of_gt (hhpos k))⟩
  have hv : Tendsto (fun k=>dirichletValue U (v k)) atTop
      (𝓝 (smoothCoreL2Multiply a (u.1 i.succ))) :=
    (smoothCoreL2Multiply_difference_tendsto a u i).comp ht'
  exact exists_dirichlet_lift_of_eventual_norm_bound v
    (fun δ hδ=>Eventually.of_forall (fun k=>(hbnd k).trans (by linarith))) hv

end GaussianTilt.MomentMapLinearDirichlet
