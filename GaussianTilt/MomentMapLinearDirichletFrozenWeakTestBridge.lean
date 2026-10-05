import GaussianTilt.MomentMapLinearDirichletVariableWeakTestClosure

/-! # Exact frozen symmetric energy-to-compact-test conversion -/
noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory Set Filter Matrix
open scoped Topology BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin
variable {n : ℕ}

/-- Symmetry converts the real weak energy orientation to the literal
constant-matrix divergence equation used by the genuine affine transport. -/
theorem constant_energy_zero_compact_tests {D : Set (CoordinateSpace n)}
    (B : Matrix (Fin n) (Fin n) ℝ) (hBs : ∀ i k, B i k=B k i)
    (hBm : ∀ i k, AEStronglyMeasurable (fun _ : CoordinateSpace n => B i k) volume)
    {KB : ℝ} (hKB : 0 ≤ KB)
    (hBb : ∀ i k, ∀ᵐ x ∂(volume : Measure (CoordinateSpace n)), |B i k| ≤ KB)
    (u : VolumeJet n)
    (heq : ∀ v : dirichletSobolev D, variableJetEnergy (fun _ => B) hBm hKB hBb u v.1=0) :
    ∀ τ : smoothCompactCore n, tsupport τ.1 ⊆ D →
      (∫ x, (fun i : Fin n => u i.succ x) ⬝ᵥ (B*ᵥcoordinateGradient τ.1 x))=0 := by
  intro τ hτ
  have hh := heq (dirichletCoreToSobolev D ⟨τ,hτ⟩)
  change variableJetEnergy (fun _ => B) hBm hKB hBb u (smoothCompactJet volume τ)=0 at hh
  rw [variableJetEnergy_smooth_test] at hh
  convert hh using 1
  apply integral_congr_ae
  apply ae_of_all
  intro x
  simp only [dotProduct,mulVec,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  rw [hBs k i]
  change u k.succ x * (B i k * coordinateDerivative i τ.1 x) = _
  ring

end GaussianTilt.MomentMapLinearDirichlet
