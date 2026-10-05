import GaussianTilt.NegativeSobolevSpace

/-! # Closability of the actual weighted gradient

Weighted integration by parts extends from the constructed smooth core to its
Hilbert closure.  Consequently the value coordinate is injective: the closed
jet completion really is a space of functions with uniquely determined weak
derivatives, not a larger space containing spurious derivative coordinates.
-/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ContDiff Topology ENNReal InnerProductSpace
namespace GaussianTilt.Letwin

lemma inner_smoothCompactToL2 {n : ℕ} (μ : Measure (CoordinateSpace n)) [IsFiniteMeasureOnCompacts μ]
    (f g : smoothCompactCore n) :
    inner ℝ (smoothCompactToL2 μ f) (smoothCompactToL2 μ g) = ∫ x, f.1 x * g.1 x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [smoothCompactToL2_ae μ f, smoothCompactToL2_ae μ g] with x hx hy
  simp only [hx, hy, RCLike.inner_apply, conj_trivial]
  ring

/-- The actual formal adjoint D_i* g = (D_i φ)g - D_i g on the smooth core. -/
def smoothCompactDerivativeAdjoint {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (i : Fin n) (g : smoothCompactCore n) : smoothCompactCore n :=
  ⟨fun x => coordinateDerivative i φ x * g.1 x - coordinateDerivative i g.1 x,
    ((smooth_coordinateDerivative hφ i).mul g.2.1).sub (smooth_coordinateDerivative g.2.1 i),
    g.2.2.mul_left.sub (g.2.2.fderiv_apply (𝕜 := ℝ) (Pi.single i 1))⟩

/-- The actual derivative and the actual formal adjoint satisfy the Hilbert
pairing identity, derived from weighted integration by parts. -/
theorem smoothCompactDerivative_adjoint {n : ℕ} {φ : CoordinateSpace n → ℝ}
    [IsFiniteMeasureOnCompacts (potentialMeasure φ)] (hφ : ContDiff ℝ ∞ φ) (i : Fin n)
    (f g : smoothCompactCore n) :
    inner ℝ (smoothCompactToL2 (potentialMeasure φ) (smoothCompactDerivative i f))
      (smoothCompactToL2 (potentialMeasure φ) g) =
    inner ℝ (smoothCompactToL2 (potentialMeasure φ) f)
      (smoothCompactToL2 (potentialMeasure φ) (smoothCompactDerivativeAdjoint hφ i g)) := by
  rw [inner_smoothCompactToL2, inner_smoothCompactToL2]
  exact weighted_integration_by_parts i (hφ.differentiable (by simp))
    (f.2.1.differentiable (by simp)) (g.2.1.differentiable (by simp))
    (((smooth_coordinateDerivative f.2.1 i).continuous.mul g.2.1.continuous).integrable_of_hasCompactSupport
      g.2.2.mul_left)
    ((f.2.1.continuous.mul (smooth_coordinateDerivative g.2.1 i).continuous).integrable_of_hasCompactSupport
      f.2.2.mul_right)
    (((f.2.1.continuous.mul g.2.1.continuous).mul
      (smooth_coordinateDerivative hφ i).continuous).integrable_of_hasCompactSupport
      (f.2.2.mul_right.mul_right))
    ((f.2.1.continuous.mul g.2.1.continuous).integrable_of_hasCompactSupport f.2.2.mul_right)

/-- Weighted integration by parts holds for every element of the actual
closed Sobolev graph, by continuity of L² pairings. -/
theorem weightedSobolev_integration_by_parts {n : ℕ} {φ : CoordinateSpace n → ℝ}
    [IsFiniteMeasureOnCompacts (potentialMeasure φ)] (hφ : ContDiff ℝ ∞ φ)
    (u : weightedSobolev (potentialMeasure φ)) (i : Fin n) (g : smoothCompactCore n) :
    inner ℝ (u.1 i.succ) (smoothCompactToL2 (potentialMeasure φ) g) =
      inner ℝ (u.1 0)
        (smoothCompactToL2 (potentialMeasure φ) (smoothCompactDerivativeAdjoint hφ i g)) := by
  let μ := potentialMeasure φ
  have hclosed : IsClosed {v : SobolevJet μ |
      inner ℝ (v i.succ) (smoothCompactToL2 μ g) =
        inner ℝ (v 0) (smoothCompactToL2 μ (smoothCompactDerivativeAdjoint hφ i g))} :=
    isClosed_eq ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (n+1) => Lp ℝ 2 μ) i.succ).continuous.inner continuous_const)
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (n+1) => Lp ℝ 2 μ) 0).continuous.inner continuous_const)
  have hcore : (LinearMap.range (smoothCompactJet μ) : Set (SobolevJet μ)) ⊆
      {v | inner ℝ (v i.succ) (smoothCompactToL2 μ g) =
        inner ℝ (v 0) (smoothCompactToL2 μ (smoothCompactDerivativeAdjoint hφ i g))} := by
    rintro _ ⟨f, rfl⟩
    exact smoothCompactDerivative_adjoint hφ i f g
  exact (closure_minimal hcore hclosed) u.2

/-- Closability: a Sobolev jet whose L² function vanishes has zero gradient. -/
theorem weightedSobolev_eq_zero_of_value_eq_zero {n : ℕ} {φ : CoordinateSpace n → ℝ}
    [IsFiniteMeasureOnCompacts (potentialMeasure φ)] (hφ : ContDiff ℝ ∞ φ)
    (u : weightedSobolev (potentialMeasure φ)) (hu : weightedSobolevValue (potentialMeasure φ) u = 0) :
    u = 0 := by
  have h0 : u.1 0 = 0 := hu
  have hd (i : Fin n) : u.1 i.succ = 0 := by
    have heq : (fun v : Lp ℝ 2 (potentialMeasure φ) => inner ℝ (u.1 i.succ) v) = fun _ => 0 := by
      apply (continuous_const.inner continuous_id).ext_on
        (smoothCompactToL2_dense (potentialMeasure φ)) continuous_const
      rintro _ ⟨g, rfl⟩
      change inner ℝ (u.1 i.succ) (smoothCompactToL2 (potentialMeasure φ) g) = 0
      rw [weightedSobolev_integration_by_parts hφ u i g, h0, inner_zero_left]
    have hz := congrFun heq (u.1 i.succ)
    exact inner_self_eq_zero.mp hz
  apply Subtype.ext
  apply PiLp.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact h0
  · exact hd j

/-- The constructed weighted Sobolev space embeds injectively into the
actual L² space. Thus its weak derivatives are well defined. -/
theorem weightedSobolevValue_injective {n : ℕ} {φ : CoordinateSpace n → ℝ}
    [IsFiniteMeasureOnCompacts (potentialMeasure φ)] (hφ : ContDiff ℝ ∞ φ) :
    Function.Injective (weightedSobolevValue (potentialMeasure φ)) := by
  intro u v huv
  apply sub_eq_zero.mp
  apply weightedSobolev_eq_zero_of_value_eq_zero hφ
  rw [map_sub, huv, sub_self]

end GaussianTilt.Letwin
