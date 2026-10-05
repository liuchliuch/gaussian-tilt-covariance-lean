import GaussianTilt.NegativeSobolevHilbert

/-!
# Construction of the weighted first Sobolev space and its weak resolvent

The space is constructed as the closed graph completion of actual smooth
compactly supported functions and their coordinate gradients inside a finite
Hilbert sum of actual L² spaces. The weak resolvent is constructed by Riesz,
not postulated as an existence hypothesis.
-/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ContDiff Topology ENNReal InnerProductSpace
namespace GaussianTilt.Letwin

/-- Coordinate differentiation on the genuine smooth compact core. -/
def smoothCompactDerivative {n : ℕ} (i : Fin n) :
    smoothCompactCore n →ₗ[ℝ] smoothCompactCore n where
  toFun f := ⟨coordinateDerivative i f.1, smooth_coordinateDerivative f.2.1 i,
    f.2.2.fderiv_apply (𝕜 := ℝ) (Pi.single i 1)⟩
  map_add' f g := by
    apply Subtype.ext
    funext x
    exact coordinateDerivative_add (f.2.1.differentiable (by simp))
      (g.2.1.differentiable (by simp)) i x
  map_smul' c f := by
    apply Subtype.ext
    funext x
    change coordinateDerivative i (fun y => c * f.1 y) x = c * coordinateDerivative i f.1 x
    unfold coordinateDerivative
    rw [((f.2.1.differentiable (by simp) x).hasFDerivAt.const_mul c).fderiv]
    simp

/-- An L² value together with n L² derivative coordinates, with the Hilbert
sum norm rather than a supremum product norm. -/
abbrev SobolevJet {n : ℕ} (μ : Measure (CoordinateSpace n)) :=
  PiLp 2 (fun _ : Fin (n + 1) => Lp ℝ 2 μ)

/-- The actual value/gradient jet of a smooth compact test. -/
def smoothCompactJet {n : ℕ} (μ : Measure (CoordinateSpace n)) [IsFiniteMeasureOnCompacts μ] :
    smoothCompactCore n →ₗ[ℝ] SobolevJet μ :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n+1) => Lp ℝ 2 μ)).symm.toLinearMap.comp
    (LinearMap.pi (Fin.cases (smoothCompactToL2 μ)
      (fun i => (smoothCompactToL2 μ).comp (smoothCompactDerivative i))))

@[simp] lemma smoothCompactJet_zero {n : ℕ} (μ : Measure (CoordinateSpace n)) [IsFiniteMeasureOnCompacts μ]
    (u : smoothCompactCore n) : smoothCompactJet μ u 0 = smoothCompactToL2 μ u := rfl

@[simp] lemma smoothCompactJet_succ {n : ℕ} (μ : Measure (CoordinateSpace n)) [IsFiniteMeasureOnCompacts μ]
    (u : smoothCompactCore n) (i : Fin n) :
    smoothCompactJet μ u i.succ = smoothCompactToL2 μ (smoothCompactDerivative i u) := rfl

/-- The weighted H¹ space, as a closed subspace of the actual Hilbert jet space. -/
def weightedSobolev {n : ℕ} (μ : Measure (CoordinateSpace n)) [IsFiniteMeasureOnCompacts μ] :
    Submodule ℝ (SobolevJet μ) := (LinearMap.range (smoothCompactJet μ)).topologicalClosure

instance weightedSobolev_complete {n : ℕ} (μ : Measure (CoordinateSpace n)) [IsFiniteMeasureOnCompacts μ] :
    CompleteSpace (weightedSobolev μ) :=
  (LinearMap.range (smoothCompactJet μ)).isClosed_topologicalClosure.completeSpace_coe

/-- Evaluation of a Sobolev jet's actual L² value. -/
def weightedSobolevValue {n : ℕ} (μ : Measure (CoordinateSpace n)) [IsFiniteMeasureOnCompacts μ] :
    weightedSobolev μ →L[ℝ] Lp ℝ 2 μ :=
  (PiLp.proj 2 (fun _ : Fin (n+1) => Lp ℝ 2 μ) 0).comp (weightedSobolev μ).subtypeL

/-- The weak solution to (I-L)u=f is the Riesz representative of f acting on
the value coordinate. This is an actual constructed object. -/
def weightedWeakResolvent {n : ℕ} (μ : Measure (CoordinateSpace n)) [IsFiniteMeasureOnCompacts μ]
    (f : Lp ℝ 2 μ) : weightedSobolev μ :=
  (InnerProductSpace.toDual ℝ (weightedSobolev μ)).symm
    ((innerSL ℝ f).comp (weightedSobolevValue μ))

/-- Weak Poisson-resolvent equation, with every term in the actual L² Hilbert
space and no solution-existence assumption. -/
theorem weightedWeakResolvent_equation {n : ℕ} (μ : Measure (CoordinateSpace n)) [IsFiniteMeasureOnCompacts μ]
    (f : Lp ℝ 2 μ) (v : weightedSobolev μ) :
    inner ℝ (weightedWeakResolvent μ f) v = inner ℝ f (weightedSobolevValue μ v) := by
  exact InnerProductSpace.toDual_symm_apply

/-- The explicit value-and-gradient form of the constructed weak equation. -/
theorem weightedWeakResolvent_coordinates {n : ℕ} (μ : Measure (CoordinateSpace n)) [IsFiniteMeasureOnCompacts μ]
    (f : Lp ℝ 2 μ) (v : weightedSobolev μ) :
    inner ℝ ((weightedWeakResolvent μ f).1 0) (v.1 0) +
      ∑ i : Fin n, inner ℝ ((weightedWeakResolvent μ f).1 i.succ) (v.1 i.succ) =
        inner ℝ f (v.1 0) := by
  have h := weightedWeakResolvent_equation μ f v
  change inner ℝ (weightedWeakResolvent μ f).1 v.1 = _ at h
  rw [PiLp.inner_apply, Fin.sum_univ_succ] at h
  exact h

/-- The constructed weak resolvent is unique. -/
theorem weightedWeakResolvent_unique {n : ℕ} (μ : Measure (CoordinateSpace n)) [IsFiniteMeasureOnCompacts μ]
    (f : Lp ℝ 2 μ) (u : weightedSobolev μ)
    (hu : ∀ v, inner ℝ u v = inner ℝ f (weightedSobolevValue μ v)) :
    u = weightedWeakResolvent μ f := by
  apply ext_inner_right ℝ
  intro v
  exact (hu v).trans (weightedWeakResolvent_equation μ f v).symm

end GaussianTilt.Letwin
