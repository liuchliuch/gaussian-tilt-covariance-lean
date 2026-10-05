import GaussianTilt.MomentMapBoundaryRegularityFlatGeometry

/-! # Uniform positivity transfer across the interior of a flat patch -/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

theorem exists_flat_core_harnack {lam Λ K : ℝ}
    (hlam : 0 < lam) (hΛ : 0 ≤ Λ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (j : Fin n) (v f : CoordinateSpace n → ℝ) (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ),
      ContDiff ℝ ∞ v → Differentiable ℝ f → (∀ i k, Differentiable ℝ (fun y => A y i k)) →
      (∀ y ∈ flatHalfBall j, 0 ≤ v y) → (∀ y ∈ flatHalfBall j, (A y).PosDef) →
      (∀ y ∈ flatHalfBall j, ∀ w : CoordinateSpace n,
        lam*‖(coordinateEquiv n).symm w‖^2 ≤ w ⬝ᵥ (A y *ᵥ w) ∧
        w ⬝ᵥ (A y *ᵥ w) ≤ Λ*‖(coordinateEquiv n).symm w‖^2) →
      (∀ y ∈ flatHalfBall j, ∀ k a b, y j*|matrixCoordinateDerivative A k y a b| ≤ K) →
      ∀ ε : ℝ, 0 ≤ ε →
      (∀ y ∈ flatHalfBall j, |f y| ≤ ε) →
      (∀ y ∈ flatHalfBall j, ∀ k, y j*|coordinateDerivative k f y| ≤ ε) →
      (∀ y ∈ flatHalfBall j, linearizedMA (A y) v y = f y) →
      ∀ y ∈ flatInteriorCore j, v (Pi.single j (1/4)) ≤ C*(v y+128*ε) := by
  obtain ⟨H,hH,hchain⟩ := exists_interior_harnack_chain (n := n) hlam hΛ hK
  refine ⟨H^128, one_le_pow₀ hH, ?_⟩
  intro j v f A hv hf hAd hn hA hEll hDA ε hε hfb hDfb hP y hy
  have hinside := flatInteriorStrip_subset j
  have hDb (z : CoordinateSpace n) (hz : z ∈ flatInteriorStrip j) (k a b : Fin n) :
      (1/64:ℝ)*|matrixCoordinateDerivative A k z a b| ≤ K := by
    have hh := hDA z (hinside hz) k a b
    have hp := hz.2
    nlinarith [abs_nonneg (matrixCoordinateDerivative A k z a b)]
  have hforc (z : CoordinateSpace n) (hz : z ∈ flatInteriorStrip j) : (1/64:ℝ)^2*|f z| ≤ ε := by
    have hh := hfb z (hinside hz)
    nlinarith [abs_nonneg (f z)]
  have hDforc (z : CoordinateSpace n) (hz : z ∈ flatInteriorStrip j) (k : Fin n) :
      (1/64:ℝ)^3*|coordinateDerivative k f z| ≤ ε := by
    have hh := hDfb z (hinside hz) k
    have hp := hz.2
    nlinarith [abs_nonneg (coordinateDerivative k f z)]
  have hc := flat_corkscrew_mem_core j
  have hh := hchain v f A (flatInteriorStrip j) (1/64) ε (by norm_num) hε hv hf hAd
    (fun z hz => hn z (hinside hz)) (fun z hz => (hA z (hinside hz)).posSemidef)
    (fun z hz => hEll z (hinside hz)) hDb hforc hDforc (fun z hz => hP z (hinside hz))
    (Pi.single j (1/4)) y 128 (by norm_num)
    (by norm_num; exact flat_core_distance_le_one j hc hy) (flatInteriorCore_tube j hc hy)
  exact hh

end GaussianTilt.MomentMapRegularity
