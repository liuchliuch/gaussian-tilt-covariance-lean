import GaussianTilt.MomentMapBoundaryRegularityScaledGradient
import GaussianTilt.MomentMapBoundaryRegularityLocalSystem

/-! # Genuine signed interior gradient estimates from local smoothness -/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

theorem exists_local_scaled_gradient_bound {lam Λ K : ℝ}
    (hlam : 0 < lam) (hΛ : 0 ≤ Λ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u f : CoordinateSpace n → ℝ) (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
        (U : Set (CoordinateSpace n)) (c : CoordinateSpace n) (r B F : ℝ),
      IsOpen U → 0 < r → 0 ≤ B → 0 ≤ F →
      ContDiffOn ℝ ∞ u U → ContDiffOn ℝ ∞ f U →
      (∀ i j, ContDiffOn ℝ ∞ (fun y => A y i j) U) →
      (∀ y, ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm c‖ ≤ 2*r → y ∈ U) →
      (∀ y, ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm c‖ < 2*r → |u y| ≤ B) →
      (∀ y, ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm c‖ < r → (A y).PosSemidef) →
      (∀ y, ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm c‖ < r → ∀ w : CoordinateSpace n,
        lam*‖(coordinateEquiv n).symm w‖^2 ≤ w ⬝ᵥ (A y *ᵥ w) ∧
        w ⬝ᵥ (A y *ᵥ w) ≤ Λ*‖(coordinateEquiv n).symm w‖^2) →
      (∀ y, ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm c‖ < r →
        ∀ k i j, r*|matrixCoordinateDerivative A k y i j| ≤ K) →
      (∀ y, ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm c‖ < r → r^2*|f y| ≤ F) →
      (∀ y, ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm c‖ < r →
        ∀ k, r^3*|coordinateDerivative k f y| ≤ F) →
      (∀ y, ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm c‖ < r → linearizedMA (A y) u y=f y) →
      ∀ i, r*|coordinateDerivative i u c| ≤ C*(B+F) := by
  obtain ⟨C,hC,hgrad⟩ := exists_scaled_interior_gradient_bound (n := n) hlam hΛ hK
  refine ⟨C,hC,?_⟩
  intro u f A U c r B F hU hr hB hF hu hf hAs hin hub hAp hEll hAb hfb hDfb hP
  let S := coordinateClosedAnnulus c 0 (2*r)
  have hS : IsCompact S := isCompact_coordinateClosedAnnulus c 0 (2*r)
  have hSU : S ⊆ U := fun y hy => hin y hy.2
  obtain ⟨u₀,hu₀,heu⟩ := exists_global_smooth_eq_near_compact_coordinate hU hu hS hSU
  obtain ⟨f₀,hf₀,hef⟩ := exists_global_smooth_eq_near_compact_coordinate hU hf hS hSU
  choose A' hA's hA'e using fun a b => exists_global_smooth_eq_near_compact_coordinate hU (hAs a b) hS hSU
  let A₀ : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ := fun y a b => A' a b y
  have hnear2 (y : CoordinateSpace n) (hy : ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm c‖ < 2*r) : y ∈ S :=
    ⟨norm_nonneg _,hy.le⟩
  have hnear1 (y : CoordinateSpace n) (hy : ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm c‖ < r) : y ∈ S :=
    hnear2 y (by linarith)
  have hAv (y : CoordinateSpace n) (hy : y ∈ S) : A₀ y=A y := by
    ext a b
    exact (hA'e a b y hy).self_of_nhds
  have hDv (y : CoordinateSpace n) (hy : y ∈ S) (k a b : Fin n) :
      matrixCoordinateDerivative A₀ k y a b=matrixCoordinateDerivative A k y a b :=
    coordinateDerivative_congr_nhds (hA'e a b y hy) k
  have hPP (y : CoordinateSpace n) (hy : ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm c‖ < r) :
      linearizedMA (A₀ y) u₀ y=f₀ y := by
    rw [hAv y (hnear1 y hy),(hef y (hnear1 y hy)).self_of_nhds,linearizedMA,
      coordinateHessian_congr_nhds (heu y (hnear1 y hy))]
    exact hP y hy
  have hh := hgrad u₀ f₀ A₀ c r B F hr hB hF hu₀ (hf₀.differentiable (by simp))
    (fun a b => (hA's a b).differentiable (by simp))
    (fun y hy => by rw [(heu y (hnear2 y hy)).self_of_nhds]; exact hub y hy)
    (fun y hy => by rw [hAv y (hnear1 y hy)]; exact hAp y hy)
    (fun y hy => by rw [hAv y (hnear1 y hy)]; exact hEll y hy)
    (fun y hy k a b => by rw [hDv y (hnear1 y hy)]; exact hAb y hy k a b)
    (fun y hy => by rw [(hef y (hnear1 y hy)).self_of_nhds]; exact hfb y hy)
    (fun y hy k => by rw [coordinateDerivative_congr_nhds (hef y (hnear1 y hy)) k]; exact hDfb y hy k) hPP
  intro i
  have hc : c ∈ S := ⟨by simp,by simpa using (show 0 ≤ 2*r by positivity)⟩
  simpa only [coordinateDerivative_congr_nhds (heu c hc) i] using hh i

end GaussianTilt.MomentMapRegularity
