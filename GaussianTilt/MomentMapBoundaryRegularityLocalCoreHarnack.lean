import GaussianTilt.MomentMapBoundaryRegularityLocalSystem

/-! # Interior Harnack propagation with no smooth boundary extension -/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

theorem exists_local_flat_core_harnack {lam Λ K : ℝ}
    (hlam : 0 < lam) (hΛ : 0 ≤ Λ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (j : Fin n) (u f : CoordinateSpace n → ℝ)
      (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ) (M : ℝ),
      0 ≤ M → LocalFlatEllipticSystem j u f A lam Λ K M →
      (∀ y ∈ flatHalfBall j, 0 ≤ u y) →
      ∀ y ∈ flatInteriorCore j, u (Pi.single j (1/4)) ≤ C*(u y+128*M) := by
  obtain ⟨H,hH,hchain⟩ := exists_interior_harnack_chain (n := n) hlam hΛ hK
  refine ⟨H^128,one_le_pow₀ hH,?_⟩
  intro j u f A M hM hs hn y hy
  let S := flatCompactInteriorStrip j
  have hS : IsCompact S := isCompact_flatCompactInteriorStrip j
  have hSU : S ⊆ flatHalfBall j := flatCompactInteriorStrip_inside j
  obtain ⟨u₀,hu₀,heu⟩ := exists_global_smooth_eq_near_compact_coordinate (isOpen_flatHalfBall j)
    hs.smooth_interior hS hSU
  obtain ⟨f₀,hf₀,hef⟩ := exists_global_smooth_eq_near_compact_coordinate (isOpen_flatHalfBall j)
    hs.forcing_smooth hS hSU
  choose B hBs hBe using fun a b => exists_global_smooth_eq_near_compact_coordinate
    (isOpen_flatHalfBall j) (hs.coefficient_smooth a b) hS hSU
  let A₀ : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ := fun z a b => B a b z
  have hAd₀ (a b : Fin n) : Differentiable ℝ (fun z => A₀ z a b) := (hBs a b).differentiable (by simp)
  have hAv (z : CoordinateSpace n) (hz : z ∈ S) : A₀ z=A z := by
    ext a b
    exact (hBe a b z hz).self_of_nhds
  have hDv (z : CoordinateSpace n) (hz : z ∈ S) (k a b : Fin n) :
      matrixCoordinateDerivative A₀ k z a b=matrixCoordinateDerivative A k z a b :=
    coordinateDerivative_congr_nhds (hBe a b z hz) k
  have huv (z : CoordinateSpace n) (hz : z ∈ S) : u₀ z=u z := (heu z hz).self_of_nhds
  have hfv (z : CoordinateSpace n) (hz : z ∈ S) : f₀ z=f z := (hef z hz).self_of_nhds
  have hstrip : flatInteriorStrip j ⊆ S := flatInteriorStrip_subset_compact j
  have hinside (z : CoordinateSpace n) (hz : z ∈ flatInteriorStrip j) : z ∈ flatHalfBall j :=
    hSU (hstrip hz)
  have hDb (z : CoordinateSpace n) (hz : z ∈ flatInteriorStrip j) (k a b : Fin n) :
      (1/64:ℝ)*|matrixCoordinateDerivative A₀ k z a b| ≤ K := by
    rw [hDv z (hstrip hz)]
    have hh := hs.coefficient_bound z (hinside z hz) k a b
    have hp := hz.2
    nlinarith [abs_nonneg (matrixCoordinateDerivative A k z a b)]
  have hforc (z : CoordinateSpace n) (hz : z ∈ flatInteriorStrip j) : (1/64:ℝ)^2*|f₀ z| ≤ M := by
    rw [hfv z (hstrip hz)]
    have hh := hs.forcing_bound z (hinside z hz)
    nlinarith [abs_nonneg (f z)]
  have hDforc (z : CoordinateSpace n) (hz : z ∈ flatInteriorStrip j) (k : Fin n) :
      (1/64:ℝ)^3*|coordinateDerivative k f₀ z| ≤ M := by
    rw [coordinateDerivative_congr_nhds (hef z (hstrip hz)) k]
    have hh := hs.forcing_derivative_bound z (hinside z hz) k
    have hp := hz.2
    nlinarith [abs_nonneg (coordinateDerivative k f z)]
  have hP₀ (z : CoordinateSpace n) (hz : z ∈ flatInteriorStrip j) : linearizedMA (A₀ z) u₀ z=f₀ z := by
    rw [hAv z (hstrip hz),hfv z (hstrip hz),linearizedMA,
      coordinateHessian_congr_nhds (heu z (hstrip hz))]
    exact hs.equation z (hinside z hz)
  have hc := flat_corkscrew_mem_core j
  have hh := hchain u₀ f₀ A₀ (flatInteriorStrip j) (1/64) M (by norm_num) hM hu₀
    (hf₀.differentiable (by simp)) hAd₀
    (fun z hz => by rw [huv z (hstrip hz)]; exact hn z (hinside z hz))
    (fun z hz => by rw [hAv z (hstrip hz)]; exact (hs.positive z (hinside z hz)).posSemidef)
    (fun z hz => by rw [hAv z (hstrip hz)]; exact hs.elliptic z (hinside z hz))
    hDb hforc hDforc hP₀ (Pi.single j (1/4)) y 128 (by norm_num)
    (by norm_num; exact flat_core_distance_le_one j hc hy) (flatInteriorCore_tube j hc hy)
  rw [huv _ (flatInteriorCore_subset_compact j hc),huv _ (flatInteriorCore_subset_compact j hy)] at hh
  exact hh

end GaussianTilt.MomentMapRegularity
