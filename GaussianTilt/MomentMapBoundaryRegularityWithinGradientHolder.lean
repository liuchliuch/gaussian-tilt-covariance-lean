import GaussianTilt.MomentMapBoundaryRegularityLocalGradientHolder

/-!
# Genuine up-to-boundary Hölder approach of intrinsic gradients

Interior residual estimates pass to the actual continuous within-domain
jet. No ambient smooth extension or boundary derivative modulus is used.
-/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

lemma within_gradient_coordinate_eq {u : CoordinateSpace n → ℝ} {j : Fin n}
    {x : CoordinateSpace n} (hx : x ∈ flatHalfBall j)
    {D : CoordinateSpace n →L[ℝ] ℝ} (hD : HasFDerivWithinAt u D (flatClosedHalfBall j) x)
    (i : Fin n) : coordinateDerivative i u x=D (Pi.single i 1) := by
  have hs : flatClosedHalfBall j ∈ 𝓝 x :=
    Filter.mem_of_superset ((isOpen_flatHalfBall j).mem_nhds hx) (flatHalfBall_subset_closed j)
  unfold coordinateDerivative
  rw [(hD.hasFDerivAt hs).fderiv]

theorem exists_local_flat_gradient_holder [NeZero n] {lam Λ K : ℝ}
    (hlam : 0 < lam) (hΛ : 0 ≤ Λ) (hK : 0 ≤ K) :
    ∃ α C : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 < C ∧
      ∀ (j : Fin n) (u f : CoordinateSpace n → ℝ) (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
        (D : CoordinateSpace n → CoordinateSpace n →L[ℝ] ℝ) (M B : ℝ),
      0 ≤ M → 0 ≤ B → LocalFlatEllipticSystem j u f A lam Λ K M →
      ContinuousOn D (flatClosedHalfBall j) →
      (∀ y ∈ flatClosedHalfBall j, HasFDerivWithinAt u (D y) (flatClosedHalfBall j) y) →
      (∀ y, ‖(coordinateEquiv n).symm y‖ ≤ 1 → 0 ≤ y j → |u y| ≤ B*y j) →
      ∀ x, ‖(coordinateEquiv n).symm x‖ ≤ 1/8 → 0 ≤ x j →
      ∀ i, |D x (Pi.single i 1)-D 0 (Pi.single i 1)| ≤
        C*(B+M)*‖(coordinateEquiv n).symm x‖^α := by
  obtain ⟨α,C,hα,hα1,hC,hinterior⟩ := exists_local_flat_interior_gradient_holder (n := n) hlam hΛ hK
  refine ⟨α,C,hα,hα1,hC,?_⟩
  intro j u f A D M B hM hB hs hDc hD hb
  have h0 : (0 : CoordinateSpace n) ∈ flatClosedHalfBall j := by constructor <;> simp
  have hi (x : CoordinateSpace n) (hx : ‖(coordinateEquiv n).symm x‖ ≤ 1/4) (ht : 0 < x j) (i : Fin n) :
      |D x (Pi.single i 1)-D 0 (Pi.single j 1)*(if i=j then 1 else 0)| ≤
        C*(B+M)*‖(coordinateEquiv n).symm x‖^α := by
    have hxU : x ∈ flatHalfBall j := ⟨by linarith,ht⟩
    have hh := hinterior j u f A M B (D 0) hM hB hs (hD 0 h0) hb x hx ht i
    rw [within_gradient_coordinate_eq hxU (hD x (flatHalfBall_subset_closed j hxU)) i] at hh
    exact hh
  have hall (x : CoordinateSpace n) (hx : ‖(coordinateEquiv n).symm x‖ ≤ 1/8) (ht : 0 ≤ x j) (i : Fin n) :
      |D x (Pi.single i 1)-D 0 (Pi.single j 1)*(if i=j then 1 else 0)| ≤
        C*(B+M)*‖(coordinateEquiv n).symm x‖^α := by
    by_cases hxp : 0 < x j
    · exact hi x (by linarith) hxp i
    have hxj : x j=0 := by linarith
    let e : CoordinateSpace n := Pi.single j 1
    let γ : ℝ → CoordinateSpace n := fun t => x+t • e
    have hγ : Continuous γ := by fun_prop
    have hγ0 : γ 0=x := by simp [γ]
    have hxS : x ∈ flatClosedHalfBall j := ⟨by linarith,ht⟩
    have hnear : ∀ᶠ t : ℝ in 𝓝 0, ‖(coordinateEquiv n).symm (γ t)‖ < 1/4 :=
      (((coordinateEquiv n).symm.continuous.comp hγ).norm.continuousAt).eventually
        (eventually_lt_nhds (by change ‖(coordinateEquiv n).symm (γ 0)‖ < 1/4; rw [hγ0]; linarith))
    have hγcoord (t : ℝ) : γ t j=t := by simp [γ,e,hxj]
    have hinside : ∀ᶠ t : ℝ in 𝓝[>] 0, γ t ∈ flatClosedHalfBall j := by
      filter_upwards [nhdsWithin_le_nhds hnear,self_mem_nhdsWithin] with t ht htp
      exact ⟨by linarith,by rw [hγcoord]; exact htp.le⟩
    have hlim : Tendsto γ (𝓝[>] 0) (𝓝 x) := by
      have hh : Tendsto γ (𝓝[>] (0:ℝ)) (𝓝 (γ 0)) := (hγ.tendsto 0).mono_left nhdsWithin_le_nhds
      simpa only [hγ0] using hh
    have hlimS : Tendsto γ (𝓝[>] 0) (𝓝[flatClosedHalfBall j] x) :=
      tendsto_nhdsWithin_iff.mpr ⟨hlim,hinside⟩
    have hlimD := (hDc x hxS).tendsto.comp hlimS
    have hEval : Tendsto (fun t => D (γ t) (Pi.single i 1)) (𝓝[>] (0:ℝ))
        (𝓝 (D x (Pi.single i 1))) :=
      ((ContinuousLinearMap.apply ℝ ℝ (Pi.single i 1 : CoordinateSpace n)).continuous.tendsto (D x)).comp hlimD
    have hleft := (hEval.sub_const (D 0 (Pi.single j 1)*(if i=j then 1 else 0))).abs
    have hrightc : Continuous (fun y : CoordinateSpace n => C*(B+M)*‖(coordinateEquiv n).symm y‖^α) :=
      continuous_const.mul ((coordinateEquiv n).symm.continuous.norm.rpow_const (fun _ => Or.inr hα.le))
    have hright := (hrightc.tendsto x).comp hlim
    apply le_of_tendsto_of_tendsto hleft hright
    filter_upwards [nhdsWithin_le_nhds hnear,self_mem_nhdsWithin] with t ht htp
    exact hi (γ t) ht.le (by rw [hγcoord]; exact htp) i
  have hz (i : Fin n) : D 0 (Pi.single i 1)=D 0 (Pi.single j 1)*(if i=j then 1 else 0) := by
    have hh := hall 0 (by simp) (by simp) i
    simp only [map_zero,norm_zero,Real.zero_rpow hα.ne',mul_zero] at hh
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hh (abs_nonneg _)))
  intro x hx ht i
  rw [hz i]
  exact hall x hx ht i

end GaussianTilt.MomentMapRegularity
