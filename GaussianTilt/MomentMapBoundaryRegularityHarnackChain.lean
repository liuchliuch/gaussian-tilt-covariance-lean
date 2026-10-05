import GaussianTilt.MomentMapBoundaryRegularityRescaling

/-! # Genuine finite Harnack propagation along an interior segment -/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

/-- Uniform Harnack is propagated by an explicitly constructed finite
chain of balls. The path and every local PDE application are supplied here. -/
theorem exists_interior_harnack_chain {lam Λ K : ℝ}
    (hlam : 0 < lam) (hΛ : 0 ≤ Λ) (hK : 0 ≤ K) :
    ∃ H : ℝ, 1 ≤ H ∧
      ∀ (v f : CoordinateSpace n → ℝ) (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
        (U : Set (CoordinateSpace n)) (r F : ℝ),
      0 < r → 0 ≤ F → ContDiff ℝ ∞ v → Differentiable ℝ f →
      (∀ i j, Differentiable ℝ (fun y => A y i j)) →
      (∀ y ∈ U, 0 ≤ v y) → (∀ y ∈ U, (A y).PosSemidef) →
      (∀ y ∈ U, ∀ w : CoordinateSpace n,
        lam*‖(coordinateEquiv n).symm w‖^2 ≤ w ⬝ᵥ (A y *ᵥ w) ∧
        w ⬝ᵥ (A y *ᵥ w) ≤ Λ*‖(coordinateEquiv n).symm w‖^2) →
      (∀ y ∈ U, ∀ k i j, r*|matrixCoordinateDerivative A k y i j| ≤ K) →
      (∀ y ∈ U, r^2*|f y| ≤ F) →
      (∀ y ∈ U, ∀ k, r^3*|coordinateDerivative k f y| ≤ F) →
      (∀ y ∈ U, linearizedMA (A y) v y = f y) →
      ∀ (x y : CoordinateSpace n) (N : ℕ), 0 < N →
      ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm x‖ ≤ (N:ℝ)*r/2 →
      (∀ z ∈ segment ℝ x y, ∀ w, ‖(coordinateEquiv n).symm w-(coordinateEquiv n).symm z‖ < 2*r → w ∈ U) →
      v x ≤ H^N * (v y+(N:ℝ)*F) := by
  obtain ⟨H₀,hH₀,hlocal⟩ := exists_scaled_interior_harnack (n := n) hlam hΛ hK
  let H := max H₀ 1
  have hH : 1 ≤ H := le_max_right _ _
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  refine ⟨H,hH,?_⟩
  intro v f A U r F hr hF hv hf hAd hn hA hEll hDA hfb hDfb hP x y N hN hdist htube
  have hNR : 0 < (N:ℝ) := Nat.cast_pos.mpr hN
  let z : ℕ → CoordinateSpace n := fun k => x + ((k:ℝ)/(N:ℝ)) • (y-x)
  have hz (k : ℕ) (hk : k ≤ N) : z k ∈ segment ℝ x y := by
    have hkr : (k:ℝ) ≤ N := Nat.cast_le.mpr hk
    have ht0 : 0 ≤ (k:ℝ)/(N:ℝ) := div_nonneg (Nat.cast_nonneg _) hNR.le
    have ht1 : (k:ℝ)/(N:ℝ) ≤ 1 := (div_le_one hNR).mpr hkr
    refine ⟨1-(k:ℝ)/(N:ℝ), (k:ℝ)/(N:ℝ), by linarith, ht0, by ring, ?_⟩
    dsimp [z]
    module
  have hzU (k : ℕ) (hk : k ≤ N) : z k ∈ U :=
    htube (z k) (hz k hk) (z k) (by simpa using (show 0 < 2*r by positivity))
  have hstepdist (k : ℕ) :
      ‖(coordinateEquiv n).symm (z (k+1))-(coordinateEquiv n).symm (z k)‖ ≤ r/2 := by
    have he : z (k+1)-z k = (1/(N:ℝ)) • (y-x) := by
      dsimp [z]
      rw [Nat.cast_add, Nat.cast_one, add_div]
      module
    rw [← map_sub, he, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hNR), map_sub]
    have hh : ‖(coordinateEquiv n).symm y-(coordinateEquiv n).symm x‖ / (N:ℝ) ≤ r/2 :=
      (div_le_iff₀ hNR).mpr (by nlinarith [hdist])
    convert hh using 1 <;> ring
  have hstep (k : ℕ) (hk : k < N) : v (z k) ≤ H*(v (z (k+1))+F) := by
    have hzseg := hz k hk.le
    have hu (w : CoordinateSpace n) (hw : ‖(coordinateEquiv n).symm w-(coordinateEquiv n).symm (z k)‖ < r) : w ∈ U :=
      htube (z k) hzseg w (by linarith)
    have hh := hlocal v f A (z k) r hr hv hf hAd
      (fun w hw => hn w (htube (z k) hzseg w hw))
      (fun w hw => hA w (hu w hw)) (fun w hw => hEll w (hu w hw))
      (fun w hw => hDA w (hu w hw)) F hF
      (fun w hw => hfb w (hu w hw)) (fun w hw => hDfb w (hu w hw))
      (fun w hw => hP w (hu w hw)) (z k) (z (k+1))
      (by simpa using (show 0 ≤ r/2 by positivity)) (hstepdist k)
    exact hh.trans (mul_le_mul_of_nonneg_right (le_max_left H₀ 1)
      (add_nonneg (hn _ (hzU (k+1) (Nat.succ_le_iff.mpr hk))) hF))
  have hind (k : ℕ) (hk : k ≤ N) : v (z 0) ≤ H^k*(v (z k)+(k:ℝ)*F) := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hkN : k < N := Nat.lt_of_succ_le hk
      have hi := ih hkN.le
      have hs := hstep k hkN
      have hm := mul_le_mul_of_nonneg_left hs (pow_nonneg hHpos.le k)
      have hFscale : (k:ℝ)*F ≤ H*((k:ℝ)*F) := le_mul_of_one_le_left (by positivity) hH
      have hmore := mul_le_mul_of_nonneg_left hFscale (pow_nonneg hHpos.le k)
      rw [pow_succ, Nat.cast_add, Nat.cast_one]
      nlinarith
  have h0 : z 0 = x := by simp [z]
  have hlast : z N = y := by simp [z, hNR.ne']
  simpa only [h0, hlast] using hind N le_rfl

end GaussianTilt.MomentMapRegularity
