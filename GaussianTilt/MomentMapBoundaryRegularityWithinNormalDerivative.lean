import GaussianTilt.MomentMapBoundaryRegularityLocalHolder
import GaussianTilt.MomentMapClassicalDirichletBoundaryWithinSlopes

/-! # Boundary Hölder estimates for genuine within-domain derivatives -/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

lemma within_boundary_normal_mem_quotient_interval {u : CoordinateSpace n → ℝ}
    {j : Fin n} {B r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hb : ∀ x, ‖(coordinateEquiv n).symm x‖ ≤ 1 → 0 ≤ x j → |u x| ≤ B*x j)
    {y : CoordinateSpace n} (hy : ‖(coordinateEquiv n).symm y‖ < r) (hyj : y j=0)
    {D : CoordinateSpace n →L[ℝ] ℝ} (hu : HasFDerivWithinAt u D (flatClosedHalfBall j) y) :
    sInf (boundaryQuotientValues u j r) ≤ D (Pi.single j 1) ∧
      D (Pi.single j 1) ≤ sSup (boundaryQuotientValues u j r) := by
  let e : CoordinateSpace n := Pi.single j 1
  have hu0 : u y=0 := by
    have hh := hb y (hy.le.trans hr1) (by rw [hyj])
    rw [hyj,mul_zero] at hh
    exact abs_eq_zero.mp (le_antisymm hh (abs_nonneg _))
  have hnorm : ∀ᶠ t : ℝ in 𝓝 0, ‖(coordinateEquiv n).symm (y+t • e)‖ < r := by
    have hc : ContinuousAt (fun t : ℝ => ‖(coordinateEquiv n).symm (y+t • e)‖) 0 := by fun_prop
    exact hc.eventually (eventually_lt_nhds (by simpa using hy))
  have hpath : ∀ᶠ t : ℝ in 𝓝[>] 0, y-t • (-e) ∈ flatClosedHalfBall j := by
    filter_upwards [nhdsWithin_le_nhds hnorm,self_mem_nhdsWithin] with t ht htp
    simp only [smul_neg,sub_neg_eq_add]
    refine ⟨ht.le.trans hr1,?_⟩
    simpa [e,hyj] using (show 0 ≤ t from htp.le)
  have hd : HasDerivWithinAt (fun t : ℝ => u (y+t • e)) (D e) (Ioi 0) 0 := by
    have hh := hasDerivWithinAt_inward_line hu hpath
    simpa only [smul_neg,sub_neg_eq_add,map_neg,neg_neg] using hh
  have hlim : Tendsto (fun t : ℝ => u (y+t • e)/t) (𝓝[>] 0) (𝓝 (D e)) := by
    have hh := (hasDerivWithinAt_iff_tendsto_slope' (show (0:ℝ) ∉ Ioi 0 by simp)).mp hd
    simpa only [slope_fun_def_field,zero_smul,add_zero,hu0,sub_zero] using hh
  have hbd := boundaryQuotientValues_bounded hr1 hb
  have hvalues : ∀ᶠ t : ℝ in 𝓝[>] 0, u (y+t • e)/t ∈ boundaryQuotientValues u j r := by
    filter_upwards [nhdsWithin_le_nhds hnorm,self_mem_nhdsWithin] with t ht htpos
    have hcoord : (y+t • e) j=t := by simp [e,hyj]
    exact ⟨y+t • e,ht.le,by rw [hcoord]; exact htpos,by rw [hcoord]⟩
  constructor
  · exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim
      (hvalues.mono (fun _ ht => csInf_le hbd.1 ht))
  · exact le_of_tendsto_of_tendsto hlim tendsto_const_nhds
      (hvalues.mono (fun _ ht => le_csSup hbd.2 ht))

/-- No ambient derivative at the boundary is needed. The actual within-domain
derivative supplied by an intrinsic jet satisfies the Hölder estimate. -/
theorem exists_local_flat_boundary_normal_holder [NeZero n] {lam Λ K : ℝ}
    (hlam : 0 < lam) (hΛ : 0 ≤ Λ) (hK : 0 ≤ K) :
    ∃ α ε₀ : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 < ε₀ ∧
      ∀ (j : Fin n) (u f : CoordinateSpace n → ℝ) (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
        (D : CoordinateSpace n → CoordinateSpace n →L[ℝ] ℝ) (M B : ℝ),
      0 ≤ M → 0 ≤ B → LocalFlatEllipticSystem j u f A lam Λ K M →
      (∀ x, ‖(coordinateEquiv n).symm x‖ ≤ 1 → 0 ≤ x j → |u x| ≤ B*x j) →
      (∀ y, ‖(coordinateEquiv n).symm y‖ ≤ 1/2 → y j=0 →
        HasFDerivWithinAt u (D y) (flatClosedHalfBall j) y) →
      ∀ y, ‖(coordinateEquiv n).symm y‖ ≤ 1/2 → y j=0 →
        |D y (Pi.single j 1)-D 0 (Pi.single j 1)| ≤
          16*(2*B+M/ε₀)*‖(coordinateEquiv n).symm y‖^α := by
  obtain ⟨α,ε₀,hα,hα1,hε,hholder⟩ := exists_local_flat_boundary_quotient_holder (n := n) hlam hΛ hK
  refine ⟨α,ε₀,hα,hα1,hε,?_⟩
  intro j u f A D M B hM hB hs hb hD y hy hyj
  by_cases hz : ‖(coordinateEquiv n).symm y‖=0
  · have he : (coordinateEquiv n).symm y=0 := norm_eq_zero.mp hz
    have hy0 : y=0 := by simpa using congrArg (coordinateEquiv n) he
    simp only [hy0,sub_self,abs_zero]
    positivity
  · have hn : 0 < ‖(coordinateEquiv n).symm y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    let r := 2*‖(coordinateEquiv n).symm y‖
    have hr : 0 < r := by dsimp only [r]; positivity
    have hr1 : r ≤ 1 := by dsimp only [r]; linarith
    have hyd : ‖(coordinateEquiv n).symm y‖ < r := by dsimp only [r]; linarith
    have h0 := within_boundary_normal_mem_quotient_interval hr hr1 hb (y := 0)
      (by simpa using hr) (by simp) (hD 0 (by simp) (by simp))
    have hyb := within_boundary_normal_mem_quotient_interval hr hr1 hb hyd hyj (hD y hy hyj)
    have hd : |D y (Pi.single j 1)-D 0 (Pi.single j 1)| ≤ boundaryQuotientOscillation u j r := by
      unfold boundaryQuotientOscillation
      exact abs_le.mpr ⟨by linarith,by linarith⟩
    have hh := hholder j u f A M B hM hB hs hb r ⟨hr,hr1⟩
    have htwo : (2:ℝ)^α ≤ 2 := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hα1
      simpa only [Real.rpow_one] using h
    apply hd.trans (hh.trans ?_)
    dsimp only [r]
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (norm_nonneg _)]
    have hh2 := mul_le_mul_of_nonneg_left htwo
      (show 0 ≤ 8*(2*B+M/ε₀)*‖(coordinateEquiv n).symm y‖^α by positivity)
    nlinarith

end GaussianTilt.MomentMapRegularity
