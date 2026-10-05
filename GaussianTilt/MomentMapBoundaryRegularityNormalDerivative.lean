import GaussianTilt.MomentMapBoundaryRegularityQuotientHolder

/-!
# Genuine Hölder control of the actual flat-boundary normal derivative

One-sided derivative limits put boundary derivatives into the proved
quotient intervals. No boundary derivative oscillation assumption is used.
-/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

lemma boundary_normal_derivative_mem_quotient_interval {u : CoordinateSpace n → ℝ}
    (hu : Differentiable ℝ u) {j : Fin n} {B r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hb : ∀ x, ‖(coordinateEquiv n).symm x‖ ≤ 1 → 0 ≤ x j → |u x| ≤ B*x j)
    {y : CoordinateSpace n} (hy : ‖(coordinateEquiv n).symm y‖ < r) (hyj : y j=0) :
    sInf (boundaryQuotientValues u j r) ≤ coordinateDerivative j u y ∧
      coordinateDerivative j u y ≤ sSup (boundaryQuotientValues u j r) := by
  let e : CoordinateSpace n := Pi.single j 1
  have hu0 : u y=0 := by
    have hh := hb y (hy.le.trans hr1) (by rw [hyj])
    rw [hyj,mul_zero] at hh
    exact abs_eq_zero.mp (le_antisymm hh (abs_nonneg _))
  have hl : HasDerivAt (fun t : ℝ => y+t • e) e 0 := by
    simpa only [id_eq,one_smul] using ((hasDerivAt_id (0:ℝ)).smul_const e).const_add y
  have hd : HasDerivAt (fun t : ℝ => u (y+t • e)) (coordinateDerivative j u y) 0 := by
    have hf : HasFDerivAt u (fderiv ℝ u y) (y+(0:ℝ) • e) := by simpa using (hu y).hasFDerivAt
    have hh := hf.comp_hasDerivAt (0:ℝ) hl
    simpa only [Function.comp_def,coordinateDerivative,e] using hh
  have hlim : Tendsto (fun t : ℝ => u (y+t • e)/t) (𝓝[>] 0) (𝓝 (coordinateDerivative j u y)) := by
    simpa [hu0,div_eq_mul_inv,mul_comm] using hd.tendsto_slope_zero_right
  have hnorm : ∀ᶠ t : ℝ in 𝓝 0, ‖(coordinateEquiv n).symm (y+t • e)‖ < r := by
    have hc : ContinuousAt (fun t : ℝ => ‖(coordinateEquiv n).symm (y+t • e)‖) 0 := by fun_prop
    exact hc.eventually (eventually_lt_nhds (by simpa using hy))
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

lemma boundary_normal_derivative_difference_le_oscillation {u : CoordinateSpace n → ℝ}
    (hu : Differentiable ℝ u) {j : Fin n} {B r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hb : ∀ x, ‖(coordinateEquiv n).symm x‖ ≤ 1 → 0 ≤ x j → |u x| ≤ B*x j)
    {y : CoordinateSpace n} (hy : ‖(coordinateEquiv n).symm y‖ < r) (hyj : y j=0) :
    |coordinateDerivative j u y-coordinateDerivative j u 0| ≤ boundaryQuotientOscillation u j r := by
  have h0 := boundary_normal_derivative_mem_quotient_interval hu hr hr1 hb (y := 0)
    (by simpa using hr) (by simp)
  have hyb := boundary_normal_derivative_mem_quotient_interval hu hr hr1 hb hy hyj
  unfold boundaryQuotientOscillation
  exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- The actual normal derivative has a universal Hölder modulus on the
flat boundary from uniform ellipticity, scale-weighted coefficient/source
derivatives, and the lower-order boundary Lipschitz bound. -/
theorem exists_flat_boundary_normal_derivative_holder [NeZero n] {lam Λ K : ℝ}
    (hlam : 0 < lam) (hΛ : 0 ≤ Λ) (hK : 0 ≤ K) :
    ∃ α ε₀ : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 < ε₀ ∧
      ∀ (j : Fin n) (u f : CoordinateSpace n → ℝ) (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ)
        (M B : ℝ),
      0 ≤ M → 0 ≤ B → FlatEllipticSystem j u f A lam Λ K M →
      (∀ x, ‖(coordinateEquiv n).symm x‖ ≤ 1 → 0 ≤ x j → |u x| ≤ B*x j) →
      ∀ y, ‖(coordinateEquiv n).symm y‖ ≤ 1/2 → y j=0 →
        |coordinateDerivative j u y-coordinateDerivative j u 0| ≤
          16*(2*B+M/ε₀)*‖(coordinateEquiv n).symm y‖^α := by
  obtain ⟨α,ε₀,hα,hα1,hε,hholder⟩ := exists_flat_boundary_quotient_holder (n := n) hlam hΛ hK
  refine ⟨α,ε₀,hα,hα1,hε,?_⟩
  intro j u f A M B hM hB hs hb y hy hyj
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
    have hd := boundary_normal_derivative_difference_le_oscillation (hs.smooth.differentiable (by simp)) hr hr1 hb hyd hyj
    have hh := hholder j u f A M B hM hB hs hb r ⟨hr,hr1⟩
    have htwo : (2:ℝ)^α ≤ 2 := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hα1
      simpa only [Real.rpow_one] using h
    have hcoef : 0 ≤ 2*B+M/ε₀ := by positivity
    apply hd.trans (hh.trans ?_)
    dsimp only [r]
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (norm_nonneg _)]
    have hh2 := mul_le_mul_of_nonneg_left htwo (show 0 ≤ 8*(2*B+M/ε₀)*‖(coordinateEquiv n).symm y‖^α by positivity)
    nlinarith

end GaussianTilt.MomentMapRegularity
