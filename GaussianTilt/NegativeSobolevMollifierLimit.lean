import GaussianTilt.NegativeSobolevMollifier

/-! # Strong L² convergence of actual compact approximate identities -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ContDiff Topology ENNReal Convolution Pointwise
namespace GaussianTilt.Letwin

lemma scalarConvolution_sub {n : ℕ} {ρ f g : CoordinateSpace n → ℝ}
    (hρ : Continuous ρ) (hρc : HasCompactSupport ρ)
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    scalarConvolution ρ (f-g) = scalarConvolution ρ f - scalarConvolution ρ g := by
  funext x
  have hi := hρc.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) hρ
    (hf.locallyIntegrable (by norm_num)) x
  have hj := hρc.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) hρ
    (hg.locallyIntegrable (by norm_num)) x
  change (∫ y, ρ y * (f (x-y)-g (x-y))) = _
  simp only [mul_sub]
  exact integral_sub hi hj

lemma scalarConvolution_congr_ae {n : ℕ} {ρ f g : CoordinateSpace n → ℝ}
    (hfg : f =ᵐ[volume] g) : scalarConvolution ρ f = scalarConvolution ρ g :=
  convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ) (Filter.EventuallyEq.refl _ _) hfg

lemma scalarConvolution_bound {n : ℕ} {ρ g : CoordinateSpace n → ℝ}
    (hρ : Continuous ρ) (hρc : HasCompactSupport ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρ1 : (∫ x, ρ x) = 1) (B : ℝ) (hg : ∀ x, ‖g x‖ ≤ B) (x : CoordinateSpace n) :
    ‖scalarConvolution ρ g x‖ ≤ B := by
  have hi : Integrable (fun y => ρ y * B) :=
    (hρ.integrable_of_hasCompactSupport hρc).mul_const B
  calc
    _ ≤ ∫ y, ρ y * B := by
      apply norm_integral_le_of_norm_le hi
      filter_upwards with y
      simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, norm_mul,
        Real.norm_of_nonneg (hρ0 y)]
      exact mul_le_mul_of_nonneg_left (hg (x-y)) (hρ0 y)
    _ = B := by rw [integral_mul_const, hρ1, one_mul]

/-- Core convergence by genuine pointwise approximate identity convergence
and a compactly supported integrable dominator. -/
theorem integral_mollifier_sub_sq_tendsto_core {n : ℕ}
    {ρ : ℕ → CoordinateSpace n → ℝ}
    (hρ : ∀ k, Continuous (ρ k)) (hρc : ∀ k, HasCompactSupport (ρ k))
    (hρ0 : ∀ k x, 0 ≤ ρ k x) (hρ1 : ∀ k, (∫ x, ρ k x) = 1)
    (hρsupp : ∀ k, Function.support (ρ k) ⊆ Metric.closedBall 0 1)
    (hρlim : Tendsto (fun k => Function.support (ρ k)) atTop (𝓝 0).smallSets)
    {g : CoordinateSpace n → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    Tendsto (fun k => ∫ x, (scalarConvolution (ρ k) g x - g x)^2) atTop (𝓝 0) := by
  obtain ⟨B, hB⟩ := hgc.exists_bound_of_continuous hg
  let K := tsupport g + Metric.closedBall (0 : CoordinateSpace n) 1
  have hK : IsCompact K := hgc.isCompact.add (isCompact_closedBall _ _)
  have hgK : Function.support g ⊆ K := by
    intro x hx
    exact ⟨x, subset_closure hx, 0, by simp, by simp⟩
  have hcK (k : ℕ) : Function.support (scalarConvolution (ρ k) g) ⊆ K := by
    exact (support_convolution_subset_swap (ContinuousLinearMap.lsmul ℝ ℝ)).trans
      (add_subset_add subset_closure (hρsupp k))
  have hB0 : 0 ≤ B := (norm_nonneg (g 0)).trans (hB 0)
  have hmem : MemLp g 2 volume := hg.memLp_of_hasCompactSupport hgc
  have hd : Integrable (K.indicator (fun _ : CoordinateSpace n => (2*B)^2)) := by
    rw [integrable_indicator_iff hK.measurableSet]
    exact integrableOn_const hK.measure_lt_top.ne
  have hlim (x : CoordinateSpace n) : Tendsto (fun k => scalarConvolution (ρ k) g x) atTop (𝓝 (g x)) := by
    apply convolution_tendsto_right
      (Filter.Eventually.of_forall hρ0) (Filter.Eventually.of_forall hρ1) hρlim
      (Filter.Eventually.of_forall fun _ => hg.aestronglyMeasurable)
      (hg.continuousAt.tendsto.comp tendsto_snd) tendsto_const_nhds
  have hconv := tendsto_integral_of_dominated_convergence (f := fun _ : CoordinateSpace n => (0 : ℝ))
    (K.indicator (fun _ : CoordinateSpace n => (2*B)^2))
    (fun k => (((scalarConvolution_continuous (hρ k) (hρc k) hmem).sub hg).pow 2).aestronglyMeasurable)
    hd ?_ ?_
  · simpa using hconv
  · intro k
    filter_upwards with x
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx, Real.norm_of_nonneg (sq_nonneg _)]
      have hbound := norm_sub_le (scalarConvolution (ρ k) g x) (g x)
      have hc := scalarConvolution_bound (hρ k) (hρc k) (hρ0 k) (hρ1 k) B hB x
      have hn : ‖scalarConvolution (ρ k) g x - g x‖ ≤ 2*B := by linarith [hB x]
      have hs := mul_self_le_mul_self (norm_nonneg _) hn
      simpa only [Real.norm_eq_abs, ← pow_two, sq_abs] using hs
    · have hz : scalarConvolution (ρ k) g x = 0 := Function.notMem_support.mp (fun h => hx (hcK k h))
      have hgz : g x = 0 := Function.notMem_support.mp (fun h => hx (hgK h))
      simp [Set.indicator_of_notMem hx, hz, hgz]
  · filter_upwards with x
    simpa using ((hlim x).sub_const (g x)).pow 2

lemma integral_add_add_sq_le_three {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {a b c : Ω → ℝ} (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) (hc : MemLp c 2 μ) :
    (∫ x, (a x + b x + c x)^2 ∂μ) ≤
      3 * ((∫ x, (a x)^2 ∂μ) + (∫ x, (b x)^2 ∂μ) + ∫ x, (c x)^2 ∂μ) := by
  have hp (x : Ω) : (a x + b x + c x)^2 ≤ 3*((a x)^2+(b x)^2+(c x)^2) := by
    nlinarith [sq_nonneg (a x-b x), sq_nonneg (a x-c x), sq_nonneg (b x-c x)]
  have h := integral_mono ((ha.add hb).add hc).integrable_sq
    (((ha.integrable_sq.add hb.integrable_sq).add hc.integrable_sq).const_mul 3) hp
  change (∫ x, (a x+b x+c x)^2 ∂μ) ≤ ∫ x, 3*((a x)^2+(b x)^2+(c x)^2) ∂μ at h
  rw [integral_const_mul,
    integral_add (f := fun x => (a x)^2+(b x)^2) (g := fun x => (c x)^2)
      (ha.integrable_sq.add hb.integrable_sq) hc.integrable_sq,
    integral_add ha.integrable_sq hb.integrable_sq] at h
  exact h

/-- Quantitative three-term comparison, using the proved contraction rather
than assuming uniform boundedness of the mollification operators. -/
lemma integral_mollifier_error_comparison {n : ℕ} {ρ f g : CoordinateSpace n → ℝ}
    (hρ : Continuous ρ) (hρc : HasCompactSupport ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρ1 : (∫ x, ρ x) = 1) (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    (∫ x, (scalarConvolution ρ f x - f x)^2) ≤
      3 * (2 * (∫ x, (f x-g x)^2) + ∫ x, (scalarConvolution ρ g x-g x)^2) := by
  let a := scalarConvolution ρ (f-g)
  let b := fun x => scalarConvolution ρ g x-g x
  let c := fun x => g x-f x
  have ha := scalarConvolution_memLp hρ hρc hρ0 hρ1 (hf.sub hg)
  have hb := (scalarConvolution_memLp hρ hρc hρ0 hρ1 hg).sub hg
  have hc := hg.sub hf
  have heq : (fun x => scalarConvolution ρ f x-f x) = fun x => a x+b x+c x := by
    funext x
    dsimp [a,b,c]
    rw [scalarConvolution_sub hρ hρc hf hg]
    simp only [Pi.sub_apply]
    ring
  have htri := integral_add_add_sq_le_three ha hb hc
  have hcon := integral_scalarConvolution_sq_le hρ hρc hρ0 hρ1 (hf.sub hg)
  have hcs : (∫ x, (c x)^2) = ∫ x, (f x-g x)^2 := by
    apply integral_congr_ae
    filter_upwards with x
    dsimp [c]
    ring
  change (∫ x, (a x+b x+c x)^2) ≤ 3*((∫ x, (a x)^2)+(∫ x, (b x)^2)+(∫ x, (c x)^2)) at htri
  rw [hcs] at htri
  change (∫ x, (a x)^2) ≤ ∫ x, (f x-g x)^2 at hcon
  change (∫ x, (fun y => scalarConvolution ρ f y-f y) x ^2) ≤ _
  rw [heq]
  change (∫ x, (a x+b x+c x)^2) ≤ 3*(2*(∫ x, (f x-g x)^2)+(∫ x, (b x)^2))
  linarith

/-- Actual compact mollification converges in Lebesgue L² for every L²
function. Density of compact smooth functions was proved independently, and
all uniform estimates here come from the proved convolution contraction. -/
theorem integral_mollifier_sub_sq_tendsto {n : ℕ}
    {ρ : ℕ → CoordinateSpace n → ℝ}
    (hρ : ∀ k, Continuous (ρ k)) (hρc : ∀ k, HasCompactSupport (ρ k))
    (hρ0 : ∀ k x, 0 ≤ ρ k x) (hρ1 : ∀ k, (∫ x, ρ k x) = 1)
    (hρsupp : ∀ k, Function.support (ρ k) ⊆ Metric.closedBall 0 1)
    (hρlim : Tendsto (fun k => Function.support (ρ k)) atTop (𝓝 0).smallSets)
    {f : CoordinateSpace n → ℝ} (hf : MemLp f 2 volume) :
    Tendsto (fun k => ∫ x, (scalarConvolution (ρ k) f x - f x)^2) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall fun k => ha.trans_le (integral_nonneg fun _ => sq_nonneg _)
  · intro ε hε
    have hδ : 0 < Real.sqrt (ε/24) := Real.sqrt_pos.2 (by positivity)
    obtain ⟨g, hgclose⟩ := (smoothCompactToL2_dense (volume : Measure (CoordinateSpace n))).exists_dist_lt
      (hf.toLp f) hδ
    have hgL : MemLp g.1 2 volume := smooth_compact_memLp g.2.1 g.2.2
    have hn : ‖hf.toLp f - smoothCompactToL2 volume g‖^2 = ∫ x, (f x-g.1 x)^2 := by
      exact (norm_toLp_sq_eq_integral (hf.sub hgL))
    rw [dist_eq_norm] at hgclose
    have herr : (∫ x, (f x-g.1 x)^2) < ε/24 := by
      have hs := Real.sq_sqrt (show 0 ≤ ε/24 by positivity)
      nlinarith [norm_nonneg (hf.toLp f - smoothCompactToL2 volume g)]
    have hlim := integral_mollifier_sub_sq_tendsto_core hρ hρc hρ0 hρ1 hρsupp hρlim g.2.1.continuous g.2.2
    filter_upwards [(tendsto_order.1 hlim).2 (ε/6) (by positivity)] with k hk
    have hc := integral_mollifier_error_comparison (hρ k) (hρc k) (hρ0 k) (hρ1 k) hf hgL
    linarith

end GaussianTilt.Letwin
