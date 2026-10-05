import Mathlib

/-!
# Scalar dynamical closure for the Gaussian-tilt upper bound

These are analysis lemmas used in Sections 3.3–3.5 of
*Optimal Covariance Inflation under Gaussian Tilts*. They concern actual real-valued
functions supplied as arguments. They do not define a surrogate covariance and do not
assert that a Gaussian-tilt path satisfies their hypotheses. That separate bridge needs
the moment-flow, variance, projected-moment, and spectral estimates.
-/

open Set Filter
open scoped Topology

namespace GaussianTilt.UpperDynamics

/-- A continuous trajectory that starts below a level and reaches it has a first contact.
This statement, unlike an assumed first-contact principle, is proved by compactness. -/
theorem exists_first_contact {f : ℝ → ℝ} {a b L : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) (ha : f a < L) (hb : L ≤ f b) :
    ∃ s ∈ Ioc a b, f s = L ∧ ∀ t ∈ Icc a s, f t ≤ L := by
  have hne : ({s ∈ Icc a b | f s = L} : Set ℝ).Nonempty := by
    obtain ⟨s, hs, heq⟩ := intermediate_value_Icc hab hf ⟨ha.le, hb⟩
    exact ⟨s, hs, heq⟩
  have hc : IsCompact {s ∈ Icc a b | f s = L} :=
    isCompact_Icc.of_isClosed_subset
      (hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton)
      (fun _ hx => hx.1)
  obtain ⟨s, hs, hleast⟩ := hc.exists_isLeast hne
  have has : a < s := lt_of_le_of_ne hs.1.1 (by
    intro heq
    rw [heq] at ha
    exact (ne_of_lt ha) hs.2)
  refine ⟨s, ⟨has, hs.1.2⟩, hs.2, ?_⟩
  intro t ht
  by_contra h
  have hLt : L < f t := lt_of_not_ge h
  obtain ⟨r, hr, hfr⟩ := intermediate_value_Icc ht.1
    (hf.mono (Icc_subset_Icc le_rfl (ht.2.trans hs.1.2))) ⟨ha.le, hLt.le⟩
  have hsr : s ≤ r := hleast ⟨⟨hr.1, hr.2.trans (ht.2.trans hs.1.2)⟩, hfr⟩
  have hrt : r = t := le_antisymm hr.2 (ht.2.trans hsr)
  exact (ne_of_lt hLt) (hrt ▸ hfr).symm

/-- The right-slope hypothesis needed by Grönwall; an upper Dini derivative bound
implies this hypothesis, and an ordinary right derivative supplies it as well. -/
def RightSlopeBound (f d : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ x ∈ Ico a b, ∀ r, d x < r →
    ∃ᶠ z in 𝓝[>] x, (z - x)⁻¹ * (f z - f x) < r

/-- Ordinary right-derivative estimates imply the slope interface used below. -/
theorem rightSlopeBound_of_hasDerivWithinAt {f f' d : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    (hd : ∀ x ∈ Ico a b, f' x ≤ d x) : RightSlopeBound f d a b := by
  intro x hx r hr
  exact (hf x hx).liminf_right_slope_le ((hd x hx).trans_lt hr)

/-- Lemma 3.7, as an analytic theorem about the two norm trajectories. The
hypotheses are differential bounds, not the desired stability conclusion. -/
theorem short_time_stability {u v : ℝ → ℝ} {a b α β : ℝ}
    (hab : a ≤ b) (hα : 0 < α) (hβ : 0 < β)
    (hu : ContinuousOn u (Icc a b)) (hv : ContinuousOn v (Icc a b))
    (hu0 : ∀ t ∈ Icc a b, 0 ≤ u t) (hv0 : ∀ t ∈ Icc a b, 0 ≤ v t)
    (hua : u a ≤ α) (hva : v a ≤ β)
    (hud : RightSlopeBound u (fun t => 10 * v t * u t) a b)
    (hvd : RightSlopeBound v (fun t => 10 * u t * v t) a b)
    (hαtime : 20 * α * (b - a) < Real.log 2)
    (hβtime : 20 * β * (b - a) < Real.log 2) :
    ∀ t ∈ Icc a b, u t ≤ 2 * α ∧ v t ≤ 2 * β := by
  intro t ht
  by_contra hbad
  let f : ℝ → ℝ := fun s => max (u s / α) (v s / β)
  have hf : ContinuousOn f (Icc a t) :=
    ((hu.div_const α).sup (hv.div_const β)).mono (Icc_subset_Icc le_rfl ht.2)
  have hfa : f a < 2 := by
    dsimp [f]
    apply max_lt
    · exact (div_lt_iff₀ hα).2 (by linarith)
    · exact (div_lt_iff₀ hβ).2 (by linarith)
  have hft : 2 ≤ f t := by
    by_contra hn
    have hf2 : f t < 2 := lt_of_not_ge hn
    have h1 := (max_lt_iff.mp hf2).1
    have h2 := (max_lt_iff.mp hf2).2
    exact hbad ⟨((div_lt_iff₀ hα).mp h1).le, ((div_lt_iff₀ hβ).mp h2).le⟩
  obtain ⟨s, hs, hfs, hprior⟩ := exists_first_contact ht.1 hf hfa hft
  have hsb : s ≤ b := hs.2.trans ht.2
  have hprioru : ∀ x ∈ Icc a s, u x ≤ 2 * α := by
    intro x hx
    exact (div_le_iff₀ hα).mp ((le_max_left _ _).trans (hprior x hx))
  have hpriorv : ∀ x ∈ Icc a s, v x ≤ 2 * β := by
    intro x hx
    exact (div_le_iff₀ hβ).mp ((le_max_right _ _).trans (hprior x hx))
  have hus : u s ≤ α * Real.exp (20 * β * (s - a)) := by
    have hg := le_gronwallBound_of_liminf_deriv_right_le
      (hu.mono (Icc_subset_Icc le_rfl hsb))
      (fun x hx => hud x ⟨hx.1, hx.2.trans_le hsb⟩) hua
      (K := 20 * β) (ε := 0) (fun x hx => by
        have hp := hpriorv x (Ico_subset_Icc_self hx)
        have hn := hu0 x ⟨hx.1, hx.2.le.trans hsb⟩
        nlinarith)
      s ⟨hs.1.le, le_rfl⟩
    simpa only [gronwallBound_ε0] using hg
  have hvs : v s ≤ β * Real.exp (20 * α * (s - a)) := by
    have hg := le_gronwallBound_of_liminf_deriv_right_le
      (hv.mono (Icc_subset_Icc le_rfl hsb))
      (fun x hx => hvd x ⟨hx.1, hx.2.trans_le hsb⟩) hva
      (K := 20 * α) (ε := 0) (fun x hx => by
        have hp := hprioru x (Ico_subset_Icc_self hx)
        have hn := hv0 x ⟨hx.1, hx.2.le.trans hsb⟩
        nlinarith)
      s ⟨hs.1.le, le_rfl⟩
    simpa only [gronwallBound_ε0] using hg
  have hexpu : Real.exp (20 * β * (s - a)) < 2 := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    apply Real.exp_lt_exp.mpr
    exact (mul_le_mul_of_nonneg_left (sub_le_sub_right hsb a) (by positivity)).trans_lt hβtime
  have hexpv : Real.exp (20 * α * (s - a)) < 2 := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    apply Real.exp_lt_exp.mpr
    exact (mul_le_mul_of_nonneg_left (sub_le_sub_right hsb a) (by positivity)).trans_lt hαtime
  have hmax : f s < 2 := by
    apply max_lt
    · apply (div_lt_iff₀ hα).2
      nlinarith [mul_lt_mul_of_pos_left hexpu hα]
    · apply (div_lt_iff₀ hβ).2
      nlinarith [mul_lt_mul_of_pos_left hexpv hβ]
  exact (ne_of_lt hmax) hfs

/-- The spectral Hilbert–Schmidt profile simplifies when q⁴≤n. -/
theorem spectral_hs_simplification {S C n q : ℝ} (hC : 0 ≤ C) (hn : 0 ≤ n)
    (hq : q ^ 4 ≤ n) (hS : S ≤ C * Real.sqrt (n + q ^ 4)) :
    S ≤ 2 * C * Real.sqrt n := by
  have hs0 := Real.sqrt_nonneg (n + q ^ 4)
  have hn0 := Real.sqrt_nonneg n
  have hsq := Real.sq_sqrt (show 0 ≤ n + q ^ 4 by positivity)
  have hsqn := Real.sq_sqrt hn
  have hroot : Real.sqrt (n + q ^ 4) ≤ 2 * Real.sqrt n := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hroot hC
  nlinarith

/-- A simultaneous explicit choice of all propagation and entropy constants. -/
theorem choose_propagation_constants {C₀ B : ℝ} (hC : 0 < C₀) :
    ∃ ε Csp κ : ℝ, 0 < ε ∧ 2 ≤ Csp ∧ B ≤ Csp ∧
      20 * C₀ * ε < Real.log 2 ∧ 40 * C₀ < Csp * Real.log 2 ∧
      5 < κ ∧ 5 * (4 * C₀) ^ 2 < κ := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let ε := Real.log 2 / (40 * C₀)
  let Csp := 2 + max 0 B + 80 * C₀ / Real.log 2
  let κ := 6 + 6 * (4 * C₀) ^ 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hr : 0 < 80 * C₀ / Real.log 2 := by positivity
  have hCsp2 : 2 ≤ Csp := by dsimp [Csp]; linarith [le_max_left (0 : ℝ) B]
  have hCspB : B ≤ Csp := by dsimp [Csp]; linarith [le_max_right (0 : ℝ) B]
  have heq : 20 * C₀ * ε = Real.log 2 / 2 := by
    dsimp [ε]
    field_simp
    <;> ring
  have hspEq : Csp * Real.log 2 = (2 + max 0 B) * Real.log 2 + 80 * C₀ := by
    dsimp [Csp]
    field_simp
  refine ⟨ε, Csp, κ, hε, hCsp2, hCspB, ?_, ?_, ?_, ?_⟩
  · rw [heq]
    linarith
  · rw [hspEq]
    have := mul_nonneg (show 0 ≤ 2 + max 0 B by positivity) hlog.le
    linarith
  · dsimp [κ]
    nlinarith [sq_nonneg (4 * C₀)]
  · dsimp [κ]
    nlinarith [sq_nonneg (4 * C₀)]

/-- The scalar endpoint propagation step in Lemma 3.8, with its constants
and earlier-time spectral estimates exposed. -/
theorem endpoint_estimate {u v : ℝ → ℝ} {T q n C₀ Csp ε : ℝ}
    (hT : 0 < T) (hq : 1 < q) (hn : 0 < n) (hC : 0 < C₀)
    (hCsp : 0 < Csp)
    (hε : 20 * C₀ * ε < Real.log 2)
    (hsp : 40 * C₀ < Csp * Real.log 2)
    (hTq : T * q ≤ ε) (hqsp : Csp * (T * Real.sqrt n) ≤ q)
    (hu : ContinuousOn u (Icc (T * (1 - 1 / q)) T))
    (hv : ContinuousOn v (Icc (T * (1 - 1 / q)) T))
    (hu0 : ∀ t ∈ Icc (T * (1 - 1 / q)) T, 0 ≤ u t)
    (hv0 : ∀ t ∈ Icc (T * (1 - 1 / q)) T, 0 ≤ v t)
    (hua : u (T * (1 - 1 / q)) ≤ C₀ * q ^ 2)
    (hva : v (T * (1 - 1 / q)) ≤ 2 * C₀ * Real.sqrt n)
    (hud : RightSlopeBound u (fun t => 10 * v t * u t) (T * (1 - 1 / q)) T)
    (hvd : RightSlopeBound v (fun t => 10 * u t * v t) (T * (1 - 1 / q)) T) :
    u T ≤ (4 * C₀) * q ^ 2 ∧ v T ≤ (4 * C₀) * Real.sqrt n := by
  have hq0 : 0 < q := by linarith
  have hlen : T - T * (1 - 1 / q) = T / q := by ring
  have hqne : q ≠ 0 := ne_of_gt hq0
  have hAB : T * (1 - 1 / q) ≤ T := by
    have : 0 < T / q := div_pos hT hq0
    linarith [hlen]
  have ha : 0 < C₀ * q ^ 2 := mul_pos hC (sq_pos_of_pos hq0)
  have hb : 0 < 2 * C₀ * Real.sqrt n := by positivity
  have hsmallA : 20 * (C₀ * q ^ 2) * (T - T * (1 - 1 / q)) < Real.log 2 := by
    rw [hlen]
    have heq : 20 * (C₀ * q ^ 2) * (T / q) = 20 * C₀ * (T * q) := by
      field_simp
      <;> ring
    rw [heq]
    exact (mul_le_mul_of_nonneg_left hTq (by positivity)).trans_lt hε
  have hsmallB : 20 * (2 * C₀ * Real.sqrt n) * (T - T * (1 - 1 / q)) < Real.log 2 := by
    rw [hlen]
    have heq : 20 * (2 * C₀ * Real.sqrt n) * (T / q) =
        40 * C₀ * (T * Real.sqrt n) / q := by ring
    rw [heq, div_lt_iff₀ hq0]
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hbound := mul_le_mul_of_nonneg_left hqsp hlog.le
    have hstrict := mul_lt_mul_of_pos_right hsp (mul_pos hT (Real.sqrt_pos.2 hn))
    nlinarith
  obtain ⟨huT, hvT⟩ := short_time_stability hAB ha hb hu hv hu0 hv0 hua hva hud hvd
    hsmallA hsmallB T ⟨hAB, le_rfl⟩
  constructor
  · nlinarith [sq_nonneg q]
  · nlinarith

/-- First-contact entropy closure (Lemma 3.9). The endpoint estimate only needs
to be supplied at a putative contact; the entropy bound itself is proved here. -/
theorem entropy_barrier_of_eventual_initial_bound {H V S : ℝ → ℝ} {b n C κ : ℝ}
    (hn : 0 < n) (hC : 0 ≤ C) (hκ : 5 * C ^ 2 < κ)
    (hH : ContinuousOn H (Icc 0 b)) (hH0 : H 0 = 0)
    (hnear : ∀ᶠ t in 𝓝[>] (0 : ℝ), H t / (n * t ^ 2) < κ)
    (hderiv : ∀ t ∈ Ioo 0 b, HasDerivAt H (t * V t) t)
    (hvar : ∀ t ∈ Ioo 0 b, V t ≤ 10 * S t ^ 2)
    (hS : ∀ t ∈ Ioo 0 b, 0 ≤ S t)
    (hcontact : ∀ t ∈ Ioo 0 b, H t = κ * n * t ^ 2 → S t ≤ C * Real.sqrt n) :
    ∀ t ∈ Icc 0 b, H t ≤ κ * n * t ^ 2 := by
  obtain ⟨δ, hδ, hδbound⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hnear
  change 0 < δ at hδ
  intro t ht
  rcases eq_or_lt_of_le ht.1 with rfl | ht0
  · simp [hH0]
  let a := min t (δ / 2)
  have ha0 : 0 < a := lt_min ht0 (by linarith)
  have hat : a ≤ t := min_le_left _ _
  have haδ : a < δ := (min_le_right _ _).trans_lt (by linarith)
  have hinit : H a ≤ κ * n * a ^ 2 := by
    have hh := hδbound ⟨ha0, haδ⟩
    have hd : 0 < n * a ^ 2 := mul_pos hn (sq_pos_of_pos ha0)
    have := (div_lt_iff₀ hd).mp hh
    nlinarith
  apply image_le_of_deriv_right_lt_deriv_boundary
    (hH.mono (Icc_subset_Icc ha0.le ht.2))
    (f' := fun x => x * V x)
    (fun x hx => (hderiv x ⟨ha0.trans_le hx.1, hx.2.trans_le ht.2⟩).hasDerivWithinAt)
    hinit
    (B' := fun x => 2 * κ * n * x)
  · intro x
    convert ((hasDerivAt_id x).pow 2).const_mul (κ * n) using 1 <;> simp only [id_eq] <;> ring
  · intro x hx hHx
    have hxb : x ∈ Ioo 0 b := ⟨ha0.trans_le hx.1, hx.2.trans_le ht.2⟩
    have hSx := hcontact x hxb hHx
    have hsq : S x ^ 2 ≤ C ^ 2 * n := by
      have hh := mul_self_le_mul_self (hS x hxb) hSx
      nlinarith [Real.sq_sqrt hn.le]
    have hv := hvar x hxb
    have hpos : 0 < n * x := mul_pos hn hxb.1
    nlinarith [mul_le_mul_of_nonneg_left hv hxb.1.le,
      mul_le_mul_of_nonneg_left hsq hxb.1.le,
      mul_lt_mul_of_pos_right hκ hpos]
  · exact ⟨hat, le_rfl⟩

/-- A local entropy envelope follows directly from continuity of radial variance,
its isotropic initial bound, and the entropy derivative. No limit or initial
entropy-envelope assumption is used in this theorem. -/
theorem initial_entropy_bound {H V : ℝ → ℝ} {b n : ℝ}
    (hb : 0 < b) (hn : 0 < n)
    (hH : ContinuousOn H (Icc 0 b)) (hH0 : H 0 = 0)
    (hV : ContinuousWithinAt V (Ici 0) 0) (hV0 : V 0 ≤ 8 * n)
    (hderiv : ∀ t ∈ Ico 0 b, HasDerivWithinAt H (t * V t) (Ici t) t) :
    ∃ δ > 0, δ ≤ b ∧ ∀ t ∈ Icc 0 δ, H t ≤ 5 * n * t ^ 2 := by
  have hVstrict : V 0 < 10 * n := by linarith
  have hnear : ∀ᶠ t in 𝓝[>] (0 : ℝ), V t < 10 * n :=
    (hV.mono Ioi_subset_Ici_self).eventually (gt_mem_nhds hVstrict)
  obtain ⟨d, hd, hdbound⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hnear
  change 0 < d at hd
  let δ := min (b / 2) (d / 2)
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  have hδb : δ < b := (min_le_left _ _).trans_lt (by linarith)
  have hδd : δ < d := (min_le_right _ _).trans_lt (by linarith)
  refine ⟨δ, hδ, hδb.le, ?_⟩
  intro t ht
  apply image_le_of_deriv_right_le_deriv_boundary
    (hH.mono (Icc_subset_Icc le_rfl (ht.2.trans hδb.le)))
    (fun x hx => hderiv x ⟨hx.1, hx.2.trans_le (ht.2.trans hδb.le)⟩)
    (B := fun x => 5 * n * x ^ 2) (B' := fun x => 10 * n * x)
  · simp [hH0]
  · exact (continuous_const.mul (continuous_id.pow 2)).continuousOn
  · intro x hx
    convert (((hasDerivAt_id x).pow 2).const_mul (5 * n)).hasDerivWithinAt using 1 <;>
      simp only [id_eq] <;> ring
  · intro x hx
    rcases eq_or_lt_of_le hx.1 with rfl | hx0
    · simp
    have hxV : V x < 10 * n := hdbound ⟨hx0, (hx.2.trans_le ht.2).trans hδd⟩
    nlinarith [mul_le_mul_of_nonneg_left hxV.le hx0.le]
  · exact ⟨ht.1, le_rfl⟩

/-- Entropy closure using exactly the initial radial-variance estimate in the paper.
The local initial envelope is derived, then propagated by the contact argument. -/
theorem entropy_barrier {H V S : ℝ → ℝ} {b n C κ : ℝ}
    (hb : 0 < b) (hn : 0 < n) (hC : 0 ≤ C)
    (hκ : 5 * C ^ 2 < κ) (hκ5 : 5 < κ)
    (hH : ContinuousOn H (Icc 0 b)) (hH0 : H 0 = 0)
    (hV : ContinuousWithinAt V (Ici 0) 0) (hV0 : V 0 ≤ 8 * n)
    (hderiv : ∀ t ∈ Ico 0 b, HasDerivAt H (t * V t) t)
    (hvar : ∀ t ∈ Ioo 0 b, V t ≤ 10 * S t ^ 2)
    (hS : ∀ t ∈ Ioo 0 b, 0 ≤ S t)
    (hcontact : ∀ t ∈ Ioo 0 b, H t = κ * n * t ^ 2 → S t ≤ C * Real.sqrt n) :
    ∀ t ∈ Icc 0 b, H t ≤ κ * n * t ^ 2 := by
  obtain ⟨δ, hδ, hδb, hδbound⟩ := initial_entropy_bound hb hn hH hH0 hV hV0
    (fun t ht => (hderiv t ht).hasDerivWithinAt)
  have hnear : ∀ᶠ t in 𝓝[>] (0 : ℝ), H t / (n * t ^ 2) < κ := by
    apply mem_nhdsGT_iff_exists_Ioo_subset.mpr
    refine ⟨δ, hδ, ?_⟩
    intro t ht
    have he := hδbound t ⟨ht.1.le, ht.2.le⟩
    have hd : 0 < n * t ^ 2 := mul_pos hn (sq_pos_of_pos ht.1)
    apply (div_lt_iff₀ hd).2
    nlinarith [mul_lt_mul_of_pos_right hκ5 hd]
  exact entropy_barrier_of_eventual_initial_bound hn hC hκ hH hH0 hnear
    (fun t ht => hderiv t ⟨ht.1.le, ht.2⟩) hvar hS hcontact

/-- Uniform admissibility of all comparison parameters below A(1+n t²).
This proves, rather than assumes, the large-dimension smallness argument used
both at entropy contact and in Proposition 3.10. -/
theorem eventually_admissible_parameters {A c ε : ℝ}
    (hA : 0 < A) (hc : 0 < c) (hε : 0 < ε) (hcA : A * c ^ 2 < 1) :
    ∀ᶠ n : ℝ in atTop, ∀ T q : ℝ,
      0 ≤ T → T ≤ c * n ^ (-(3 / 8 : ℝ)) →
      0 ≤ q → q ≤ A * (1 + n * T ^ 2) → q ^ 4 ≤ n ∧ T * q ≤ ε := by
  have hlim₁ : Tendsto (fun n : ℝ => A * (n ^ (-(1 / 4 : ℝ)) + c ^ 2))
      atTop (𝓝 (A * c ^ 2)) := by
    convert ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).add_const (c ^ 2)).const_mul A using 1 <;> simp
  have hlim₂ : Tendsto (fun n : ℝ => A * (c * n ^ (-(3 / 8 : ℝ)) +
        c ^ 3 * n ^ (-(1 / 8 : ℝ)))) atTop (𝓝 0) := by
    convert (((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 8)).const_mul c).add
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 8)).const_mul (c ^ 3))).const_mul A using 1 <;> simp
  have he₁ := hlim₁.eventually (gt_mem_nhds hcA)
  have he₂ := hlim₂.eventually (gt_mem_nhds hε)
  filter_upwards [he₁, he₂, eventually_gt_atTop (0 : ℝ)] with n hn₁ hn₂ hn0
  intro T q hT hTmax hq hqmax
  have hp2 : n * (n ^ (-(3 / 8 : ℝ))) ^ 2 = n ^ (1 / 4 : ℝ) := by
    conv_lhs => lhs; rw [← Real.rpow_one n]
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hn0.le, ← Real.rpow_add hn0]
    norm_num
  have hp3 : n * (n ^ (-(3 / 8 : ℝ))) ^ 3 = n ^ (-(1 / 8 : ℝ)) := by
    conv_lhs => lhs; rw [← Real.rpow_one n]
    rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul hn0.le, ← Real.rpow_add hn0]
    norm_num
  have hp4 : (n ^ (1 / 4 : ℝ)) ^ 4 = n := by
    rw [← Real.rpow_natCast _ 4, ← Real.rpow_mul hn0.le]
    norm_num
  have hinv : n ^ (-(1 / 4 : ℝ)) * n ^ (1 / 4 : ℝ) = 1 := by
    rw [← Real.rpow_add hn0]
    norm_num
  have hprod : n * T ^ 2 ≤ c ^ 2 * n ^ (1 / 4 : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hT hTmax 2) hn0.le
    nlinarith [hp2]
  have hqbound : q ≤ n ^ (1 / 4 : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hn₁.le (Real.rpow_nonneg hn0.le (1 / 4 : ℝ))
    have hp := mul_le_mul_of_nonneg_left hprod hA.le
    nlinarith [hinv]
  constructor
  · exact (pow_le_pow_left₀ hq hqbound 4).trans_eq hp4
  · have hpT3 : n * T ^ 3 ≤ c ^ 3 * n ^ (-(1 / 8 : ℝ)) := by
      have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hT hTmax 3) hn0.le
      calc
        n * T ^ 3 ≤ n * (c * n ^ (-(3 / 8 : ℝ))) ^ 3 := hh
        _ = c ^ 3 * (n * (n ^ (-(3 / 8 : ℝ))) ^ 3) := by ring
        _ = c ^ 3 * n ^ (-(1 / 8 : ℝ)) := by rw [hp3]
    have hprodq := mul_le_mul_of_nonneg_left hqmax hT
    have hsum := mul_le_mul_of_nonneg_left (add_le_add hTmax hpT3) hA.le
    nlinarith

/-- Universal positive window constants can be chosen for every positive A. -/
theorem exists_admissible_window {A ε : ℝ} (hA : 0 < A) (hε : 0 < ε) :
    ∃ c > 0, ∀ᶠ n : ℝ in atTop, ∀ T q : ℝ,
      0 ≤ T → T ≤ c * n ^ (-(3 / 8 : ℝ)) →
      0 ≤ q → q ≤ A * (1 + n * T ^ 2) → q ^ 4 ≤ n ∧ T * q ≤ ε := by
  let c := Real.sqrt (1 / (2 * A))
  have hc : 0 < c := Real.sqrt_pos.2 (by positivity)
  have hc2 : c ^ 2 = 1 / (2 * A) := Real.sq_sqrt (by positivity)
  have hAc : A * c ^ 2 < 1 := by
    rw [hc2]
    have heq : A * (1 / (2 * A)) = 1 / 2 := by field_simp
    rw [heq]
    norm_num
  exact ⟨c, hc, eventually_admissible_parameters hA hc hε hAc⟩

/-- The q choice in Proposition 3.10 dominates all three comparison requirements. -/
theorem comparison_parameter_lower_bound {n t H κ Csp C₁ : ℝ}
    (hn : 0 ≤ n) (ht : 0 ≤ t) (hsp : 0 ≤ Csp) (hκ : 0 ≤ κ)
    (hC₁ : Csp * max 1 κ ≤ C₁) (hH : H ≤ κ * n * t ^ 2) :
    Csp * max 1 (max H (t * Real.sqrt n)) ≤ C₁ * (1 + n * t ^ 2) := by
  have hnt : 0 ≤ n * t ^ 2 := mul_nonneg hn (sq_nonneg t)
  have hCsp : Csp ≤ C₁ := by
    have := mul_le_mul_of_nonneg_left (le_max_left (1 : ℝ) κ) hsp
    nlinarith
  have hCκ : Csp * κ ≤ C₁ :=
    (mul_le_mul_of_nonneg_left (le_max_right (1 : ℝ) κ) hsp).trans hC₁
  have hC₁0 : 0 ≤ C₁ := hsp.trans hCsp
  have htsqrt : t * Real.sqrt n ≤ (1 + n * t ^ 2) / 2 := by
    nlinarith [sq_nonneg (1 - t * Real.sqrt n), Real.sq_sqrt hn]
  rw [mul_max_of_nonneg _ _ hsp, mul_max_of_nonneg _ _ hsp]
  apply max_le
  · nlinarith [mul_nonneg hC₁0 hnt]
  · apply max_le
    · have hh := mul_le_mul_of_nonneg_left hH hsp
      have hk := mul_le_mul_of_nonneg_right hCκ hnt
      nlinarith
    · have hh := mul_le_mul_of_nonneg_left htsqrt hsp
      have hc := mul_le_mul_of_nonneg_right hCsp (show 0 ≤ 1 + n * t ^ 2 by positivity)
      nlinarith

/-- The elementary squaring step at the end of Proposition 3.10. -/
theorem small_precision_algebra {M C C₁ n t : ℝ}
    (hC : 0 ≤ C) (hM : M ≤ C * (C₁ * (1 + n * t ^ 2)) ^ 2) :
    M ≤ (2 * C * C₁ ^ 2) * (1 + n ^ 2 * t ^ 4) := by
  have hsq := sq_nonneg (1 - n * t ^ 2)
  have hmult := mul_nonneg (mul_nonneg hC (sq_nonneg C₁)) hsq
  nlinarith

/-- Sections 3.3–3.5 as a single analytic implication. The only spectral input
is at the earlier time T(1-1/q); the endpoint and entropy conclusions are proved.
The `hadmiss` hypothesis is supplied in sufficiently large dimensions by
`eventually_admissible_parameters`, with a universal positive window. -/
theorem small_precision_from_analytic_inputs
    {u S H V : ℝ → ℝ} {n b C₀ Csp ε κ C₁ : ℝ}
    (hn : 0 < n) (hb : 0 < b) (hC : 0 < C₀) (hsp : 2 ≤ Csp)
    (hC₁ : C₁ = Csp * max 1 κ)
    (hκ5 : 5 < κ) (hκ : 5 * (4 * C₀) ^ 2 < κ)
    (hε : 20 * C₀ * ε < Real.log 2)
    (hspTime : 40 * C₀ < Csp * Real.log 2)
    (hu : ContinuousOn u (Icc 0 b)) (hS : ContinuousOn S (Icc 0 b))
    (hu0 : ∀ t ∈ Icc 0 b, 0 ≤ u t) (hS0 : ∀ t ∈ Icc 0 b, 0 ≤ S t)
    (huinit : u 0 ≤ 1)
    (hud : RightSlopeBound u (fun t => 10 * S t * u t) 0 b)
    (hSd : RightSlopeBound S (fun t => 10 * u t * S t) 0 b)
    (hH : ContinuousOn H (Icc 0 b)) (hH0 : H 0 = 0)
    (hV : ContinuousWithinAt V (Ici 0) 0) (hV0 : V 0 ≤ 8 * n)
    (hHd : ∀ t ∈ Ico 0 b, HasDerivAt H (t * V t) t)
    (hvar : ∀ t ∈ Ioo 0 b, V t ≤ 10 * S t ^ 2)
    (hadmiss : ∀ T q : ℝ, T ∈ Icc 0 b → 0 ≤ q →
      q ≤ C₁ * (1 + n * T ^ 2) → q ^ 4 ≤ n ∧ T * q ≤ ε)
    (hspectral : ∀ T q : ℝ, T ∈ Ioc 0 b →
      Csp * max 1 (max (H T) (T * Real.sqrt n)) ≤ q → q ^ 4 ≤ n →
      u (T * (1 - 1 / q)) ≤ C₀ * q ^ 2 ∧
      S (T * (1 - 1 / q)) ≤ 2 * C₀ * Real.sqrt n) :
    (∀ t ∈ Icc 0 b, H t ≤ κ * n * t ^ 2) ∧
    (∀ t ∈ Icc 0 b,
      u t ≤ (1 + 8 * C₀ * C₁ ^ 2) * (1 + n ^ 2 * t ^ 4)) := by
  have hsp0 : 0 < Csp := by linarith
  have hκ0 : 0 ≤ κ := by linarith
  have hC₁sp : Csp ≤ C₁ := by
    rw [hC₁]
    simpa using mul_le_mul_of_nonneg_left (le_max_left (1 : ℝ) κ) hsp0.le
  have hC₁0 : 0 < C₁ := hsp0.trans_le hC₁sp
  have hep : ∀ T q : ℝ, T ∈ Ioc 0 b →
      Csp * max 1 (max (H T) (T * Real.sqrt n)) ≤ q →
      q ^ 4 ≤ n → T * q ≤ ε →
      u T ≤ (4 * C₀) * q ^ 2 ∧ S T ≤ (4 * C₀) * Real.sqrt n := by
    intro T q hT hq hnq hTq
    have hqsp : Csp ≤ q := by
      have hh := mul_le_mul_of_nonneg_left
        (le_max_left (1 : ℝ) (max (H T) (T * Real.sqrt n))) hsp0.le
      nlinarith
    have hq1 : 1 < q := by linarith
    have hq0 : 0 < q := by linarith
    have ha0 : 0 ≤ T * (1 - 1 / q) := by
      apply mul_nonneg hT.1.le
      have hh : 1 / q ≤ 1 := (div_le_one hq0).2 (by linarith)
      linarith
    have hinterval : Icc (T * (1 - 1 / q)) T ⊆ Icc 0 b :=
      Icc_subset_Icc ha0 hT.2
    obtain ⟨hus, hSs⟩ := hspectral T q hT hq hnq
    have hqscale : Csp * (T * Real.sqrt n) ≤ q := by
      have hh : T * Real.sqrt n ≤ max 1 (max (H T) (T * Real.sqrt n)) :=
        (le_max_right _ _).trans (le_max_right _ _)
      exact (mul_le_mul_of_nonneg_left hh hsp0.le).trans hq
    apply endpoint_estimate hT.1 hq1 hn hC hsp0 hε hspTime hTq hqscale
      (hu.mono hinterval) (hS.mono hinterval)
      (fun t ht => hu0 t (hinterval ht)) (fun t ht => hS0 t (hinterval ht)) hus hSs
    · intro x hx
      exact hud x ⟨ha0.trans hx.1, hx.2.trans_le hT.2⟩
    · intro x hx
      exact hSd x ⟨ha0.trans hx.1, hx.2.trans_le hT.2⟩
  have hentropy : ∀ t ∈ Icc 0 b, H t ≤ κ * n * t ^ 2 := by
    apply entropy_barrier hb hn (show 0 ≤ 4 * C₀ by positivity) hκ hκ5
      hH hH0 hV hV0 hHd hvar (fun t ht => hS0 t (Ioo_subset_Icc_self ht))
    intro T hT hcontact
    let q := Csp * max 1 (max (H T) (T * Real.sqrt n))
    have hq0 : 0 ≤ q := mul_nonneg hsp0.le ((le_max_left _ _).trans' (by norm_num))
    have hqmax : q ≤ C₁ * (1 + n * T ^ 2) :=
      comparison_parameter_lower_bound hn.le hT.1.le hsp0.le hκ0
        (by rw [hC₁]) hcontact.le
    obtain ⟨hqn, hTq⟩ := hadmiss T q (Ioo_subset_Icc_self hT) hq0 hqmax
    exact (hep T q ⟨hT.1, hT.2.le⟩ le_rfl hqn hTq).2
  refine ⟨hentropy, ?_⟩
  intro T hT
  rcases eq_or_lt_of_le hT.1 with rfl | hT0
  · have hcoef : 0 ≤ 8 * C₀ * C₁ ^ 2 := by positivity
    simpa using huinit.trans (show (1 : ℝ) ≤ 1 + 8 * C₀ * C₁ ^ 2 by linarith)
  let q := C₁ * (1 + n * T ^ 2)
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hqreq : Csp * max 1 (max (H T) (T * Real.sqrt n)) ≤ q :=
    comparison_parameter_lower_bound hn.le hT.1 hsp0.le hκ0
      (by rw [hC₁]) (hentropy T hT)
  obtain ⟨hqn, hTq⟩ := hadmiss T q hT hq0 le_rfl
  have huT := (hep T q ⟨hT0, hT.2⟩ hqreq hqn hTq).1
  have halg := small_precision_algebra (show 0 ≤ 4 * C₀ by positivity) huT
  have hnonneg : 0 ≤ 1 + n ^ 2 * T ^ 4 := by positivity
  nlinarith

/-- The exact power identity responsible for the exponent 2/5. -/
theorem balance_exponents {n : ℝ} (hn : 0 < n) :
    n ^ 2 * (n ^ (-(2 / 5 : ℝ))) ^ 4 = n ^ (2 / 5 : ℝ) := by
  rw [← Real.rpow_natCast n 2, ← Real.rpow_natCast _ 4, ← Real.rpow_mul hn.le,
    ← Real.rpow_add hn]
  norm_num

/-- The final small- and large-precision split. This is an optimization theorem about
any scalar function, not a definition or assumed bound for covariance. -/
theorem optimize_precision {f : ℝ → ℝ} {n C cutoff : ℝ}
    (hn : 1 ≤ n) (hC : 1 ≤ C)
    (hcutoff : n ^ (-(2 / 5 : ℝ)) ≤ cutoff)
    (hsmall : ∀ t ∈ Icc 0 cutoff, f t ≤ C * (1 + n ^ 2 * t ^ 4))
    (hlarge : ∀ t, 0 < t → f t ≤ 1 / (2 * t)) :
    ∀ t, 0 ≤ t → f t ≤ (2 * C) * n ^ (2 / 5 : ℝ) := by
  have hn0 : 0 < n := by linarith
  have hscale : 0 < n ^ (-(2 / 5 : ℝ)) := Real.rpow_pos_of_pos hn0 _
  have hnp : 1 ≤ n ^ (2 / 5 : ℝ) := Real.one_le_rpow hn (by norm_num)
  intro t ht
  by_cases hts : t ≤ n ^ (-(2 / 5 : ℝ))
  · have hs := hsmall t ⟨ht, hts.trans hcutoff⟩
    have hpow : t ^ 4 ≤ (n ^ (-(2 / 5 : ℝ))) ^ 4 := pow_le_pow_left₀ ht hts 4
    have he := balance_exponents hn0
    have hmul := mul_le_mul_of_nonneg_left hpow (sq_nonneg n)
    have hmulC := mul_le_mul_of_nonneg_left hmul (show 0 ≤ C by linarith)
    nlinarith [mul_nonneg (show 0 ≤ C by linarith) (show 0 ≤ n ^ (2 / 5 : ℝ) - 1 by linarith)]
  · have hst : n ^ (-(2 / 5 : ℝ)) ≤ t := (lt_of_not_ge hts).le
    have ht0 : 0 < t := hscale.trans_le hst
    have hl := hlarge t ht0
    have hi : 1 / (2 * t) ≤ 1 / (2 * n ^ (-(2 / 5 : ℝ))) := by
      apply one_div_le_one_div_of_le (by positivity)
      linarith
    have hident : 1 / (2 * n ^ (-(2 / 5 : ℝ))) = n ^ (2 / 5 : ℝ) / 2 := by
      rw [Real.rpow_neg hn0.le]
      field_simp
    rw [hident] at hi
    nlinarith [mul_le_mul_of_nonneg_right hC (show 0 ≤ n ^ (2 / 5 : ℝ) by positivity)]

/-- The optimal scale eventually lies inside the n^(-3/8) entropy window. -/
theorem eventually_optimal_scale_in_window {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℝ in atTop, n ^ (-(2 / 5 : ℝ)) ≤ c * n ^ (-(3 / 8 : ℝ)) := by
  have ht : Tendsto (fun n : ℝ => n ^ (-(1 / 40 : ℝ))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num)
  have he : ∀ᶠ n : ℝ in atTop, n ^ (-(1 / 40 : ℝ)) < c :=
    ht.eventually (gt_mem_nhds hc)
  filter_upwards [he, eventually_gt_atTop (0 : ℝ)] with n hn hn0
  have hm := mul_le_mul_of_nonneg_right hn.le
    (Real.rpow_nonneg hn0.le (-(3 / 8 : ℝ)))
  rw [← Real.rpow_add hn0] at hm
  norm_num at hm ⊢
  exact hm

/-- A crude n-bound absorbs all dimensions excluded by an eventual estimate.
This is the finite-dimension constant-enlargement step in the final proof. -/
theorem uniformize_dimension_bound {f : ℝ → ℝ → ℝ} {C : ℝ}
    (heventual : ∀ᶠ n : ℝ in atTop, ∀ t ≥ 0, f n t ≤ C * n ^ (2 / 5 : ℝ))
    (hcrude : ∀ n ≥ 1, ∀ t ≥ 0, f n t ≤ n) :
    ∃ D > 0, ∀ n ≥ 1, ∀ t ≥ 0, f n t ≤ D * n ^ (2 / 5 : ℝ) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp heventual
  let D := max C (max 1 N)
  have hD1 : 1 ≤ D := (le_max_left _ _).trans (le_max_right _ _)
  have hD0 : 0 < D := by linarith
  have hDC : C ≤ D := le_max_left _ _
  have hDN : N ≤ D := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨D, hD0, ?_⟩
  intro n hn t ht
  have hpow : 1 ≤ n ^ (2 / 5 : ℝ) := Real.one_le_rpow hn (by norm_num)
  by_cases hnN : N ≤ n
  · exact (hN n hnN t ht).trans
      (mul_le_mul_of_nonneg_right hDC (by positivity))
  · have hfn := hcrude n hn t ht
    have hnD : n ≤ D := (lt_of_not_ge hnN).le.trans hDN
    have hm := mul_le_mul_of_nonneg_left hpow hD0.le
    nlinarith

/-- Natural-dimension version of the same constant-enlargement step. -/
theorem uniformize_natural_dimension_bound {f : ℕ → ℝ → ℝ} {C : ℝ}
    (heventual : ∀ᶠ n : ℕ in atTop, ∀ t ≥ 0, f n t ≤ C * (n : ℝ) ^ (2 / 5 : ℝ))
    (hcrude : ∀ n ≥ 1, ∀ t ≥ 0, f n t ≤ (n : ℝ)) :
    ∃ D > 0, ∀ n ≥ 1, ∀ t ≥ 0, f n t ≤ D * (n : ℝ) ^ (2 / 5 : ℝ) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp heventual
  let D := max C (max 1 (N : ℝ))
  have hD1 : 1 ≤ D := (le_max_left _ _).trans (le_max_right _ _)
  have hD0 : 0 < D := by linarith
  have hDC : C ≤ D := le_max_left _ _
  have hDN : (N : ℝ) ≤ D := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨D, hD0, ?_⟩
  intro n hn t ht
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow : 1 ≤ (n : ℝ) ^ (2 / 5 : ℝ) := Real.one_le_rpow hn1 (by norm_num)
  by_cases hnN : N ≤ n
  · exact (hN n hnN t ht).trans
      (mul_le_mul_of_nonneg_right hDC (by positivity))
  · have hfn := hcrude n hn t ht
    have hnN' : (n : ℝ) ≤ N := by exact_mod_cast (lt_of_not_ge hnN).le
    have hnD : (n : ℝ) ≤ D := hnN'.trans hDN
    have hm := mul_le_mul_of_nonneg_left hpow hD0.le
    nlinarith

/-- Explicit analytic prerequisites for the upper-bound closure.

In the intended application `u` and `S` are the operator and Hilbert–Schmidt
norms of the actual uncentered moment matrix, `H` is relative entropy, and `V`
is radial variance. This structure neither defines those quantities nor proves
that a measure has these properties. Its spectral field is precisely the
independent earlier-time estimate from Section 3.2, not an endpoint bound. -/
structure ScalarFlowInputs (n C₀ B : ℝ) (u S H V : ℝ → ℝ) : Prop where
  u_continuous : ContinuousOn u (Ici 0)
  S_continuous : ContinuousOn S (Ici 0)
  u_nonnegative : ∀ t ≥ 0, 0 ≤ u t
  S_nonnegative : ∀ t ≥ 0, 0 ≤ S t
  u_initial : u 0 ≤ 1
  u_slope : ∀ b > 0, RightSlopeBound u (fun t => 10 * S t * u t) 0 b
  S_slope : ∀ b > 0, RightSlopeBound S (fun t => 10 * u t * S t) 0 b
  H_continuous : ContinuousOn H (Ici 0)
  H_initial : H 0 = 0
  V_continuous : ContinuousWithinAt V (Ici 0) 0
  V_initial : V 0 ≤ 8 * n
  H_derivative : ∀ t ≥ 0, HasDerivAt H (t * V t) t
  V_bound : ∀ t ≥ 0, V t ≤ 10 * S t ^ 2
  earlier_spectrum : ∀ T q : ℝ, 0 < T → 1 < q →
    B * max 1 (max (H T) (T * Real.sqrt n)) ≤ q → q ^ 4 ≤ n →
    u (T * (1 - 1 / q)) ≤ C₀ * q ^ 2 ∧
    S (T * (1 - 1 / q)) ≤ 2 * C₀ * Real.sqrt n

/-- Universal small-precision constants, with every scalar admissibility and
first-contact argument discharged. The measure-theoretic and spectral bridge
is explicitly represented by `ScalarFlowInputs`. -/
theorem eventually_small_precision {C₀ B : ℝ} (hC₀ : 0 < C₀) :
    ∃ c C κ : ℝ, 0 < c ∧ 1 ≤ C ∧ 0 < κ ∧
      ∀ᶠ n : ℝ in atTop, ∀ u S H V : ℝ → ℝ,
        ScalarFlowInputs n C₀ B u S H V →
        ∀ t ∈ Icc 0 (c * n ^ (-(3 / 8 : ℝ))),
          H t ≤ κ * n * t ^ 2 ∧ u t ≤ C * (1 + n ^ 2 * t ^ 4) := by
  obtain ⟨ε, Csp, κ, hε0, hsp, hspB, hε, hspTime, hκ5, hκ⟩ :=
    choose_propagation_constants (B := B) hC₀
  let C₁ := Csp * max 1 κ
  have hsp0 : 0 < Csp := by linarith
  have hC₁0 : 0 < C₁ := mul_pos hsp0 (lt_max_of_lt_left (by norm_num))
  obtain ⟨c, hc, hadm⟩ := exists_admissible_window hC₁0 hε0
  let C := 1 + 8 * C₀ * C₁ ^ 2
  have hC1 : 1 ≤ C := by
    have hh : 0 ≤ 8 * C₀ * C₁ ^ 2 := by positivity
    dsimp [C]
    linarith
  refine ⟨c, C, κ, hc, hC1, by linarith, ?_⟩
  filter_upwards [hadm, eventually_gt_atTop (0 : ℝ)] with n hnAdmiss hn0
  intro u S H V data
  let b := c * n ^ (-(3 / 8 : ℝ))
  have hb : 0 < b := mul_pos hc (Real.rpow_pos_of_pos hn0 _)
  have hinterval : Icc 0 b ⊆ Ici 0 := Icc_subset_Ici_self
  have hresult := small_precision_from_analytic_inputs hn0 hb hC₀ hsp rfl hκ5 hκ hε hspTime
    (data.u_continuous.mono hinterval) (data.S_continuous.mono hinterval)
    (fun t ht => data.u_nonnegative t ht.1) (fun t ht => data.S_nonnegative t ht.1)
    data.u_initial (data.u_slope b hb) (data.S_slope b hb)
    (data.H_continuous.mono hinterval) data.H_initial data.V_continuous data.V_initial
    (fun t ht => data.H_derivative t ht.1) (fun t ht => data.V_bound t ht.1.le)
    (fun T q hT hq hqmax => hnAdmiss T q hT.1 hT.2 hq hqmax)
    (fun T q hT hq hqn => by
      have hm : 1 ≤ max 1 (max (H T) (T * Real.sqrt n)) := le_max_left _ _
      have hm0 : 0 ≤ max 1 (max (H T) (T * Real.sqrt n)) := by linarith
      have hqsp : Csp ≤ q := by
        have hh := mul_le_mul_of_nonneg_left hm hsp0.le
        nlinarith
      have hq1 : 1 < q := by linarith
      exact data.earlier_spectrum T q hT.1 hq1
        ((mul_le_mul_of_nonneg_right hspB hm0).trans hq) hqn)
  intro t ht
  exact ⟨hresult.1 t ht, hresult.2 t ht⟩

/-- The complete analytic upper-bound chain, ending in n^(2/5), conditional on
explicit flow/spectral inputs and the independently established Brascamp–Lieb
and crude trace bounds for the scalar quantity being bounded. This theorem does
not assert that those hypotheses hold for any measure. -/
theorem uniform_upper_from_analytic_inputs
    {C₀ B : ℝ} {u S H V σ : ℕ → ℝ → ℝ}
    (hC₀ : 0 < C₀)
    (hdata : ∀ n : ℕ, 1 ≤ n → ScalarFlowInputs (n : ℝ) C₀ B (u n) (S n) (H n) (V n))
    (hσu : ∀ n ≥ 1, ∀ t ≥ 0, σ n t ≤ u n t)
    (hBL : ∀ n ≥ 1, ∀ t > 0, σ n t ≤ 1 / (2 * t))
    (hcrude : ∀ n ≥ 1, ∀ t ≥ 0, σ n t ≤ (n : ℝ)) :
    ∃ D > 0, ∀ n ≥ 1, ∀ t ≥ 0, σ n t ≤ D * (n : ℝ) ^ (2 / 5 : ℝ) := by
  obtain ⟨c, C, κ, hc, hC, hκ, hsmall⟩ := eventually_small_precision (B := B) hC₀
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have heventual : ∀ᶠ n : ℕ in atTop, ∀ t ≥ 0,
      σ n t ≤ (2 * C) * (n : ℝ) ^ (2 / 5 : ℝ) := by
    filter_upwards [hcast.eventually hsmall,
      hcast.eventually (eventually_optimal_scale_in_window hc),
      eventually_ge_atTop (1 : ℕ)] with n hnsmall hnwindow hn1
    have hs := hnsmall (u n) (S n) (H n) (V n) (hdata n hn1)
    have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    exact optimize_precision hn1' hC hnwindow
      (fun t ht => (hσu n hn1 t ht.1).trans (hs t ht).2)
      (hBL n hn1)
  exact uniformize_natural_dimension_bound heventual hcrude

end GaussianTilt.UpperDynamics
