import GaussianTilt.MomentMapFrechetDifferentiability

/-! # Pointwise recovery of the variational source

Monotone convergence of the recovered source densities and the proved
partition upper bound force recovery everywhere. Continuity upgrades the
result from almost-everywhere equality; no biconjugacy theorem is assumed.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators
namespace GaussianTilt.MomentMapCoercivity
variable {n : ℕ}

lemma fenchel_antitone_dual {K : Set (E n)} {u v : E n → ℝ} {R : ℝ}
    (hKn : K.Nonempty) (hK : ∀ y ∈ K, ‖y‖ ≤ R) (hu : ∀ y ∈ K, 0 ≤ u y)
    (huv : ∀ y ∈ K, u y ≤ v y) (x : E n) : fenchel K v x ≤ fenchel K u x := by
  apply csSup_le (fenchelValues_nonempty hKn _ _)
  rintro a ⟨y, hy, rfl⟩
  exact (sub_le_sub_left (huv y hy) _).trans (fenchel_young hK hu x hy)

lemma recoveredDual_nonneg {ψ : E n → ℝ} (hψ0 : ψ 0 = 0) (hψ : ∀ x, 0 ≤ ψ x) (k : ℕ) (y : E n) :
    0 ≤ recoveredDual ψ k y :=
  fenchel_nonneg (sourceBall_norm_bound k) (fun x _ => hψ x) (zero_mem_sourceBall k) hψ0 y

theorem recovered_source_ge_source_of_partition_bound
    {K : Set (E n)} {ψ : E n → ℝ} {R : ℝ}
    (hKn : K.Nonempty) (hK : ∀ y ∈ K, ‖y‖ ≤ R)
    (hψ0 : ψ 0 = 0) (hψ : ∀ x, 0 ≤ ψ x) (hψc : Continuous ψ)
    (hψi : Integrable (fun x => Real.exp (-ψ x)))
    (hφi : ∀ k, Integrable (fun x => Real.exp (-fenchel K (recoveredDual ψ k) x)))
    (hpart : ∀ k, dualPartition K (recoveredDual ψ k) ≤ ∫ x, Real.exp (-ψ x)) :
    ∀ k x, ψ x ≤ fenchel K (recoveredDual ψ k) x := by
  let F : ℕ → E n → ℝ≥0∞ := fun k x => ENNReal.ofReal (Real.exp (-fenchel K (recoveredDual ψ k) x))
  let G : E n → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (-ψ x))
  have hφc (k : ℕ) : Continuous (fenchel K (recoveredDual ψ k)) :=
    (fenchel_lipschitz hKn hK (fun y _ => recoveredDual_nonneg hψ0 hψ k y)).continuous
  have hFm (k : ℕ) : Measurable (F k) :=
    (Real.continuous_exp.comp (hφc k).neg).measurable.ennreal_ofReal
  have hmono : Monotone F := by
    intro i j hij x
    apply ENNReal.ofReal_mono
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    exact fenchel_antitone_dual hKn hK (fun y _ => recoveredDual_nonneg hψ0 hψ i y)
      (fun y _ => recoveredDual_monotone hψ y hij) x
  have hGint : (∫⁻ x, G x) = ENNReal.ofReal (∫ x, Real.exp (-ψ x)) :=
    (ofReal_integral_eq_lintegral_ofReal hψi (ae_of_all _ (fun x => (Real.exp_pos _).le))).symm
  have hFint (k : ℕ) : (∫⁻ x, F k x) = ENNReal.ofReal (dualPartition K (recoveredDual ψ k)) :=
    (ofReal_integral_eq_lintegral_ofReal (hφi k) (ae_of_all _ (fun x => (Real.exp_pos _).le))).symm
  have hGle (x : E n) : G x ≤ ⨆ k, F k x := by
    have hx : x ∈ ⋃ k : ℕ, sourceBall (n := n) k := by rw [iUnion_sourceBall]; trivial
    obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    apply le_trans _ (le_iSup (fun k => F k x) k)
    apply ENNReal.ofReal_mono
    exact Real.exp_le_exp.mpr (neg_le_neg (fenchel_recoveredDual_le_source hKn hψ k hk))
  have hsupint : (∫⁻ x, ⨆ k, F k x) ≤ ∫⁻ x, G x := by
    rw [lintegral_iSup hFm hmono, hGint]
    apply iSup_le
    intro k
    rw [hFint]
    exact ENNReal.ofReal_mono (hpart k)
  have hGF : G =ᵐ[volume] (fun x => ⨆ k, F k x) :=
    ae_eq_of_ae_le_of_lintegral_le (ae_of_all _ hGle)
      (by rw [hGint]; exact ENNReal.ofReal_ne_top)
      (Measurable.iSup hFm).aemeasurable hsupint
  intro k
  have hAE : ψ ≤ᵐ[volume] fenchel K (recoveredDual ψ k) := by
    filter_upwards [hGF] with x hx
    have h := le_iSup (fun k => F k x) k
    rw [← hx] at h
    have hr := ENNReal.toReal_mono (show G x ≠ ⊤ from ENNReal.ofReal_ne_top) h
    change (ENNReal.ofReal (Real.exp (-fenchel K (recoveredDual ψ k) x))).toReal ≤
      (ENNReal.ofReal (Real.exp (-ψ x))).toReal at hr
    simp only [ENNReal.toReal_ofReal (Real.exp_nonneg _)] at hr
    exact neg_le_neg_iff.mp (Real.exp_le_exp.mp hr)
  have heq : (fun x => max (ψ x) (fenchel K (recoveredDual ψ k) x)) =ᵐ[volume]
      fenchel K (recoveredDual ψ k) := hAE.mono (fun x hx => max_eq_right hx)
  have hall := Measure.eq_of_ae_eq heq (hψc.max (hφc k)) (hφc k)
  intro x
  exact max_eq_right_iff.mp (congrFun hall x)

theorem recovered_source_eq_on_sourceBall_of_partition_bound
    {K : Set (E n)} {ψ : E n → ℝ} {R : ℝ}
    (hKn : K.Nonempty) (hK : ∀ y ∈ K, ‖y‖ ≤ R)
    (hψ0 : ψ 0 = 0) (hψ : ∀ x, 0 ≤ ψ x) (hψc : Continuous ψ)
    (hψi : Integrable (fun x => Real.exp (-ψ x)))
    (hφi : ∀ k, Integrable (fun x => Real.exp (-fenchel K (recoveredDual ψ k) x)))
    (hpart : ∀ k, dualPartition K (recoveredDual ψ k) ≤ ∫ x, Real.exp (-ψ x))
    (k : ℕ) {x : E n} (hx : x ∈ sourceBall k) :
    fenchel K (recoveredDual ψ k) x = ψ x :=
  le_antisymm (fenchel_recoveredDual_le_source hKn hψ k hx)
    (recovered_source_ge_source_of_partition_bound hKn hK hψ0 hψ hψc hψi hφi hpart k x)

end GaussianTilt.MomentMapCoercivity
