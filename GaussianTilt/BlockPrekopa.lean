import GaussianTilt.EuclideanBrascampLieb

/-!
# Compact Prékopa for arbitrary finite coordinate blocks

Fibre integrability and the Fubini identity are proved along with the
logconcavity of the actual marginal; no density formula is assumed.
-/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace GaussianTilt.BlockPrekopa
open LogConcaveMarginal EuclideanBrascampLieb

lemma logconcave_comp_linear {E F : Type*} [AddCommMonoid E] [Module ℝ E]
    [AddCommMonoid F] [Module ℝ F] {f : F → ℝ} (hf : IsLogConcave f)
    (L : E →ₗ[ℝ] F) : IsLogConcave (fun x ↦ f (L x)) := by
  refine ⟨fun x ↦ hf.1 (L x), ?_⟩
  intro x y a b ha hb hab
  simpa only [map_add, map_smul] using hf.2 (L x) (L y) a b ha hb hab

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def packLast (n : ℕ) : ((E × (Fin n → ℝ)) × ℝ) →ₗ[ℝ] E × (Fin (n + 1) → ℝ) where
  toFun p := (p.1.1, (splitLast n).symm (p.1.2, p.2))
  map_add' := by
    intro p q
    apply Prod.ext
    · rfl
    · exact (splitLast n).symm.map_add (p.1.2, p.2) (q.1.2, q.2)
  map_smul' := by
    intro c p
    apply Prod.ext
    · rfl
    · exact (splitLast n).symm.map_smul c (p.1.2, p.2)

lemma packLast_norm_left (n : ℕ) (y : Fin n → ℝ) (u : ℝ) :
    ‖y‖ ≤ ‖(splitLast n).symm (y, u)‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  have h := norm_le_pi_norm ((splitLast n).symm (y, u)) i.castSucc
  simpa only [splitLast_symm_castSucc] using h

lemma packLast_norm_right (n : ℕ) (y : Fin n → ℝ) (u : ℝ) :
    ‖u‖ ≤ ‖(splitLast n).symm (y, u)‖ := by
  have h := norm_le_pi_norm ((splitLast n).symm (y, u)) (Fin.last n)
  simpa only [splitLast_symm_last] using h

lemma marginal_measurable {n : ℕ} {f : E × (Fin n → ℝ) → ℝ} (hm : Measurable f) :
    Measurable (fun x ↦ ∫ y : Fin n → ℝ, f (x, y)) :=
  (hm.stronglyMeasurable.integral_prod_right (f := fun x y ↦ f (x, y))).measurable

/-- Prékopa over any finite coordinate block, including all integrability
needed to interpret the actual Lebesgue marginal. -/
theorem logconcave_marginal_and_fibres : ∀ {n : ℕ} {f : E × (Fin n → ℝ) → ℝ} {R : ℝ},
    IsLogConcave f → Measurable f → (∀ x y, R < ‖y‖ → f (x, y) = 0) →
    IsLogConcave (fun x ↦ ∫ y : Fin n → ℝ, f (x, y)) ∧
      ∀ x, Integrable (fun y : Fin n → ℝ ↦ f (x, y))
  | 0, f, R, hf, hm, hs => by
    have heq (x : E) : (∫ y : Fin 0 → ℝ, f (x, y)) = f (x, 0) := by
      rw [Measure.volume_pi_eq_dirac 0, integral_dirac]
    constructor
    · simp_rw [heq]
      exact logconcave_comp_linear hf (LinearMap.inl ℝ E (Fin 0 → ℝ))
    · intro x
      rw [Measure.volume_pi_eq_dirac 0]
      exact integrable_dirac (f := fun y : Fin 0 → ℝ ↦ f (x, y)) (by simp)
  | n + 1, f, R, hf, hm, hs => by
    let F : (E × (Fin n → ℝ)) × ℝ → ℝ := fun p ↦ f (packLast n p)
    let g : E × (Fin n → ℝ) → ℝ := fun p ↦ ∫ u : ℝ, F (p, u)
    have hF : IsLogConcave F := logconcave_comp_linear hf (packLast n)
    have hFm : Measurable F := hm.comp ((packLast (E := E) n).continuous_of_finiteDimensional.measurable)
    have hFs (p : E × (Fin n → ℝ)) : ∀ u ∉ Icc (-R) R, F (p, u) = 0 := by
      intro u hu
      have hu' : R < ‖u‖ := by
        rw [Real.norm_eq_abs]
        exact lt_of_not_ge (fun h ↦ hu (abs_le.mp h))
      exact hs p.1 _ (hu'.trans_le (packLast_norm_right n p.2 u))
    have hgi (p : E × (Fin n → ℝ)) : Integrable (fun u : ℝ ↦ F (p, u)) :=
      integrable_of_compact_support (logconcave_slice hF p)
        (hFm.comp measurable_prod_mk_left) ⟨-R, R, hFs p⟩
    have hg : IsLogConcave g := marginal_logconcave_of_compact_slices hF hgi
      (fun p ↦ ⟨-R, R, hFs p⟩)
    have hgm : Measurable g :=
      (hFm.stronglyMeasurable.integral_prod_right (f := fun p u ↦ F (p, u))).measurable
    have hgs (x : E) (y : Fin n → ℝ) (hy : R < ‖y‖) : g (x, y) = 0 := by
      apply integral_eq_zero_of_ae
      exact Filter.Eventually.of_forall fun u ↦ hs x _ (hy.trans_le (packLast_norm_left n y u))
    obtain ⟨hgLC, hgI⟩ := logconcave_marginal_and_fibres hg hgm hgs
    have hprod (x : E) : Integrable (fun p : (Fin n → ℝ) × ℝ ↦ F ((x, p.1), p.2)) := by
      apply (integrable_prod_iff (by
        have h := hFm.comp (show Measurable (fun p : (Fin n → ℝ) × ℝ ↦ ((x, p.1), p.2)) from by fun_prop)
        exact h.aestronglyMeasurable)).mpr
      constructor
      · exact Filter.Eventually.of_forall fun y ↦ hgi (x, y)
      · have h := hgI x
        simpa only [g, Real.norm_of_nonneg (hF.1 _)] using h
    have hwhole (x : E) : Integrable (fun y : Fin (n + 1) → ℝ ↦ f (x, y)) := by
      have h := (splitLast_measurePreserving n).integrable_comp (hprod x).aestronglyMeasurable |>.mpr (hprod x)
      simpa only [Function.comp_def, F, packLast, LinearMap.coe_mk, AddHom.coe_mk,
        Prod.mk.eta, LinearEquiv.symm_apply_apply] using h
    have hFubini (x : E) : (∫ y : Fin (n + 1) → ℝ, f (x, y)) =
        ∫ y : Fin n → ℝ, g (x, y) := by
      have h := (splitLast_measurePreserving n).integral_comp
        (splitLast n).toContinuousLinearEquiv.toHomeomorph.measurableEmbedding
        (fun p : (Fin n → ℝ) × ℝ ↦ F ((x, p.1), p.2))
      have h' : (∫ y : Fin (n + 1) → ℝ, f (x, y)) =
          ∫ p : (Fin n → ℝ) × ℝ, F ((x, p.1), p.2) := by
        simpa only [Function.comp_def, F, packLast, LinearMap.coe_mk, AddHom.coe_mk,
          Prod.mk.eta, LinearEquiv.symm_apply_apply] using h
      rw [h']
      exact integral_prod (fun p : (Fin n → ℝ) × ℝ ↦ F ((x, p.1), p.2)) (hprod x)
    exact ⟨by simpa only [hFubini] using hgLC, hwhole⟩

end GaussianTilt.BlockPrekopa
