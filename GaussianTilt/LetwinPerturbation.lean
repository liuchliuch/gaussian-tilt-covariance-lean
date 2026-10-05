import GaussianTilt.LetwinConvexity

/-! # Local convexity of the functional Brascamp--Lieb perturbation -/
noncomputable section
open Set Filter MeasureTheory Matrix
open scoped Topology ContDiff BigOperators
namespace GaussianTilt.Letwin

lemma second_deriv_add {f g : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (t : ℝ) :
    deriv (deriv (fun s => f s + g s)) t = deriv (deriv f) t + deriv (deriv g) t := by
  have heq : deriv (fun s => f s + g s) = fun s => deriv f s + deriv g s := by
    funext s
    exact deriv_fun_add (hf.differentiable (by norm_num) s) (hg.differentiable (by norm_num) s)
  rw [heq]
  exact deriv_fun_add (hf.differentiable_deriv_two t) (hg.differentiable_deriv_two t)

lemma second_deriv_sub {f g : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (t : ℝ) :
    deriv (deriv (fun s => f s - g s)) t = deriv (deriv f) t - deriv (deriv g) t := by
  have heq : deriv (fun s => f s - g s) = fun s => deriv f s - deriv g s := by
    funext s
    exact deriv_fun_sub (hf.differentiable (by norm_num) s) (hg.differentiable (by norm_num) s)
  rw [heq]
  exact deriv_fun_sub (hf.differentiable_deriv_two t) (hg.differentiable_deriv_two t)

lemma second_deriv_mul {f g : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (t : ℝ) :
    deriv (deriv (fun s => f s * g s)) t =
      deriv (deriv f) t * g t + 2 * deriv f t * deriv g t + f t * deriv (deriv g) t := by
  have heq : deriv (fun s => f s * g s) = fun s => deriv f s * g s + f s * deriv g s := by
    funext s
    exact deriv_fun_mul (hf.differentiable (by norm_num) s) (hg.differentiable (by norm_num) s)
  rw [heq]
  have h := ((hf.differentiable_deriv_two t).hasDerivAt.mul
    (hg.differentiable (by norm_num) t).hasDerivAt).add
    ((hf.differentiable (by norm_num) t).hasDerivAt.mul (hg.differentiable_deriv_two t).hasDerivAt)
  have h' := h.deriv
  change deriv (fun s => deriv f s * g s + f s * deriv g s) t = _ at h'
  rw [h']
  ring

lemma second_deriv_perturbation_scalar {P F A : ℝ → ℝ}
    (hP : ContDiff ℝ 2 P) (hF : ContDiff ℝ 2 F) (hA : ContDiff ℝ 2 A) (s ε : ℝ) :
    deriv (deriv (fun t => P t - (t * s) * F t + (t * s)^2 / 2 * (A t + ε))) 0 =
      deriv (deriv P) 0 - 2 * s * deriv F 0 + s ^ 2 * (A 0 + ε) := by
  let q := fun t : ℝ => t * s
  let r := fun t : ℝ => (t * s)^2 / 2
  have hq : ContDiff ℝ 2 q := by dsimp [q]; fun_prop
  have hr : ContDiff ℝ 2 r := by dsimp [r]; fun_prop
  have hqd : deriv q = fun _ => s := by
    funext t
    simp [q]
  have hrd : deriv r = fun t => t * s ^ 2 := by
    funext t
    have h := (((hasDerivAt_id t).mul_const s).pow 2).div_const 2
    convert h.deriv using 1
    dsimp [r]
    ring
  have hqdd : deriv (deriv q) 0 = 0 := by rw [hqd]; simp
  have hrdd : deriv (deriv r) 0 = s ^ 2 := by
    rw [hrd]
    simp
  change deriv (deriv (fun t => P t - q t * F t + r t * (A t + ε))) 0 = _
  rw [second_deriv_add (hP.sub (hq.mul hF)) (hr.mul (hA.add contDiff_const)),
    second_deriv_sub hP (hq.mul hF), second_deriv_mul hq hF,
    second_deriv_mul hr (hA.add contDiff_const), hqdd, hrdd, hqd, hrd]
  simp [q, r]

/-- The perturbation on time times the original coordinate space. -/
def functionalPerturbation {n : ℕ} (φ f a : CoordinateSpace n → ℝ) (ε : ℝ)
    (p : ℝ × CoordinateSpace n) : ℝ :=
  φ p.2 - p.1 * f p.2 + p.1 ^ 2 / 2 * (a p.2 + ε)

lemma functionalPerturbation_contDiff {n : ℕ} {φ f a : CoordinateSpace n → ℝ}
    {k : WithTop ℕ∞} (hφ : ContDiff ℝ k φ) (hf : ContDiff ℝ k f) (ha : ContDiff ℝ k a) (ε : ℝ) :
    ContDiff ℝ k (functionalPerturbation φ f a ε) := by
  exact ((hφ.comp contDiff_snd).sub (contDiff_fst.mul (hf.comp contDiff_snd))).add
    (((contDiff_fst.pow 2).div_const 2).mul ((ha.comp contDiff_snd).add contDiff_const))

/-- The actual joint Hessian at time zero has exactly the Schur block needed
for the perturbation argument. -/
theorem functionalPerturbation_second_at_zero {n : ℕ} {φ f a : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hf : ContDiff ℝ 2 f) (ha : ContDiff ℝ 2 a)
    (ε : ℝ) (x v : CoordinateSpace n) (s : ℝ) :
    fderiv ℝ (fderiv ℝ (functionalPerturbation φ f a ε)) (0, x) (s, v) (s, v) =
      matrixQuadratic (coordinateHessian φ x) v - 2 * s * fderiv ℝ f x v + s ^ 2 * (a x + ε) := by
  have hline := second_deriv_affine_line_comp (functionalPerturbation_contDiff hφ hf ha ε) (0, x) (s, v) 0
  simp only [zero_smul, add_zero] at hline
  rw [← hline]
  have heq : (fun t : ℝ => functionalPerturbation φ f a ε ((0, x) + t • (s, v))) =
      (fun t => φ (x + t • v) - (t * s) * f (x + t • v) + (t * s)^2 / 2 * (a (x + t • v) + ε)) := by
    funext t
    simp [functionalPerturbation]
  rw [heq, second_deriv_perturbation_scalar (P := fun t => φ (x + t • v))
    (F := fun t => f (x + t • v)) (A := fun t => a (x + t • v))
    (hφ.comp (contDiff_const.add (contDiff_id.smul contDiff_const)))
    (hf.comp (contDiff_const.add (contDiff_id.smul contDiff_const)))
    (ha.comp (contDiff_const.add (contDiff_id.smul contDiff_const))),
    second_deriv_affine_line_comp hφ x v 0, deriv_affine_line_comp (hf.differentiable (by norm_num)) x v 0]
  simp only [zero_smul, add_zero]
  rw [secondFDeriv_eq_hessianQuadratic hφ.contDiffAt]

lemma smooth_inverseHessian {n : ℕ} {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hdet : ∀ x, (coordinateHessian φ x).det ≠ 0) (i j : Fin n) :
    ContDiff ℝ ∞ (fun x => inverseHessian φ x i j) :=
  contDiff_matrix_inv (smooth_coordinateHessian hφ) hdet i j

lemma smooth_inverseHessian_energy {n : ℕ} {φ f : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hf : ContDiff ℝ ∞ f)
    (hdet : ∀ x, (coordinateHessian φ x).det ≠ 0) :
    ContDiff ℝ ∞ (diffusionGamma (inverseHessian φ) f f) := by
  unfold diffusionGamma diffusionFlux
  apply ContDiff.sum
  intro i _
  apply ContDiff.mul
  · apply ContDiff.sum
    intro j _
    exact (smooth_inverseHessian hφ hdet i j).mul (smooth_coordinateDerivative hf j)
  · exact smooth_coordinateDerivative hf i

lemma diffusionGamma_eq_matrixQuadratic {n : ℕ}
    (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ) (f : CoordinateSpace n → ℝ) (x : CoordinateSpace n) :
    diffusionGamma A f f x = matrixQuadratic (A x) (coordinateGradient f x) := by
  simp only [diffusionGamma, diffusionFlux, matrixQuadratic, Matrix.mulVec, dotProduct, coordinateGradient]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma fderiv_eq_gradient_dotProduct {n : ℕ} (f : CoordinateSpace n → ℝ) (x v : CoordinateSpace n) :
    fderiv ℝ f x v = coordinateGradient f x ⬝ᵥ v := by
  rw [fderiv_apply_eq_sum_coordinates]
  simp only [coordinateGradient, dotProduct, mul_comm]

/-- Strict positivity of the actual joint Hessian at time zero. -/
theorem functionalPerturbation_second_pos_at_zero {n : ℕ} {φ f : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hf : ContDiff ℝ ∞ f)
    (hH : ∀ x, (coordinateHessian φ x).PosDef) {ε : ℝ} (hε : 0 < ε)
    (x : CoordinateSpace n) (w : ℝ × CoordinateSpace n) (hw : w ≠ 0) :
    0 < fderiv ℝ (fderiv ℝ (functionalPerturbation φ f (diffusionGamma (inverseHessian φ) f f) ε))
      (0, x) w w := by
  obtain ⟨s, v⟩ := w
  have ha := smooth_inverseHessian_energy hφ hf (fun x => (hH x).det_pos.ne')
  rw [functionalPerturbation_second_at_zero (contDiff_infty.mp hφ 2)
    (contDiff_infty.mp hf 2) (contDiff_infty.mp ha 2),
    diffusionGamma_eq_matrixQuadratic, fderiv_eq_gradient_dotProduct]
  exact gradient_energy_form_pos (hH x) (coordinateGradient f x) v s hε hw

lemma bilinear_nonneg_of_unit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v : E, ‖v‖ = 1 → 0 ≤ B v v) (v : E) : 0 ≤ B v v := by
  by_cases hv : v = 0
  · simp [hv]
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hu : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
  have h := hB ((‖v‖⁻¹ : ℝ) • v) hu
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul] at h
  exact (mul_nonneg_iff_of_pos_left (inv_pos.mpr hn)).mp
    ((mul_nonneg_iff_of_pos_left (inv_pos.mpr hn)).mp h)

/-- The local joint convexity required by the Prékopa perturbation proof of
functional Brascamp--Lieb. The time interval is uniform over the entire compact
convex set K. -/
theorem functionalPerturbation_locally_convex {n : ℕ} {φ f : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hf : ContDiff ℝ ∞ f)
    (hH : ∀ x, (coordinateHessian φ x).PosDef)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (hKc : Convex ℝ K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ConvexOn ℝ (Ioo (-δ) δ ×ˢ K)
      (functionalPerturbation φ f (diffusionGamma (inverseHessian φ) f f) ε) := by
  let Φ := functionalPerturbation φ f (diffusionGamma (inverseHessian φ) f f) ε
  have ha := smooth_inverseHessian_energy hφ hf (fun x => (hH x).det_pos.ne')
  have hΦ : ContDiff ℝ ∞ Φ := functionalPerturbation_contDiff hφ hf ha ε
  have hΦ2 : ContDiff ℝ 2 Φ := contDiff_infty.mp hΦ 2
  have hDD : Continuous (fderiv ℝ (fderiv ℝ Φ)) :=
    (hΦ2.fderiv_right (m := 1) (by norm_num)).continuous_fderiv le_rfl
  let Z : Set (CoordinateSpace n × (ℝ × CoordinateSpace n)) :=
    K ×ˢ Metric.sphere 0 1
  have hZ : IsCompact Z := hK.prod (isCompact_sphere _ _)
  let q := fun z : ℝ × (CoordinateSpace n × (ℝ × CoordinateSpace n)) =>
    fderiv ℝ (fderiv ℝ Φ) (z.1, z.2.1) z.2.2 z.2.2
  have hq : Continuous q :=
    ((hDD.comp (continuous_fst.prodMk continuous_snd.fst)).clm_apply continuous_snd.snd).clm_apply continuous_snd.snd
  have hevent : ∀ᶠ t : ℝ in 𝓝 0, ∀ z ∈ Z,
      0 < fderiv ℝ (fderiv ℝ Φ) (t, z.1) z.2 z.2 := by
    apply hZ.eventually_forall_of_forall_eventually
    intro z hz
    have hnorm : ‖z.2‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hz.2
    have hne : z.2 ≠ 0 := by intro h; simp [h] at hnorm
    have hp : 0 < q (0, z) := functionalPerturbation_second_pos_at_zero hφ hf hH hε z.1 z.2 hne
    exact hq.continuousAt.eventually (lt_mem_nhds hp)
  obtain ⟨δ, hδ, hδprop⟩ := Metric.mem_nhds_iff.mp hevent
  refine ⟨δ, hδ, convexOn_of_secondFDeriv_nonneg ((convex_Ioo _ _).prod hKc) hΦ2 ?_⟩
  intro p hp v
  apply bilinear_nonneg_of_unit (fderiv ℝ (fderiv ℝ Φ) p) _ v
  intro u hu
  have ht : p.1 ∈ Metric.ball (0 : ℝ) δ := by
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_lt] using hp.1
  exact (hδprop ht (p.2, u) ⟨hp.2, by simpa only [Metric.mem_sphere, dist_zero_right] using hu⟩).le

end GaussianTilt.Letwin
