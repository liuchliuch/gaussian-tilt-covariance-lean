import GaussianTilt.MomentMapLinearDirichletHarmonicL2Decay
import GaussianTilt.MomentMapLinearDirichletH1GradientHarmonic

/-! # Actual reflection symmetry and half-ball excess energy -/
noncomputable section
set_option maxHeartbeats 2500000
set_option maxSynthPendingDepth 1000
open MeasureTheory Set Filter
open scoped Topology ContDiff BigOperators ENNReal
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.Letwin GaussianTilt.MomentMapElliptic
variable {n : ℕ}

lemma euclidean_coordinate_ae_ne_zero (j : Fin n) : ∀ᵐ x : KernelSpace n ∂volume, x j ≠ 0 := by
  have hμ : MeasurePreserving (dirichletCoordinateEquiv n) volume volume := PiLp.volume_preserving_ofLp (Fin n)
  exact hμ.quasiMeasurePreserving.ae (Measure.ae_eval_ne (fun _ : Fin n => (volume : Measure ℝ)) j 0)

lemma integral_even_on_ball_eq_two_upper (j : Fin n) {R : ℝ} {f : KernelSpace n → ℝ}
    (hi : IntegrableOn f (Metric.ball (0:KernelSpace n) R) volume)
    (heven : ∀ x ∈ Metric.ball (0:KernelSpace n) R, f (flatReflection j x)=f x) :
    (∫ x in Metric.ball (0:KernelSpace n) R, f x)=2*(∫ x in upperCampanatoBall j 0 R, f x) := by
  let b := (Metric.ball (0:KernelSpace n) R).indicator f
  let g := (upperCampanatoBall j 0 R).indicator f
  have hgi : Integrable g volume := (hi.mono_set inter_subset_left).integrable_indicator (isOpen_upperCampanatoBall j 0 R).measurableSet
  have hgTi : Integrable (fun x => g (flatReflection j x)) volume :=
    ((flatReflection j).measurePreserving.integrable_comp hgi.aestronglyMeasurable).mpr hgi
  have hsame (x : KernelSpace n) : flatReflection j x ∈ Metric.ball (0:KernelSpace n) R ↔ x ∈ Metric.ball 0 R := by
    simp only [Metric.mem_ball,dist_zero_right,LinearIsometryEquiv.norm_map]
  have he : b =ᵐ[volume] (fun x => g x+g (flatReflection j x)) := by
    filter_upwards [euclidean_coordinate_ae_ne_zero j] with x hxj
    by_cases hx : x ∈ Metric.ball (0:KernelSpace n) R
    · have hTx := (hsame x).mpr hx
      by_cases hp : 0 < x j
      · have hTn : flatReflection j x ∉ upperCampanatoBall j 0 R := by
          intro h
          have hh := h.2
          change 0 < flatReflection j x j at hh
          rw [flatReflection_apply,if_pos rfl] at hh
          linarith
        rw [show b x=f x from indicator_of_mem hx _,show g x=f x from indicator_of_mem (show x ∈ upperCampanatoBall j 0 R from ⟨hx,hp⟩) _,
          show g (flatReflection j x)=0 from indicator_of_notMem hTn _,add_zero]
      · have hn : x j < 0 := lt_of_le_of_ne (le_of_not_gt hp) hxj
        have hxnot : x ∉ upperCampanatoBall j 0 R := fun h => hp h.2
        have hTp : flatReflection j x ∈ upperCampanatoBall j 0 R :=
          ⟨hTx,by change 0 < flatReflection j x j; rw [flatReflection_apply,if_pos rfl]; linarith⟩
        rw [show b x=f x from indicator_of_mem hx _,show g x=0 from indicator_of_notMem hxnot _,
          show g (flatReflection j x)=f (flatReflection j x) from indicator_of_mem hTp _,zero_add,heven x hx]
    · have hTx : flatReflection j x ∉ Metric.ball (0:KernelSpace n) R := fun h => hx ((hsame x).mp h)
      rw [show b x=0 from indicator_of_notMem hx _,
        show g x=0 from indicator_of_notMem (fun h => hx h.1) _,
        show g (flatReflection j x)=0 from indicator_of_notMem (fun h => hTx h.1) _,add_zero]
  rw [← integral_indicator Metric.isOpen_ball.measurableSet]
  change (∫ x, b x)=_
  rw [integral_congr_ae he,integral_add hgi hgTi,
    (flatReflection j).measurePreserving.integral_comp (flatReflection j).toHomeomorph.measurableEmbedding]
  rw [show (∫ x, g x)=∫ x in upperCampanatoBall j 0 R, f x from integral_indicator (isOpen_upperCampanatoBall j 0 R).measurableSet]
  ring

lemma reflected_vector_excess_even (j : Fin n) {H : KernelSpace n → KernelSpace n} {R : ℝ}
    (hpar : ∀ i x, x ∈ Metric.ball (0:KernelSpace n) R → H (flatReflection j x) i=-flatReflectionSign j i*H x i)
    {q : KernelSpace n} (hq : ∀ i, i ≠ j → q i=0) :
    ∀ x ∈ Metric.ball (0:KernelSpace n) R, ‖H (flatReflection j x)-q‖^2=‖H x-q‖^2 := by
  intro x hx
  rw [euclidean_norm_sub_sq,euclidean_norm_sub_sq]
  apply Finset.sum_congr rfl
  intro i _
  rw [hpar i x hx]
  by_cases hij : i=j
  · simp [flatReflectionSign,hij]
  · rw [hq i hij]
    simp [flatReflectionSign,hij]

/-- True reflected harmonic fields yield the normal-constant half-ball
excess decay. The normal vector is their actual value at the center. -/
theorem exists_reflected_harmonic_L2_excess_decay [NeZero n] :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : Fin n) (H : KernelSpace n → KernelSpace n),
      (∀ i, MemLp (fun x => H x i) 2 volume) → ∀ R : ℝ, 0 < R →
      (∀ i x, x ∈ Metric.ball (0:KernelSpace n) R → ContDiffAt ℝ ∞ (fun y => H y i) x) →
      (∀ i x, x ∈ Metric.ball (0:KernelSpace n) R → kernelLaplacian (fun y => H y i) x=0) →
      (∀ i x, x ∈ Metric.ball (0:KernelSpace n) R → H (flatReflection j x) i=-flatReflectionSign j i*H x i) →
      (∀ i, i ≠ j → H 0 i=0) ∧ ∀ q : KernelSpace n, (∀ i, i ≠ j → q i=0) →
      ∀ r : ℝ, 0 < r → r ≤ R/2 →
        (∫ x in upperCampanatoBall j 0 r, ‖H x-H 0‖^2) ≤
          C*(r/R)^(n+2)*(∫ x in upperCampanatoBall j 0 R, ‖H x-q‖^2) := by
  obtain ⟨C,hC,hdec⟩ := exists_harmonic_vector_L2_excess_decay (n := n)
  refine ⟨2*C,by positivity,?_⟩
  intro j H hH R hR hs hhar hpar
  refine ⟨?_,?_⟩
  · intro i hij
    have hh := hpar i 0 (Metric.mem_ball_self hR)
    simp only [map_zero,flatReflectionSign,if_neg hij,neg_mul,one_mul] at hh
    linarith
  · intro q hq r hr hrR
    have hb := hdec H hH 0 R hR hs hhar q r hr hrR
    rw [integral_even_on_ball_eq_two_upper j (integrableOn_euclidean_excess_of_coordinate_memLp hH q 0 R)
      (reflected_vector_excess_even j hpar hq)] at hb
    have hmono : (∫ x in upperCampanatoBall j 0 r, ‖H x-H 0‖^2) ≤
        ∫ x in Metric.ball (0:KernelSpace n) r, ‖H x-H 0‖^2 :=
      setIntegral_mono_set (integrableOn_euclidean_excess_of_coordinate_memLp hH (H 0) 0 r)
        (ae_of_all _ (fun _ => sq_nonneg _)) (ae_of_all _ (fun _ hx => hx.1))
    exact hmono.trans (hb.trans_eq (by ring))

end GaussianTilt.MomentMapLinearDirichlet
