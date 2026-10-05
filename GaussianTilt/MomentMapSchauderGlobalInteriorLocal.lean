import GaussianTilt.MomentMapSchauderInteriorJetEstimate
import GaussianTilt.MomentMapSchauderUniformEllipticity

/-! # Uniform interior patches for a compact coefficient family -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 2400000
open Set Filter Matrix
open scoped Topology ContDiff
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic GaussianTilt.HolderSpace
variable {n : ℕ}

theorem exists_body_interior_local_estimate [NeZero n]
    {I : Type*} [TopologicalSpace I] {P : Set I} (hP : IsCompact P)
    {S : Set (KernelSpace n)} (hS : Convex ℝ S) (hSc : IsClosed S)
    {α K : ℝ} (hα : 0 < α) (hα1 : α < 1) (hK : 0 ≤ K)
    (a : KernelSpace n) (ha : a ∈ interior S)
    (A : I → KernelSpace n → Matrix (Fin n) (Fin n) ℝ)
    (hAt : ContinuousOn (fun t => A t a) P) (hA0 : ∀ t ∈ P, (A t a).PosDef)
    (hAs : ∀ t ∈ P, ∀ x ∈ S, (A t x).IsSymm)
    (hAH : ∀ t ∈ P, ∀ x ∈ S, ∀ y ∈ S, ∀ i k, |A t x i k-A t y i k| ≤ K*‖x-y‖^α) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ t ∈ P, ∀ J : Jet (KernelSpace n) ℝ hS α,
      ∀ (f : KernelSpace n → ℝ) (U F H : ℝ), 0 ≤ U → 0 ≤ F → 0 ≤ H →
      (∀ x : S, |value S ℝ α (jetValue (KernelSpace n) ℝ hS α J) x| ≤ U) →
      (∀ x ∈ S, |f x| ≤ F) →
      (∀ x ∈ S, ∀ y ∈ S, |f x-f y| ≤ H*‖x-y‖^α) →
      (∀ x ∈ interior S, euclideanEllipticOperator (A t x)
        (extendValue α (jetValue (KernelSpace n) ℝ hS α J)) x=f x) →
      (∀ x ∈ S ∩ Metric.ball a r,
        ‖extendValue α (jetSecond (KernelSpace n) ℝ hS α J) x‖ ≤ C*(U+F+H)+ε*‖J‖) ∧
      (∀ x ∈ S ∩ Metric.ball a r, ∀ y ∈ S ∩ Metric.ball a r,
        ‖extendValue α (jetSecond (KernelSpace n) ℝ hS α J) x-
          extendValue α (jetSecond (KernelSpace n) ℝ hS α J) y‖ ≤
            (C*(U+F+H)+ε*‖J‖)*‖x-y‖^α) := by
  obtain ⟨q,hq,hball⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds ha)
  let R := q/8
  have hR : 0 < R := by dsimp [R]; positivity
  have hbigI : Metric.closedBall a (4*R) ⊆ interior S :=
    (Metric.closedBall_subset_ball (by dsimp [R]; linarith : 4*R < q)).trans hball
  have hRI : Metric.closedBall a R ⊆ interior S :=
    (Metric.closedBall_subset_closedBall (by linarith : R ≤ 4*R)).trans hbigI
  have hRS : Metric.closedBall a R ⊆ S := hRI.trans interior_subset
  obtain ⟨lam,Λ,hlam,hΛ,hell⟩ := exists_uniform_ellipticity_on_compact hP hAt hA0
  obtain ⟨r,hr,hrR,hbase⟩ := exists_interior_jet_estimate_small_highest (n := n)
    hα hα1 hK hR hlam hΛ.le (L0 := 0) (L1 := 0) le_rfl le_rfl
  refine ⟨r,hr,?_⟩
  intro ε hε
  obtain ⟨C,hC,hest⟩ := hbase ε hε
  refine ⟨C,hC,?_⟩
  intro t ht J f U F H hU hF hH hu hf hfH heq
  have hEq : ∀ x ∈ Metric.closedBall a R,
      matrixContraction (A t x) (bilinearEntryMatrix (extendValue α (jetSecond (KernelSpace n) ℝ hS α J) x))+
        extendValue α (jetFirst (KernelSpace n) ℝ hS α J) x (0 : KernelSpace n)=f x := by
    intro x hx
    simp only [map_zero,add_zero]
    rw [← jet_second_eq_fderiv_fderiv hS hα J (hRI hx)]
    exact heq x (hRI hx)
  obtain ⟨hb,hHh⟩ := hest S hS hSc ⟨a,ha⟩ a (hbigI.trans interior_subset) J (A t) (fun _ => 0) f
    (hA0 t ht) (fun v => (hell t ht v).1) (fun v => (hell t ht v).2)
    (fun x hx => hAs t ht x (hRS hx))
    (fun x hx y hy i k => hAH t ht x (hRS hx) y (hRS hy) i k)
    (fun _ _ => by simp) (fun _ _ _ _ => by simp) hEq U F H hU hF hH hu
    (fun x hx => hf x (hRS hx)) (fun x hx y hy => hfH x (hRS hx) y (hRS hy))
  have hsmall : C*(U+F+H)+ε*‖jetSecond (KernelSpace n) ℝ hS α J‖ ≤ C*(U+F+H)+ε*‖J‖ :=
    add_le_add_left (mul_le_mul_of_nonneg_left (norm_jetSecond_le hS α J) hε.le) _
  exact ⟨fun x hx => (hb x hx.2).trans hsmall,
    fun x hx y hy => (hHh x hx.2 y hy.2).trans (mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg (norm_nonneg _) α))⟩

end GaussianTilt.MomentMapSchauder
