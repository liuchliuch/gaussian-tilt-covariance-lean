import GaussianTilt.MomentMapSchauderInteriorJetLower
import GaussianTilt.MomentMapSchauderInteriorJetCoefficient

/-! # Direct interior closed-jet Schauder estimate with independent small highest term -/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 3000000
open Set Filter Matrix
open scoped Topology ContDiff
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic GaussianTilt.HolderSpace
variable {n : ℕ}

/-- An arbitrary genuine closed C²,α jet satisfies the local interior
elliptic estimate, including a Hölder first-order drift. No global C²
extension or unproved local regularity assertion is assumed. The radius
is fixed before δ, and the highest-norm coefficient is exactly δ. -/
theorem exists_interior_jet_estimate_small_highest [NeZero n]
    {α K R lam Λ L0 L1 : ℝ} (hα : 0 < α) (hα1 : α < 1) (hK : 0 ≤ K) (hR : 0 < R)
    (hlam : 0 < lam) (hΛ : 0 ≤ Λ) (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1) :
    ∃ r : ℝ, 0 < r ∧ 4*r ≤ R ∧ ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 < C ∧
      ∀ (S : Set (KernelSpace n)) (hS : Convex ℝ S), IsClosed S → (interior S).Nonempty →
      ∀ a : KernelSpace n, Metric.closedBall a (4*R) ⊆ S →
      ∀ J : Jet (KernelSpace n) ℝ hS α,
      let u := extendValue α (jetValue (KernelSpace n) ℝ hS α J)
      let D := extendValue α (jetFirst (KernelSpace n) ℝ hS α J)
      let B := extendValue α (jetSecond (KernelSpace n) ℝ hS α J)
      ∀ (A : KernelSpace n → Matrix (Fin n) (Fin n) ℝ) (b : KernelSpace n → KernelSpace n) (f : KernelSpace n → ℝ),
      (A a).PosDef →
      (∀ v : KernelSpace n, lam*‖v‖^2 ≤ euclideanQuadratic (A a) v) →
      (∀ v : KernelSpace n, euclideanQuadratic (A a) v ≤ Λ*‖v‖^2) →
      (∀ x ∈ Metric.closedBall a R, (A x).IsSymm) →
      (∀ x ∈ Metric.closedBall a R, ∀ y ∈ Metric.closedBall a R, ∀ i k, |A x i k-A y i k| ≤ K*‖x-y‖^α) →
      (∀ x ∈ Metric.closedBall a R, ‖b x‖ ≤ L0) →
      (∀ x ∈ Metric.closedBall a R, ∀ y ∈ Metric.closedBall a R, ‖b x-b y‖ ≤ L1*‖x-y‖^α) →
      (∀ x ∈ Metric.closedBall a R, matrixContraction (A x) (bilinearEntryMatrix (B x))+D x (b x)=f x) →
      ∀ U F H : ℝ, 0 ≤ U → 0 ≤ F → 0 ≤ H →
      (∀ x : S, |value S ℝ α (jetValue (KernelSpace n) ℝ hS α J) x| ≤ U) →
      (∀ x ∈ Metric.closedBall a R, |f x| ≤ F) →
      (∀ x ∈ Metric.closedBall a R, ∀ y ∈ Metric.closedBall a R, |f x-f y| ≤ H*‖x-y‖^α) →
      (∀ x ∈ Metric.ball a r, ‖B x‖ ≤ C*(U+F+H)+δ*‖jetSecond (KernelSpace n) ℝ hS α J‖) ∧
      (∀ x ∈ Metric.ball a r, ∀ y ∈ Metric.ball a r,
        ‖B x-B y‖ ≤ (C*(U+F+H)+δ*‖jetSecond (KernelSpace n) ℝ hS α J‖)*‖x-y‖^α) := by
  obtain ⟨r,C0,hr,hrR,hC0,hbase⟩ := exists_interior_first_jet_schauder (n := n) hα hα1 hlam hΛ hK hΛ hR
  refine ⟨r,hr,hrR,?_⟩
  intro δ hδ
  let Z := 3+2*L0+L1
  have hZ : 0 < Z := by dsimp [Z]; positivity
  let η := δ/(Z*C0)
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨L,hL,hinterp⟩ := interior_jet_lower_holder_small_highest (n := n)
    (show 0 < 4*R by positivity) hα hα1.le hη
  let C := C0*(1+Z*L)+1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro S hS hSc hint a hball J
  dsimp only
  intro A b f hA0 hlower hupper hAs hAH hbB hbH heq U F H hU hF hH huB hfB hfH
  let u := extendValue α (jetValue (KernelSpace n) ℝ hS α J)
  let D := extendValue α (jetFirst (KernelSpace n) ℝ hS α J)
  let B := extendValue α (jetSecond (KernelSpace n) ℝ hS α J)
  let Q := ‖jetSecond (KernelSpace n) ℝ hS α J‖
  have hQ : 0 ≤ Q := norm_nonneg _
  let V := L*U+η*Q
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hballInt : Metric.ball a (4*R) ⊆ interior S :=
    Metric.isOpen_ball.subset_interior_iff.mpr (Metric.ball_subset_closedBall.trans hball)
  have hsubR : Metric.closedBall a R ⊆ S := (Metric.closedBall_subset_closedBall (by linarith : R ≤ 4*R)).trans hball
  have hRint : Metric.closedBall a R ⊆ interior S :=
    (Metric.closedBall_subset_ball (by linarith : R < 4*R)).trans hballInt
  have huC2 : ContDiffOn ℝ 2 u (interior S) := jet_contDiffOn_two hS hα J
  obtain ⟨v,hv,_,hvu⟩ := exists_global_contDiff_patch isOpen_interior 2 huC2 a
    (r := 2*R) (R := 3*R) (by positivity) (by linarith)
    ((Metric.ball_subset_ball (by linarith : 3*R ≤ 4*R)).trans hballInt)
  have heN : ∀ x ∈ Metric.ball a (2*R), v =ᶠ[𝓝 x] u :=
    fun x hx => eventually_of_mem (Metric.isOpen_ball.mem_nhds hx) (fun y hy => hvu hy)
  have hsubR2 : Metric.closedBall a R ⊆ Metric.ball a (2*R) := Metric.closedBall_subset_ball (by linarith)
  have hvD : ∀ x ∈ Metric.closedBall a R, fderiv ℝ v x=D x := by
    intro x hx
    rw [(heN x (hsubR2 hx)).fderiv_eq]
    exact (jet_hasFDerivAt hS hα J (hRint hx)).fderiv
  have hvB : ∀ x ∈ Metric.closedBall a R, fderiv ℝ (fderiv ℝ v) x=B x := by
    intro x hx
    rw [(heN x (hsubR2 hx)).fderiv.fderiv_eq]
    exact jet_second_eq_fderiv_fderiv hS hα J (hRint hx)
  have hlow := hinterp S hS hSc hint a hball J U hU huB
  dsimp only at hlow
  have hlowR : Metric.closedBall a R ⊆ Metric.closedBall a (4*R/2) := Metric.closedBall_subset_closedBall (by linarith)
  have hDB : ∀ x ∈ Metric.closedBall a R, ‖D x‖ ≤ V := fun x hx => (hlow.1 x (hlowR hx)).1
  have hDH : ∀ x ∈ Metric.closedBall a R, ∀ y ∈ Metric.closedBall a R, ‖D x-D y‖ ≤ V*‖x-y‖^α :=
    fun x hx y hy => hlow.2.2 x (hlowR hx) y (hlowR hy)
  have hub : ∀ x ∈ Metric.closedBall a R, |v x| ≤ U := by
    intro x hx
    rw [(heN x (hsubR2 hx)).self_of_nhds]
    rw [show u x=value S ℝ α (jetValue (KernelSpace n) ℝ hS α J) ⟨x,hsubR hx⟩ from extendValue_mem α _ (hsubR hx)]
    exact huB ⟨x,hsubR hx⟩
  have huH : ∀ x ∈ Metric.closedBall a R, ∀ y ∈ Metric.closedBall a R, |v x-v y| ≤ V*‖x-y‖^α := by
    intro x hx y hy
    rw [(heN x (hsubR2 hx)).self_of_nhds,(heN y (hsubR2 hy)).self_of_nhds]
    exact hlow.2.1 x (hlowR hx) y (hlowR hy)
  have hBs : ∀ x ∈ Metric.closedBall a R, ‖B x‖ ≤ Q := by
    intro x hx
    rw [show B x=value S _ α (jetSecond (KernelSpace n) ℝ hS α J) ⟨x,hsubR hx⟩ from extendValue_mem α _ (hsubR hx)]
    exact norm_value_apply_le S _ α _ _
  have hBH : ∀ x ∈ Metric.closedBall a R, ∀ y ∈ Metric.closedBall a R, ‖B x-B y‖ ≤ Q*‖x-y‖^α := by
    intro x hx y hy
    rw [show B x=value S _ α (jetSecond (KernelSpace n) ℝ hS α J) ⟨x,hsubR hx⟩ from extendValue_mem α _ (hsubR hx),
      show B y=value S _ α (jetSecond (KernelSpace n) ℝ hS α J) ⟨y,hsubR hy⟩ from extendValue_mem α _ (hsubR hy)]
    exact norm_value_sub_le S _ α _ _ _
  let g := fun x => f x-D x (b x)
  have hgeq : ∀ x ∈ Metric.closedBall a R, euclideanEllipticOperator (A x) v x=g x := by
    intro x hx
    have hb : euclideanEllipticOperator (A x) v x=matrixContraction (A x) (bilinearEntryMatrix (B x)) := by
      unfold euclideanEllipticOperator matrixContraction bilinearEntryMatrix
      rw [hvB x hx]
    rw [hb]
    have hh := heq x hx
    dsimp [g]
    linarith
  have hgB : ∀ x ∈ Metric.closedBall a R, |g x| ≤ F+V*L0 := by
    intro x hx
    apply (abs_sub _ _).trans
    have hh : |D x (b x)| ≤ V*L0 := by
      have ht := (D x).le_opNorm (b x)
      rw [Real.norm_eq_abs] at ht
      exact ht.trans (mul_le_mul (hDB x hx) (hbB x hx) (norm_nonneg _) hV)
    exact add_le_add (hfB x hx) hh
  have hgH : ∀ x ∈ Metric.closedBall a R, ∀ y ∈ Metric.closedBall a R, |g x-g y| ≤ (H+V*L1+V*L0)*‖x-y‖^α := by
    intro x hx y hy
    have hh := holder_clm_apply_bound hV hL0 hV hL1 hDB hbB hDH hbH x hx y hy
    rw [Real.norm_eq_abs] at hh
    have he : g x-g y=(f x-f y)-(D x (b x)-D y (b y)) := by dsimp [g]; ring
    rw [he]
    exact (abs_sub _ _).trans ((add_le_add (hfH x hx y hy) hh).trans_eq (by ring))
  obtain ⟨hvs,hvH⟩ := hbase a A hA0 hlower hupper (abs_coefficient_entry_le_upper hA0 hΛ hupper) hAs hAH v g hv
    U V Q V V Q (F+V*L0) (H+V*L1+V*L0) hU hV hQ hV hV hQ (by positivity) (by positivity)
    hub (fun x hx => by rw [hvD x hx]; exact hDB x hx) (fun x hx => by rw [hvB x hx]; exact hBs x hx)
    huH (fun x hx y hy => by rw [hvD x hx,hvD y hy]; exact hDH x hx y hy)
    (fun x hx y hy => by rw [hvB x hx,hvB y hy]; exact hBH x hx y hy) hgB hgH hgeq
  have hηeq : Z*C0*η=δ := by dsimp [η]; field_simp
  have htotal : C0*(U+V+V+V+(F+V*L0)+(H+V*L1+V*L0)) ≤ C*(U+F+H)+δ*Q := by
    have he : C0*(U+V+V+V+(F+V*L0)+(H+V*L1+V*L0))=C0*(1+Z*L)*U+C0*(F+H)+δ*Q := by
      have hηQ := congrArg (fun z : ℝ => z*Q) hηeq
      dsimp [Z] at hηQ ⊢
      dsimp [V]
      nlinarith only [hηQ]
    rw [he]
    have hLC : C0*(1+Z*L) ≤ C := by dsimp [C]; linarith
    have hC0C : C0 ≤ C := by dsimp [C]; nlinarith [mul_nonneg (mul_nonneg hC0.le hZ.le) hL]
    have hh1 := mul_le_mul_of_nonneg_right hLC hU
    have hh2 := mul_le_mul_of_nonneg_right hC0C (add_nonneg hF hH)
    nlinarith only [hh1,hh2]
  have hsmall : Metric.ball a r ⊆ Metric.closedBall a R :=
    Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith))
  constructor
  · intro x hx
    change ‖B x‖ ≤ C*(U+F+H)+δ*Q
    rw [← hvB x (hsmall hx)]
    exact (hvs x hx).trans htotal
  · intro x hx y hy
    change ‖B x-B y‖ ≤ (C*(U+F+H)+δ*Q)*‖x-y‖^α
    rw [← hvB x (hsmall hx),← hvB y (hsmall hy)]
    exact (hvH x hx y hy).trans (mul_le_mul_of_nonneg_right htotal (Real.rpow_nonneg (norm_nonneg _) α))

end GaussianTilt.MomentMapSchauder
