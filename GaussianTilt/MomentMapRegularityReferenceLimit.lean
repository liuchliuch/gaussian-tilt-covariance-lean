import GaussianTilt.MomentMapRegularityReferenceClassicalMeasure
import GaussianTilt.MomentMapRegularityReferenceC2Equation
import GaussianTilt.MomentMapClassicalDirichletDomainLimit
import GaussianTilt.MomentMapCampanatoLocalEndpoint

/-! # Actual quadratic-jet transfer from inner classical reference solutions

The varying-domain comparison theorem supplies uniform convergence. Actual
Pogorelov--Calabi/Taylor estimates then construct geometric quadratic
approximations of the weak reference, without presupposing its derivatives.
Classical solvability itself is still a separate theorem under construction.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Gradient
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

def referenceLimitConstant (n : ℕ) (r R : ℝ) : ℝ :=
  (referenceTaylorConstant n r R+1)*(r/4)^3

/-- Construct all geometric quadratic approximations from the actual
classical references on the constructed nested domains. -/
theorem geometric_quadratic_approximations_of_classical_inner_references [NeZero n]
    {S : Set (E n)} (hS : IsCompact S) (hSn : S.Nonempty)
    {u : E n → ℝ} (huc : Continuous u) (hucv : ConvexOn ℝ S u)
    (hub : ∀ x ∈ frontier S, u x = 0)
    (huid : ∀ A, IsCompact A → A ⊆ interior S → volume (subgradientImageOn S u A) = volume A)
    (d : ℕ → SmoothInnerDomain S ∅)
    (hex : ∀ A, IsCompact A → A ⊆ interior S → ∀ᶠ m in atTop, A ⊆ (d m).domain)
    (v : ℕ → E n → ℝ) (hvc : ∀ m, Continuous (v m))
    (hvs : ∀ m, ContDiffOn ℝ ∞ (v m) (interior (d m).body))
    (hvv : ∀ m, ConvexOn ℝ (d m).body (v m))
    (hvb : ∀ m, ∀ x ∈ frontier (d m).body, v m x = 0)
    (hvH : ∀ m, ∀ x ∈ interior (d m).body,
      (coordinateHessian (coordinatePullback (v m)) (coordinateEquiv n x)).PosDef)
    (hvMA : ∀ m, ∀ x ∈ interior (d m).body,
      (coordinateHessian (coordinatePullback (v m)) (coordinateEquiv n x)).det = 1)
    {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hSR : S ⊆ Metric.closedBall 0 R)
    (hrS : Metric.closedBall (0 : E n) r ⊆ interior S) :
    ∀ x ∈ Metric.ball (0 : E n) (r/4), ∃ a : ℕ → ℝ, ∃ p : ℕ → E n,
      ∃ H : ℕ → E n →L[ℝ] E n,
      (∀ k z w, inner ℝ (H k z) w = inner ℝ z (H k w)) ∧
      ∀ k, ∀ h : E n, ‖h‖ ≤ (r/4)*(1/2 : ℝ)^k →
        |u (x+h)-quadraticJet (a k) (p k) 0 (H k) h| ≤
          referenceLimitConstant n r R * ((1/2 : ℝ)^2*(1/2 : ℝ))^k := by
  classical
  have hvid (m : ℕ) (A : Set (E n)) (hA : IsCompact A) (hAS : A ⊆ interior (d m).body) :
      volume (subgradientImageOn (d m).body (v m) A) = volume A :=
    subgradientImageOn_volume_eq_of_interior_classical_unit_det (contDiffOn_infty.mp (hvs m) 2)
      (hvv m) hA.measurableSet hAS (hvH m) (fun x hx => hvMA m x (hAS hx))
  have hlim := unit_density_dirichlet_tendstoUniformlyOn_inner_domains hS hSn huc hucv hub huid d hex
    (fun m => (hvc m).continuousOn) hvb hvid
  have hgood : ∀ᶠ m in atTop, Metric.closedBall (0 : E n) r ⊆ (d m).domain :=
    hex _ (isCompact_closedBall _ _) hrS
  let eps := fun k : ℕ => (r/4)^3*(1/8 : ℝ)^k
  have heps (k : ℕ) : 0 < eps k := by dsimp [eps]; positivity
  have hchoose (k : ℕ) : ∃ m : ℕ,
      (Metric.closedBall (0 : E n) r ⊆ (d m).domain) ∧
      ∀ y ∈ S, |u y-(d m).body.indicator (v m) y| < eps k := by
    have hevent := Metric.tendstoUniformlyOn_iff.mp hlim (eps k) (heps k)
    obtain ⟨m,hm,happrox⟩ := (hgood.and hevent).exists
    exact ⟨m,hm,fun y hy => by simpa only [Real.dist_eq] using happrox y hy⟩
  choose m hm happrox using hchoose
  intro x hx
  have hxnorm : ‖x‖ < r/4 := by simpa using hx
  have hxp : x ∈ Metric.closedBall (0 : E n) (r/4) := Metric.ball_subset_closedBall hx
  have hTaylor (k : ℕ) : ∃ p : E n, ∃ H : E n →L[ℝ] E n,
      (∀ z w, inner ℝ (H z) w = inner ℝ z (H w)) ∧
      ∀ h : E n, ‖h‖ ≤ r/4 →
        |v (m k) (x+h)-quadraticJet (v (m k) x) p 0 H h| ≤ referenceTaylorConstant n r R * ‖h‖^3 := by
    apply smooth_reference_quadratic_approximation (S := (d (m k)).body) (hvc (m k)) (d (m k)).compact_sublevel
      (hvs (m k)) (hvv (m k)) (hvb (m k)) (hvid (m k)) (hvH (m k)) (hvMA (m k)) hr hR
      ((d (m k)).sublevel_inside.trans (interior_subset.trans hSR))
    · simpa only [(d (m k)).interior_body] using hm k
    · exact hxp
  choose p H hH hT using hTaylor
  refine ⟨fun k => v (m k) x,p,H,hH,?_⟩
  intro k h hh
  have hpow : (1/2 : ℝ)^k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hnorm : ‖h‖ ≤ r/4 := hh.trans (mul_le_of_le_one_right (by positivity) hpow)
  have hsum : x+h ∈ Metric.closedBall (0 : E n) r := by
    rw [Metric.mem_closedBall,dist_zero_right]
    exact (norm_add_le _ _).trans (by linarith)
  have hyS : x+h ∈ S := interior_subset (hrS hsum)
  have hym : x+h ∈ (d (m k)).body := by
    have hy := hm k hsum
    exact (show (d (m k)).defining (x+h) ≤ 0 from le_of_lt hy)
  have herror : |u (x+h)-v (m k) (x+h)| ≤ eps k := by
    have hh := happrox k (x+h) hyS
    rw [indicator_of_mem hym] at hh
    exact hh.le
  have hcube : ‖h‖^3 ≤ eps k := by
    have hc := pow_le_pow_left₀ (norm_nonneg h) hh 3
    calc
      _ ≤ ((r/4)*(1/2 : ℝ)^k)^3 := hc
      _ = eps k := by
        dsimp [eps]
        rw [mul_pow,← pow_mul, Nat.mul_comm k 3, pow_mul]
        norm_num
  calc
    |u (x+h)-quadraticJet (v (m k) x) (p k) 0 (H k) h| ≤
        |u (x+h)-v (m k) (x+h)| + |v (m k) (x+h)-quadraticJet (v (m k) x) (p k) 0 (H k) h| :=
      abs_sub_le _ _ _
    _ ≤ eps k + referenceTaylorConstant n r R * ‖h‖^3 := add_le_add herror (hT k h hnorm)
    _ ≤ eps k + referenceTaylorConstant n r R * eps k := add_le_add_left
      (mul_le_mul_of_nonneg_left hcube (referenceTaylorConstant_nonneg n r R)) _
    _ = referenceLimitConstant n r R * ((1/2 : ℝ)^2*(1/2 : ℝ))^k := by
      dsimp [eps,referenceLimitConstant]
      norm_num
      ring

/-- The localized Campanato endpoint derives both actual derivatives and
a uniform Hessian Lipschitz bound from the constructed approximations. -/
theorem reference_contDiffOn_two_of_classical_inner_references [NeZero n]
    {S : Set (E n)} (hS : IsCompact S) (hSn : S.Nonempty)
    {u : E n → ℝ} (huc : Continuous u) (hucv : ConvexOn ℝ S u)
    (hub : ∀ x ∈ frontier S, u x = 0)
    (huid : ∀ A, IsCompact A → A ⊆ interior S → volume (subgradientImageOn S u A) = volume A)
    (d : ℕ → SmoothInnerDomain S ∅)
    (hex : ∀ A, IsCompact A → A ⊆ interior S → ∀ᶠ m in atTop, A ⊆ (d m).domain)
    (v : ℕ → E n → ℝ) (hvc : ∀ m, Continuous (v m))
    (hvs : ∀ m, ContDiffOn ℝ ∞ (v m) (interior (d m).body))
    (hvv : ∀ m, ConvexOn ℝ (d m).body (v m))
    (hvb : ∀ m, ∀ x ∈ frontier (d m).body, v m x = 0)
    (hvH : ∀ m, ∀ x ∈ interior (d m).body,
      (coordinateHessian (coordinatePullback (v m)) (coordinateEquiv n x)).PosDef)
    (hvMA : ∀ m, ∀ x ∈ interior (d m).body,
      (coordinateHessian (coordinatePullback (v m)) (coordinateEquiv n x)).det = 1)
    {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hSR : S ⊆ Metric.closedBall 0 R)
    (hrS : Metric.closedBall (0 : E n) r ⊆ interior S) :
    ContDiffOn ℝ 2 u (Metric.ball (0 : E n) (r/4)) ∧
      ∃ H : E n → E n →L[ℝ] E n,
        (∀ x ∈ Metric.ball (0 : E n) (r/4), HasFDerivAt (gradient u) (H x) x) ∧
        ∀ x ∈ Metric.ball (0 : E n) (r/4), ∀ y ∈ Metric.ball (0 : E n) (r/4),
          2*‖x-y‖ ≤ r/4 → ‖H x-H y‖ ≤
            (36*campanatoLimitConstant (r/4) (1/2) (1/2) (referenceLimitConstant n r R))*‖x-y‖ := by
  have hC : 0 ≤ referenceLimitConstant n r R := by
    unfold referenceLimitConstant
    exact mul_nonneg (by linarith [referenceTaylorConstant_nonneg n r R]) (by positivity)
  have happ := geometric_quadratic_approximations_of_classical_inner_references hS hSn huc hucv hub huid
    d hex v hvc hvs hvv hvb hvH hvMA hr hR hSR hrS
  obtain ⟨hreg,H,hH,hholder⟩ := contDiffOn_two_of_geometric_quadratic_approximations_local
    Metric.isOpen_ball (show 0 < r/4 by positivity) (show (0:ℝ)<1/2 by norm_num)
    (show (1/2:ℝ)<1 by norm_num) (show (0:ℝ)<1/2 by norm_num)
    (show (1/2:ℝ)<1 by norm_num) hC happ
  have halpha : oscillationExponent (1/2 : ℝ) (1/2 : ℝ) = 1 := by
    unfold oscillationExponent
    exact div_self (Real.log_neg (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1)).ne
  refine ⟨hreg,H,hH,?_⟩
  intro x hx y hy hxy
  have hh := hholder x hx y hy hxy
  rw [halpha] at hh
  norm_num at hh ⊢
  convert hh using 1 <;> ring

/-- The weak reference satisfies the actual classical equation after the
constructed C² transfer; positivity and the determinant equation are derived. -/
theorem reference_C2_equation_of_classical_inner_references [NeZero n]
    {S : Set (E n)} (hS : IsCompact S) (hSn : S.Nonempty)
    {u : E n → ℝ} (huc : Continuous u) (hucv : ConvexOn ℝ S u)
    (hub : ∀ x ∈ frontier S, u x = 0)
    (huid : ∀ A, IsCompact A → A ⊆ interior S → volume (subgradientImageOn S u A) = volume A)
    (d : ℕ → SmoothInnerDomain S ∅)
    (hex : ∀ A, IsCompact A → A ⊆ interior S → ∀ᶠ m in atTop, A ⊆ (d m).domain)
    (v : ℕ → E n → ℝ) (hvc : ∀ m, Continuous (v m))
    (hvs : ∀ m, ContDiffOn ℝ ∞ (v m) (interior (d m).body))
    (hvv : ∀ m, ConvexOn ℝ (d m).body (v m))
    (hvb : ∀ m, ∀ x ∈ frontier (d m).body, v m x = 0)
    (hvH : ∀ m, ∀ x ∈ interior (d m).body,
      (coordinateHessian (coordinatePullback (v m)) (coordinateEquiv n x)).PosDef)
    (hvMA : ∀ m, ∀ x ∈ interior (d m).body,
      (coordinateHessian (coordinatePullback (v m)) (coordinateEquiv n x)).det = 1)
    {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hSR : S ⊆ Metric.closedBall 0 R)
    (hrS : Metric.closedBall (0 : E n) r ⊆ interior S) :
    ContDiffOn ℝ 2 u (Metric.ball (0 : E n) (r/4)) ∧
      ∀ x ∈ Metric.ball (0 : E n) (r/4),
        (coordinateHessian (coordinatePullback u) (coordinateEquiv n x)).PosDef ∧
        (coordinateHessian (coordinatePullback u) (coordinateEquiv n x)).det = 1 := by
  have hreg := (reference_contDiffOn_two_of_classical_inner_references hS hSn huc hucv hub huid
    d hex v hvc hvs hvv hvb hvH hvMA hr hR hSR hrS).1
  refine ⟨hreg,positive_hessian_and_unit_det_of_C2_alexandrov hucv Metric.isOpen_ball ?_ hreg huid⟩
  exact (Metric.ball_subset_closedBall.trans
    (Metric.closedBall_subset_closedBall (by linarith))).trans hrS

end GaussianTilt.MomentMapRegularity
