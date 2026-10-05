import GaussianTilt.MomentMapBoundaryRegularitySlopeContraction

/-! # Actual flat elliptic systems and their scale covariance -/
noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin
variable {n : ℕ}

/-- Only the actual equation and quantitative lower-order data are stored.
There is no regularity or oscillation estimate among these fields. -/
structure FlatEllipticSystem (j : Fin n) (u f : CoordinateSpace n → ℝ)
    (A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ) (lam Λ K M : ℝ) : Prop where
  smooth : ContDiff ℝ ∞ u
  forcing_diff : Differentiable ℝ f
  coefficient_diff : ∀ i k, Differentiable ℝ (fun y => A y i k)
  positive : ∀ y ∈ flatHalfBall j, (A y).PosDef
  elliptic : ∀ y ∈ flatHalfBall j, ∀ w : CoordinateSpace n,
    lam*‖(coordinateEquiv n).symm w‖^2 ≤ w ⬝ᵥ (A y *ᵥ w) ∧
    w ⬝ᵥ (A y *ᵥ w) ≤ Λ*‖(coordinateEquiv n).symm w‖^2
  coefficient_bound : ∀ y ∈ flatHalfBall j, ∀ k a b,
    y j*|matrixCoordinateDerivative A k y a b| ≤ K
  forcing_bound : ∀ y ∈ flatHalfBall j, |f y| ≤ M
  forcing_derivative_bound : ∀ y ∈ flatHalfBall j, ∀ k,
    y j*|coordinateDerivative k f y| ≤ M
  equation : ∀ y ∈ flatHalfBall j, linearizedMA (A y) u y = f y

def flatRescaledSolution (u : CoordinateSpace n → ℝ) (r : ℝ) (x : CoordinateSpace n) : ℝ :=
  r⁻¹*u (r • x)

def flatRescaledForcing (f : CoordinateSpace n → ℝ) (r : ℝ) (x : CoordinateSpace n) : ℝ :=
  r*f (r • x)

lemma coordinateDerivative_dilation {v : CoordinateSpace n → ℝ} (hv : Differentiable ℝ v)
    (r : ℝ) (k : Fin n) (x : CoordinateSpace n) :
    coordinateDerivative k (fun y => v (r • y)) x = r*coordinateDerivative k v (r • x) := by
  simpa only [ellipticRescalePoint,zero_add] using coordinateDerivative_ellipticRescale hv 0 r k x

lemma norm_coordinate_dilation (r : ℝ) (x : CoordinateSpace n) :
    ‖(coordinateEquiv n).symm (r • x)‖ = |r| *‖(coordinateEquiv n).symm x‖ := by
  rw [map_smul,norm_smul,Real.norm_eq_abs]

lemma FlatEllipticSystem.rescale {j : Fin n} {u f : CoordinateSpace n → ℝ}
    {A : CoordinateSpace n → Matrix (Fin n) (Fin n) ℝ} {lam Λ K M r : ℝ}
    (h : FlatEllipticSystem j u f A lam Λ K M) (hr : 0 < r) (hr1 : r ≤ 1) :
    FlatEllipticSystem j (flatRescaledSolution u r) (flatRescaledForcing f r)
      (fun y => A (r • y)) lam Λ K (r*M) := by
  have hscale : ContDiff ℝ ∞ (fun y : CoordinateSpace n => r • y) := contDiff_const.smul contDiff_id
  have hs (y : CoordinateSpace n) (hy : y ∈ flatHalfBall j) : r • y ∈ flatHalfBall j := by
    constructor
    · rw [norm_coordinate_dilation,abs_of_pos hr]
      have hh := mul_lt_mul_of_pos_left hy.1 hr
      nlinarith
    · change 0 < r*y j
      exact mul_pos hr hy.2
  refine ⟨contDiff_const.mul (h.smooth.comp hscale),
    (h.forcing_diff.comp (hscale.differentiable (by simp))).const_mul _,
    fun i k => (h.coefficient_diff i k).comp (hscale.differentiable (by simp)),
    fun y hy => h.positive (r • y) (hs y hy), fun y hy => h.elliptic (r • y) (hs y hy), ?_, ?_, ?_, ?_⟩
  · intro y hy k a b
    change y j*|coordinateDerivative k (fun z => A (r • z) a b) y| ≤ K
    rw [coordinateDerivative_dilation (h.coefficient_diff a b),abs_mul,abs_of_pos hr]
    have hh := h.coefficient_bound (r • y) (hs y hy) k a b
    change (r*y j)*|coordinateDerivative k (fun z => A z a b) (r • y)| ≤ K at hh
    nlinarith
  · intro y hy
    change |r*f (r • y)| ≤ r*M
    rw [abs_mul,abs_of_pos hr]
    exact mul_le_mul_of_nonneg_left (h.forcing_bound (r • y) (hs y hy)) hr.le
  · intro y hy k
    have hd : Differentiable ℝ (fun y => f (r • y)) := h.forcing_diff.comp (hscale.differentiable (by simp))
    change y j*|coordinateDerivative k (fun z => r*f (r • z)) y| ≤ r*M
    rw [coordinateDerivative_const_mul hd,coordinateDerivative_dilation h.forcing_diff,
      abs_mul,abs_mul,abs_of_pos hr]
    have hh := mul_le_mul_of_nonneg_left (h.forcing_derivative_bound (r • y) (hs y hy) k) hr.le
    change r*((r*y j)*|coordinateDerivative k f (r • y)|) ≤ r*M at hh
    nlinarith
  · intro y hy
    have hup : ContDiffAt ℝ 2 (fun z => u (r • z)) y :=
      (contDiff_infty.mp (h.smooth.comp hscale) 2).contDiffAt
    change linearizedMA (A (r • y)) (fun z => r⁻¹*u (r • z)) y = r*f (r • y)
    rw [linearizedMA_const_mul_at _ hup]
    have hl := linearizedMA_ellipticRescale h.smooth (A (r • y)) 0 r y
    simp only [ellipticRescalePoint,zero_add] at hl
    rw [hl,h.equation (r • y) (hs y hy)]
    field_simp

end GaussianTilt.MomentMapRegularity
