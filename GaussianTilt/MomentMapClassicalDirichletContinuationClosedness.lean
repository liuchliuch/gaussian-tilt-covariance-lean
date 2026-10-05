import GaussianTilt.MomentMapHolderJetCompactness
import GaussianTilt.MomentMapHolderMongeAmpereInverse
import GaussianTilt.MomentMapClassicalDirichletClassicalLimit

/-!
# Actual nonlinear Dirichlet passage to a bounded Hölder-jet limit

The explicit Hölder norm bound remains the a-priori estimate to be supplied
by nonlinear boundary regularity. Compactness, zero boundary preservation,
positive definiteness, and the nonlinear determinant passage are proved.
-/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 500000
open Set Filter Matrix
open scoped Topology BoundedContinuousFunction ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin GaussianTilt.HolderSpace
variable {n : ℕ}

lemma holder_hessianMatrix_apply {S : Set (CoordinateSpace n)} (hS : Convex ℝ S)
    (α : ℝ) (j : Jet (CoordinateSpace n) ℝ hS α) (x : S) (i l : Fin n) :
    hessianMatrix hS α j x i l = hessianEntry i l
      (value S (CoordinateSpace n →L[ℝ] CoordinateSpace n →L[ℝ] ℝ) α
        (jetSecond (CoordinateSpace n) ℝ hS α j) x) := rfl

lemma holder_hessianMatrix_tendsto_of_second_field_tendsto
    {S : Set (CoordinateSpace n)} (hS : Convex ℝ S) (α : ℝ)
    {j : ℕ → Jet (CoordinateSpace n) ℝ hS α} {g : Jet (CoordinateSpace n) ℝ hS α}
    (h : Tendsto (fun k => value S (CoordinateSpace n →L[ℝ] CoordinateSpace n →L[ℝ] ℝ) α
      (jetSecond (CoordinateSpace n) ℝ hS α (j k))) atTop
      (𝓝 (value S (CoordinateSpace n →L[ℝ] CoordinateSpace n →L[ℝ] ℝ) α
        (jetSecond (CoordinateSpace n) ℝ hS α g)))) (x : S) :
    Tendsto (fun k => hessianMatrix hS α (j k) x) atTop (𝓝 (hessianMatrix hS α g x)) := by
  have hx := (BoundedContinuousFunction.continuous_eval_const (x := x) |>.tendsto _).comp h
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro l
  exact ((hessianEntry i l).continuous.tendsto _).comp hx

lemma isSymm_of_tendsto_matrices {H : ℕ → Matrix (Fin n) (Fin n) ℝ}
    {M : Matrix (Fin n) (Fin n) ℝ} (hH : ∀ k, (H k).IsSymm)
    (hlim : Tendsto H atTop (𝓝 M)) : M.IsSymm := by
  have hclosed : IsClosed {N : Matrix (Fin n) (Fin n) ℝ | N.IsSymm} := by
    exact isClosed_eq (by fun_prop : Continuous (fun N : Matrix (Fin n) (Fin n) ℝ => Nᵀ)) continuous_id
  exact hclosed.mem_of_tendsto hlim (Eventually.of_forall hH)

/-- A uniform value-field limit of actual zero-boundary jets remains in the
true closed boundary kernel, even without convergence in the Hölder norm. -/
lemma holder_zeroBoundary_of_value_limit {S : Set (CoordinateSpace n)} (hS : Convex ℝ S) (α : ℝ)
    (j : ℕ → zeroBoundary (CoordinateSpace n) ℝ hS α) {g : Jet (CoordinateSpace n) ℝ hS α}
    (h : Tendsto (fun k => value S ℝ α (jetValue (CoordinateSpace n) ℝ hS α (j k).1)) atTop
      (𝓝 (value S ℝ α (jetValue (CoordinateSpace n) ℝ hS α g)))) :
    g ∈ zeroBoundary (CoordinateSpace n) ℝ hS α := by
  simp only [zeroBoundary,Submodule.mem_iInf,LinearMap.mem_ker]
  intro x
  have hg := ((BoundedContinuousFunction.evalCLM ℝ x.1).continuous.tendsto _).comp h
  have hzero (k : ℕ) : value S ℝ α (jetValue (CoordinateSpace n) ℝ hS α (j k).1) x.1 = 0 := by
    have hj := (j k).2
    simp only [zeroBoundary,Submodule.mem_iInf,LinearMap.mem_ker] at hj
    exact hj x
  change Tendsto (fun k => value S ℝ α (jetValue (CoordinateSpace n) ℝ hS α (j k).1) x.1) atTop
    (𝓝 (value S ℝ α (jetValue (CoordinateSpace n) ℝ hS α g) x.1)) at hg
  exact tendsto_nhds_unique hg (by simp_rw [hzero]; exact tendsto_const_nhds)

/-- Actual zero-boundary Hölder-jet solutions pass to a genuine solution of
the limiting nonlinear equation under an explicit uniform Hölder norm bound.
Strict positivity at the limit follows from the actual positive density. -/
theorem exists_holder_dirichlet_solution_limit
    {S : Set (CoordinateSpace n)} (hS : Convex ℝ S) (hSc : IsCompact S)
    {α C : ℝ} (hα : 0 < α) (hC : 0 ≤ C)
    {t : ℕ → ℝ} {τ : ℝ} (ht : Tendsto t atTop (𝓝 τ))
    {F : ℝ → Space S ℝ α} (hF : ContinuousAt F τ)
    (hFpos : ∀ x : S, 0 < value S ℝ α (F τ) x)
    (j : ℕ → zeroBoundary (CoordinateSpace n) ℝ hS α)
    (hbound : ∀ k, ‖j k‖ ≤ C)
    (hpd : ∀ k, ∀ x : S, (hessianMatrix hS α (j k).1 x).PosDef)
    (hMA : ∀ k, mongeAmpere hS α (j k).1 = F (t k)) :
    ∃ g : zeroBoundary (CoordinateSpace n) ℝ hS α, ‖g‖ ≤ C ∧
      (∀ x : S, (hessianMatrix hS α g.1 x).PosDef) ∧ mongeAmpere hS α g.1 = F τ := by
  obtain ⟨g,hg,φ,hφ,hv,hD,hH⟩ := exists_jet_uniform_subseq hS hSc hα hC (fun k => (j k).1) hbound
  have hzero := holder_zeroBoundary_of_value_limit hS α (fun k => j (φ k)) hv
  have hmatrix (x : S) := holder_hessianMatrix_tendsto_of_second_field_tendsto hS α hH x
  have hdet (x : S) : (hessianMatrix hS α g x).det = value S ℝ α (F τ) x := by
    have hleft := (continuous_id.matrix_det.tendsto (hessianMatrix hS α g x)).comp (hmatrix x)
    have hright := ((eval S ℝ α x).continuous.tendsto (F τ)).comp
      (hF.tendsto.comp (ht.comp hφ.tendsto_atTop))
    apply tendsto_nhds_unique hleft
    convert hright using 1
    ext k
    change (hessianMatrix hS α (j (φ k)).1 x).det = value S ℝ α (F (t (φ k))) x
    rw [← value_mongeAmpere,hMA (φ k)]
  have hpdg (x : S) : (hessianMatrix hS α g x).PosDef := by
    have hs := isSymm_of_tendsto_matrices (fun k => show (hessianMatrix hS α (j (φ k)).1 x).IsSymm from by
      simpa only [Matrix.IsHermitian,Matrix.IsSymm,Matrix.conjTranspose_eq_transpose_of_trivial] using
        (hpd (φ k) x).isHermitian) (hmatrix x)
    have hp := posSemidef_of_tendsto_matrices hs (fun k => (hpd (φ k) x).posSemidef) (hmatrix x)
    exact posDef_of_posSemidef_det_ne_zero hp (by rw [hdet x]; exact (hFpos x).ne')
  refine ⟨⟨g,hzero⟩,hg,hpdg,?_⟩
  apply value_injective S ℝ α
  apply BoundedContinuousFunction.ext
  intro x
  rw [value_mongeAmpere]
  exact hdet x

/-- The actual set of solvable homotopy parameters is closed once the
explicit uniform Hölder a-priori bound has been established. -/
theorem isClosed_holder_dirichlet_parameters_of_uniform_bound
    {S : Set (CoordinateSpace n)} (hS : Convex ℝ S) (hSc : IsCompact S)
    {α C : ℝ} (hα : 0 < α) (hC : 0 ≤ C)
    (F : ℝ → Space S ℝ α) (hF : Continuous F)
    (hFpos : ∀ t ∈ Icc (0:ℝ) 1, ∀ x : S, 0 < value S ℝ α (F t) x)
    (hbound : ∀ t ∈ Icc (0:ℝ) 1, ∀ j : zeroBoundary (CoordinateSpace n) ℝ hS α,
      (∀ x : S, (hessianMatrix hS α j.1 x).PosDef) → mongeAmpere hS α j.1 = F t → ‖j‖ ≤ C) :
    IsClosed {t : ℝ | t ∈ Icc (0:ℝ) 1 ∧ ∃ j : zeroBoundary (CoordinateSpace n) ℝ hS α,
      (∀ x : S, (hessianMatrix hS α j.1 x).PosDef) ∧ mongeAmpere hS α j.1 = F t} := by
  apply isSeqClosed_iff_isClosed.mp
  intro t τ ht htlim
  have hτ : τ ∈ Icc (0:ℝ) 1 := isClosed_Icc.mem_of_tendsto htlim (Eventually.of_forall (fun k => (ht k).1))
  choose j hjpd hjMA using fun k => (ht k).2
  obtain ⟨g,hg,hgpd,hgMA⟩ := exists_holder_dirichlet_solution_limit hS hSc hα hC htlim hF.continuousAt
    (hFpos τ hτ) j (fun k => hbound (t k) (ht k).1 (j k) (hjpd k) (hjMA k)) hjpd hjMA
  exact ⟨hτ,g,hgpd,hgMA⟩

end GaussianTilt.MomentMapRegularity
