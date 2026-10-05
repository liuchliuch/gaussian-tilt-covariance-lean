import GaussianTilt.MomentMapClassicalDirichletContinuationAdmissibility

/-! # Genuine openness of the admissible Dirichlet homotopy solution set -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 500000
open Set Filter Matrix
open scoped Topology BoundedContinuousFunction ContDiff
namespace GaussianTilt.MomentMapRegularity
open GaussianTilt.Letwin GaussianTilt.HolderSpace
variable {n : ℕ}

/-- The actual inverse-function theorem preserves positive Hessians and
zero boundary values. Linear bijectivity is the precise pending linear PDE
input, rather than an assumed nonlinear local-solvability theorem. -/
theorem holder_dirichlet_local_parameter_solvability
    {S : Set (CoordinateSpace n)} (hS : Convex ℝ S) (hSc : IsCompact S)
    (hint : (interior S).Nonempty) {α : ℝ} (hα : 0 < α)
    {F : ℝ → Space S ℝ α} {τ : ℝ} (hF : ContinuousAt F τ)
    (j : zeroBoundary (CoordinateSpace n) ℝ hS α)
    (hpd : ∀ x : S, (hessianMatrix hS α j.1 x).PosDef)
    (hMA : mongeAmpere hS α j.1 = F τ)
    (hbij : Function.Bijective (fderiv ℝ (dirichletMongeAmpere hS α 0) j)) :
    ∀ᶠ t in 𝓝 τ, ∃ k : zeroBoundary (CoordinateSpace n) ℝ hS α,
      (∀ x : S, (hessianMatrix hS α k.1 x).PosDef) ∧ mongeAmpere hS α k.1 = F t := by
  let U : Set (zeroBoundary (CoordinateSpace n) ℝ hS α) :=
    {k | ∀ x : S, (hessianMatrix hS α k.1 x).PosDef}
  have hU : IsOpen U := (isOpen_positive_holder_hessians hS hSc hint hα).preimage
    (zeroBoundary (CoordinateSpace n) ℝ hS α).subtypeL.continuous
  have hlocal := dirichletMongeAmpere_local_solvability hS α 0 j hbij (hU.mem_nhds hpd)
  have he : dirichletMongeAmpere hS α 0 j = F τ := by simpa [dirichletMongeAmpere] using hMA
  rw [he] at hlocal
  filter_upwards [hF.eventually hlocal] with t ht
  obtain ⟨k,hk,hkeq⟩ := ht
  exact ⟨k,hk,by simpa [dirichletMongeAmpere] using hkeq⟩

/-- Continuation is an actual connectedness argument after the explicit
linear bijectivity and uniform Hölder estimate have been proved. All compact
limit, determinant, positive-definiteness and boundary steps are discharged. -/
theorem holder_dirichlet_continuation
    {S : Set (CoordinateSpace n)} (hS : Convex ℝ S) (hSc : IsCompact S)
    (hint : (interior S).Nonempty) {α C : ℝ} (hα : 0 < α) (hC : 0 ≤ C)
    (F : ℝ → Space S ℝ α) (hF : Continuous F)
    (hFpos : ∀ t ∈ Icc (0:ℝ) 1, ∀ x : S, 0 < value S ℝ α (F t) x)
    (j₀ : zeroBoundary (CoordinateSpace n) ℝ hS α)
    (hpd₀ : ∀ x : S, (hessianMatrix hS α j₀.1 x).PosDef)
    (hMA₀ : mongeAmpere hS α j₀.1 = F 0)
    (hbij : ∀ t ∈ Icc (0:ℝ) 1, ∀ j : zeroBoundary (CoordinateSpace n) ℝ hS α,
      (∀ x : S, (hessianMatrix hS α j.1 x).PosDef) → mongeAmpere hS α j.1 = F t →
      Function.Bijective (fderiv ℝ (dirichletMongeAmpere hS α 0) j))
    (hbound : ∀ t ∈ Icc (0:ℝ) 1, ∀ j : zeroBoundary (CoordinateSpace n) ℝ hS α,
      (∀ x : S, (hessianMatrix hS α j.1 x).PosDef) → mongeAmpere hS α j.1 = F t → ‖j‖ ≤ C) :
    ∃ j : zeroBoundary (CoordinateSpace n) ℝ hS α,
      (∀ x : S, (hessianMatrix hS α j.1 x).PosDef) ∧ mongeAmpere hS α j.1 = F 1 := by
  let T : Set (Icc (0:ℝ) 1) := {t | ∃ j : zeroBoundary (CoordinateSpace n) ℝ hS α,
    (∀ x : S, (hessianMatrix hS α j.1 x).PosDef) ∧ mongeAmpere hS α j.1 = F t}
  have hclosed : IsClosed T := by
    have hc := isClosed_holder_dirichlet_parameters_of_uniform_bound hS hSc hα hC F hF hFpos hbound
    have hp := hc.preimage (continuous_subtype_val : Continuous (fun t : Icc (0:ℝ) 1 => (t:ℝ)))
    convert hp using 1
    ext t
    exact (and_iff_right t.2).symm
  have hopen : IsOpen T := by
    apply isOpen_iff_mem_nhds.mpr
    rintro t ⟨j,hpd,hMA⟩
    have hh := holder_dirichlet_local_parameter_solvability hS hSc hint hα (hF.continuousAt)
      j hpd hMA (hbij t t.2 j hpd hMA)
    exact continuous_subtype_val.continuousAt.eventually hh
  have hne : T.Nonempty := ⟨⟨0,by norm_num⟩,j₀,hpd₀,hMA₀⟩
  have heq : T = univ := (show IsClopen T from ⟨hclosed,hopen⟩).eq_univ hne
  have hmem : (⟨1,by norm_num⟩ : Icc (0:ℝ) 1) ∈ T := by rw [heq]; trivial
  exact hmem

end GaussianTilt.MomentMapRegularity
