import GaussianTilt.MomentMapHolderMongeAmpere

/-! # Local inversion of the actual Dirichlet Monge–Ampère map

This is the Banach inverse-function step. The explicitly stated linear
bijectivity must be supplied by the separate classical Dirichlet theory.
It is not an analytic axiom or a paper-level closure.
-/
noncomputable section
open Set Filter Matrix
open scoped Topology BoundedContinuousFunction ContDiff
namespace GaussianTilt.HolderSpace
variable {n : ℕ}

theorem dirichletMongeAmpere_fderiv_apply_value {S : Set (Coord (n := n))}
    (hS : Convex ℝ S) (α : ℝ) (base : Jet Coord ℝ hS α)
    (j k : zeroBoundary Coord ℝ hS α) (x : S) :
    value S ℝ α (fderiv ℝ (dirichletMongeAmpere hS α base) j k) x =
      Matrix.trace ((hessianMatrix hS α (base + j.1) x).adjugate * hessianMatrix hS α k.1 x) := by
  have hlin : HasFDerivAt (fun z : zeroBoundary Coord ℝ hS α => base + z.1)
      (zeroBoundary Coord ℝ hS α).subtypeL j :=
    (zeroBoundary Coord ℝ hS α).subtypeL.hasFDerivAt.const_add base
  have hma := ((contDiff_infty.mp (contDiff_mongeAmpere hS α) 1).differentiable le_rfl
    (base + j.1)).hasFDerivAt.comp j hlin
  rw [show fderiv ℝ (dirichletMongeAmpere hS α base) j =
      (fderiv ℝ (mongeAmpere hS α) (base + j.1)).comp
        (zeroBoundary Coord ℝ hS α).subtypeL from hma.fderiv]
  exact mongeAmpere_fderiv_apply_value hS α _ _ x

/-- Every sufficiently small change in the actual Hölder right-hand side
has an actual zero-boundary C² solution near the original jet, once the
cofactor Dirichlet derivative has been proved bijective. -/
theorem dirichletMongeAmpere_local_solvability {S : Set (Coord (n := n))}
    (hS : Convex ℝ S) (α : ℝ) (base : Jet Coord ℝ hS α)
    (j : zeroBoundary Coord ℝ hS α)
    (hbij : Function.Bijective (fderiv ℝ (dirichletMongeAmpere hS α base) j))
    {U : Set (zeroBoundary Coord ℝ hS α)} (hU : U ∈ 𝓝 j) :
    ∀ᶠ f in 𝓝 (dirichletMongeAmpere hS α base j),
      ∃ k ∈ U, dirichletMongeAmpere hS α base k = f := by
  let L := fderiv ℝ (dirichletMongeAmpere hS α base) j
  let e : zeroBoundary Coord ℝ hS α ≃L[ℝ] Space S ℝ α :=
    ContinuousLinearEquiv.ofBijective L (LinearMap.ker_eq_bot.mpr hbij.1)
      (LinearMap.range_eq_top.mpr hbij.2)
  have he : (e : zeroBoundary Coord ℝ hS α →L[ℝ] Space S ℝ α) = L :=
    ContinuousLinearEquiv.coe_ofBijective _ _ _
  have hd : HasStrictFDerivAt (dirichletMongeAmpere hS α base) (e : _ →L[ℝ] _) j := by
    rw [he]
    exact (contDiff_dirichletMongeAmpere hS α base).hasStrictFDerivAt (by simp)
  have hin := hd.localInverse_tendsto hU
  filter_upwards [hin, hd.eventually_right_inverse] with f hf hi
  exact ⟨hd.localInverse _ e j f, hf, hi⟩

end GaussianTilt.HolderSpace
