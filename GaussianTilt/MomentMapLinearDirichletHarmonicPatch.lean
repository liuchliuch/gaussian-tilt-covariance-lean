import GaussianTilt.MomentMapLinearDirichletHarmonicRegularity

/-!
# Actual patching of local regular representatives

The canonical mollifier limit defines a single representative. Whenever
local continuous representatives agree almost everywhere, the actual
mollifiers eventually see only that neighborhood and converge to their
pointwise values. Thus the canonical representative inherits the local
regularity and remains in the original almost-everywhere class.
-/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff Convolution
namespace GaussianTilt.MomentMapLinearDirichlet
open GaussianTilt.MomentMapElliptic
variable {n : ℕ}

def harmonicRepresentative (f : KernelSpace n → ℝ) (x : KernelSpace n) : ℝ :=
  limUnder atTop (fun k => harmonicMollify k f x)

lemma harmonicRepresentative_ae_eq {f : KernelSpace n → ℝ} (hf : LocallyIntegrable f volume) :
    harmonicRepresentative f =ᵐ[volume] f := by
  filter_upwards [harmonicMollify_ae_tendsto hf] with x hx
  exact hx.limUnder_eq

lemma harmonicMollify_tendsto_of_local_ae_eq {f v : KernelSpace n → ℝ}
    {U : Set (KernelSpace n)} (hU : IsOpen U) (hv : Continuous v)
    (hfv : ∀ᵐ y ∂volume, y ∈ U → f y = v y) {x : KernelSpace n} (hx : x ∈ U) :
    Tendsto (fun k => harmonicMollify k f x) atTop (𝓝 (v x)) := by
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  have ht : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have he : (fun k => harmonicMollify k f x) =ᶠ[atTop] (fun k => harmonicMollify k v x) := by
    filter_upwards [(tendsto_order.mp ht).2 r hr] with k hk
    simp only [harmonicMollify, harmonicConvolution_flip_apply]
    apply integral_congr_ae
    filter_upwards [hfv] with y hy
    by_cases hxy : (harmonicMollifierBump n k).normed volume (x-y) = 0
    · simp only [hxy, mul_zero]
    · have hyball : y ∈ Metric.closedBall x ((k : ℝ) + 1)⁻¹ :=
        harmonic_mollifier_translated_support k x (subset_tsupport _ hxy)
      have hyU : y ∈ U := hrU (Metric.closedBall_subset_ball hk hyball)
      rw [hy hyU]
  have hvlim : Tendsto (fun k => harmonicMollify k v x) atTop (𝓝 (v x)) :=
    ContDiffBump.convolution_tendsto_right_of_continuous (φ := harmonicMollifierBump n) ht hv x
  exact hvlim.congr' he.symm

lemma harmonicRepresentative_eqOn_of_local_ae_eq {f v : KernelSpace n → ℝ}
    {U : Set (KernelSpace n)} (hU : IsOpen U) (hv : Continuous v)
    (hfv : ∀ᵐ y ∂volume, y ∈ U → f y = v y) : EqOn (harmonicRepresentative f) v U := by
  intro x hx
  exact (harmonicMollify_tendsto_of_local_ae_eq hU hv hfv hx).limUnder_eq

/-- Any proved local regular representatives patch to one actual function
of the same AE class. This applies at C² as well as C∞ regularity. -/
theorem contDiffAt_harmonicRepresentative_of_local_representatives
    {f : KernelSpace n → ℝ} {Ω : Set (KernelSpace n)} {m : WithTop ℕ∞}
    (hlocal : ∀ x ∈ Ω, ∃ r : ℝ, 0 < r ∧ ∃ v : KernelSpace n → ℝ,
      ContDiff ℝ m v ∧ ∀ᵐ y ∂volume, y ∈ Metric.ball x r → v y = f y) :
    ∀ x ∈ Ω, ContDiffAt ℝ m (harmonicRepresentative f) x := by
  intro x hx
  obtain ⟨r, hr, v, hv, hvf⟩ := hlocal x hx
  have he := harmonicRepresentative_eqOn_of_local_ae_eq Metric.isOpen_ball hv.continuous (by
    filter_upwards [hvf] with y hy hym
    exact (hy hym).symm)
  exact hv.contDiffAt.congr_of_eventuallyEq
    (Filter.eventually_of_mem (Metric.ball_mem_nhds x hr) he)

end GaussianTilt.MomentMapLinearDirichlet
