import GaussianTilt.MomentMapSchauderBoundaryWeakClassical
import GaussianTilt.MomentMapSchauderBoundaryPatchGeometry
import GaussianTilt.MomentMapHolderJetBounds

/-! # Proven flat-boundary C²,α Schauder estimate for actual weak solutions

The complete compatible Hölder jet is constructed from the weak equation,
actual Newtonian interior regularity, boundary polynomial approximation,
and the derived limits of the true interior derivatives. Its norm is
controlled uniformly by the solution and forcing data.
-/
noncomputable section
set_option maxSynthPendingDepth 1000
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 3200000
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ContDiff
namespace GaussianTilt.MomentMapSchauder
open GaussianTilt.MomentMapElliptic GaussianTilt.MomentMapLinearDirichlet GaussianTilt.MomentMapRegularity
variable {n : ℕ}

/-- Actual scale-uniform flat-boundary Schauder estimate, including the
full closed-domain Banach jet and its norm. Initial boundary derivatives
or an initial Hessian modulus are not hypotheses. -/
theorem exists_flat_boundary_schauder_jet [NeZero n] {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : Fin n) (u f : KernelSpace n → ℝ),
      FlatWeakPoisson j u f → Continuous f → ∀ B H F : ℝ,
      0 ≤ B → 0 ≤ H → 0 ≤ F → (∀ x y, |f x-f y| ≤ H*‖x-y‖^α) →
      (∀ x ∈ Metric.ball (0 : KernelSpace n) 2, |u x| ≤ B) →
      (∀ x ∈ Metric.ball (0 : KernelSpace n) 2, |f x| ≤ F) →
      ∃ J : HolderSpace.Jet (KernelSpace n) ℝ (convex_flatClosedPatch j (1/32)) α,
        ‖J‖ ≤ C*(B+H+F) ∧
        (∀ x : flatClosedPatch j (1/32),
          HolderSpace.value (flatClosedPatch j (1/32)) ℝ α
            (HolderSpace.jetValue (KernelSpace n) ℝ (convex_flatClosedPatch j (1/32)) α J) x=u x) ∧
        (∀ x : flatClosedPatch j (1/32), 0 < (x : KernelSpace n) j →
          HolderSpace.value (flatClosedPatch j (1/32)) (KernelSpace n →L[ℝ] ℝ) α
            (HolderSpace.jetFirst (KernelSpace n) ℝ (convex_flatClosedPatch j (1/32)) α J) x=fderiv ℝ u x) ∧
        (∀ x : flatClosedPatch j (1/32), 0 < (x : KernelSpace n) j →
          HolderSpace.value (flatClosedPatch j (1/32)) (KernelSpace n →L[ℝ] KernelSpace n →L[ℝ] ℝ) α
            (HolderSpace.jetSecond (KernelSpace n) ℝ (convex_flatClosedPatch j (1/32)) α J) x=fderiv ℝ (fderiv ℝ u) x) := by
  obtain ⟨Cb,hCb,hpoly⟩ := exists_uniform_flat_boundary_jets (n := n) hα hα1
  obtain ⟨C1,hC1,hfirst⟩ := exists_flat_first_field_bounds (n := n) hα hα1
  obtain ⟨C2,hC2,hsecond⟩ := exists_flat_second_field_bounds (n := n) hα hα1
  let C := (1+C1+C2)*(Cb+1)+1
  have hC : 0 < C := by dsimp [C]; positivity
  have h1C : 1 ≤ C := by dsimp [C]; nlinarith [mul_pos (show 0 < 1+C1+C2 by positivity) (show 0 < Cb+1 by positivity)]
  refine ⟨C,hC,?_⟩
  intro j u f hu hf B H F hB hH hF hfH huB hfB
  let N := B+H+F
  let M := Cb*N
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hM : 0 ≤ M := mul_nonneg hCb.le hN
  have hNbig : M+H ≤ (Cb+1)*N := by dsimp [M,N]; nlinarith
  have hCbound (A : ℝ) (hA : 0 ≤ A) (hAC : A ≤ 1+C1+C2) : A*(M+H) ≤ C*N := by
    have hh := mul_le_mul hAC hNbig (by positivity : 0 ≤ M+H) (by positivity : 0 ≤ 1+C1+C2)
    apply hh.trans
    dsimp [C]
    nlinarith
  have hC1bound := hCbound C1 hC1.le (by linarith)
  have hC2bound := hCbound C2 hC2.le (by linarith)
  have hBN : B ≤ C*N := by
    have hh := mul_le_mul_of_nonneg_right h1C hN
    dsimp [N] at hh ⊢
    nlinarith
  have hpExists : ∀ a : KernelSpace n, ∃ p : KernelSpace n, ∃ T : KernelSpace n →L[ℝ] KernelSpace n,
      ‖a‖ ≤ 1 → a j=0 →
      (∀ v w, inner ℝ (T v) w=inner ℝ v (T w)) ∧ ‖p‖ ≤ M ∧ ‖T‖ ≤ M ∧
      (∀ h, kernelLaplacian (quadraticJet 0 p 0 T) h= -f a) ∧
      (∀ h, ‖h‖ ≤ 1/4 → 0 ≤ h j → |u (a+h)-quadraticJet 0 p 0 T h| ≤ M*‖h‖^(2+α)) := by
    intro a
    by_cases ha : ‖a‖ ≤ 1 ∧ a j=0
    · obtain ⟨p,T,hT,hpb,hTb,_,hEq,hRem⟩ := hpoly j u f hu hf B H F hB hH hF hfH huB hfB a ha.1 ha.2
      exact ⟨p,T,fun _ _ => ⟨hT,hpb,hTb,hEq,hRem⟩⟩
    · exact ⟨0,0,fun hn hj => (ha ⟨hn,hj⟩).elim⟩
  choose p T hp using hpExists
  have hData : FlatPolynomialData j u f α M p T :=
    ⟨fun a ha hj => (hp a ha hj).1,fun a ha hj => (hp a ha hj).2.1,
      fun a ha hj => (hp a ha hj).2.2.1,fun a ha hj => (hp a ha hj).2.2.2.1,
      fun a ha hj => (hp a ha hj).2.2.2.2⟩
  obtain ⟨huC2,huEq⟩ := flatWeakPoisson_classical hu hf hα hα1 hH hfH
  obtain ⟨hDb,hDLip,hDc⟩ := hfirst j u f huC2 hf huEq M H hM hH hfH p T hData
  obtain ⟨hHb,hHH,hHc⟩ := hsecond j u f huC2 hf huEq M H hM hH hfH p T hData
  let S := flatClosedPatch j (1/32)
  let D := flatFirstField j u p
  let Q := flatSecondField j u T
  have hS : Convex ℝ S := convex_flatClosedPatch j (1/32)
  have hSc : IsCompact S := isCompact_flatClosedPatch j (1/32)
  have hint : (interior S).Nonempty := flatClosedPatch_nonempty_interior j (by norm_num : (0:ℝ)<1/32)
  have huC : ContinuousOn u S := by
    obtain ⟨A,hA,hgrowth⟩ := hu.growth
    exact continuousOn_flat_patch_of_growth j (by norm_num : (1:ℝ)/32<2) hu.continuous hu.zero_lower hgrowth
  have hdu : ∀ x ∈ interior S, HasFDerivAt u (D x) x := by
    intro x hx
    have hxu := flatClosedPatch_interior_subset_upper (by norm_num : (1:ℝ)/32<2) hx
    exact hasFDerivAt_flat_value j p (huC2.contDiffAt ((isOpen_flatUpperBall j 2).mem_nhds hxu)) hxu.2
  have hdD : ∀ x ∈ interior S, HasFDerivAt D (Q x) x := by
    intro x hx
    have hxu := flatClosedPatch_interior_subset_upper (by norm_num : (1:ℝ)/32<2) hx
    exact hasFDerivAt_flatFirstField j p T (huC2.contDiffAt ((isOpen_flatUpperBall j 2).mem_nhds hxu)) hxu.2
  have huLip : ∀ x ∈ S, ∀ y ∈ S, ‖u x-u y‖ ≤ C1*(M+H)*‖x-y‖ := by
    intro x hx y hy
    exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun z hz => HolderSpace.hasFDerivWithinAt_of_continuous_interior_field hS hSc.isClosed hint huC hDc hdu hz)
      hDb hS hy hx
  have hdist : ∀ x ∈ S, ∀ y ∈ S, ‖x-y‖ ≤ ‖x-y‖^α := by
    intro x hx y hy
    apply Real.self_le_rpow_of_le_one (norm_nonneg _) _ hα1.le
    have hx' := flat_patch_norm hx
    have hy' := flat_patch_norm hy
    exact (norm_sub_le _ _).trans (by linarith)
  have huH : ∀ x ∈ S, ∀ y ∈ S, ‖u x-u y‖ ≤ C1*(M+H)*dist x y^α := by
    intro x hx y hy
    rw [dist_eq_norm]
    exact (huLip x hx y hy).trans (mul_le_mul_of_nonneg_left (hdist x hx y hy) (by positivity))
  have hDH : ∀ x ∈ S, ∀ y ∈ S, ‖D x-D y‖ ≤ C1*(M+H)*dist x y^α := by
    intro x hx y hy
    rw [dist_eq_norm]
    exact (hDLip x hx y hy).trans (mul_le_mul_of_nonneg_left (hdist x hx y hy) (by positivity))
  have hQH : ∀ x ∈ S, ∀ y ∈ S, ‖Q x-Q y‖ ≤ C2*(M+H)*dist x y^α := by
    simpa only [dist_eq_norm] using hHH
  obtain ⟨J,hJu,hJD,hJQ⟩ := HolderSpace.exists_jet_of_continuous_holder_interior_fields
    hS hSc hint u D Q huC hDc hHc huH hDH hQH hdu hdD
  have hJn : ‖J‖ ≤ C*N := by
    apply HolderSpace.norm_jet_le_of_field_norms hS J
    · apply HolderSpace.norm_le_of_value_bounds (by positivity : 0 ≤ C*N)
      · intro x
        rw [hJu,Real.norm_eq_abs]
        exact (huB x (by rw [Metric.mem_ball,dist_zero_right]; exact (flat_patch_norm x.2).trans_lt (by norm_num))).trans hBN
      · intro x y
        rw [hJu,hJu]
        exact (huH x x.2 y y.2).trans (mul_le_mul_of_nonneg_right hC1bound (Real.rpow_nonneg dist_nonneg α))
    · apply HolderSpace.norm_le_of_value_bounds (by positivity : 0 ≤ C*N)
      · intro x
        rw [hJD]
        exact (hDb x x.2).trans hC1bound
      · intro x y
        rw [hJD,hJD]
        exact (hDH x x.2 y y.2).trans (mul_le_mul_of_nonneg_right hC1bound (Real.rpow_nonneg dist_nonneg α))
    · apply HolderSpace.norm_le_of_value_bounds (by positivity : 0 ≤ C*N)
      · intro x
        rw [hJQ]
        have hx16 : (x : KernelSpace n) ∈ flatClosedPatch j (1/16) :=
          ⟨Metric.closedBall_subset_closedBall (by norm_num) x.2.1,x.2.2⟩
        exact (hHb x hx16).trans hC2bound
      · intro x y
        rw [hJQ,hJQ]
        exact (hQH x x.2 y y.2).trans (mul_le_mul_of_nonneg_right hC2bound (Real.rpow_nonneg dist_nonneg α))
  refine ⟨J,hJn,hJu,?_,?_⟩
  · intro x hx
    rw [hJD]
    exact if_pos hx
  · intro x hx
    rw [hJQ]
    exact if_pos hx

end GaussianTilt.MomentMapSchauder
