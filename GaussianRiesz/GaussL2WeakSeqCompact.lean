import GaussianRiesz.HermiteL2Orthonormal
import GaussianRiesz.HermiteL2Complete
open MeasureTheory
theorem GaussL2WeakSeqCompact {n : ℕ} (v : ℕ → Lp ℝ 2 (GaussMeasure n)) (R : ℝ)
    (hbd : ∀ k, ‖v k‖ ≤ R) :
    ∃ (σ : ℕ → ℕ) (u : Lp ℝ 2 (GaussMeasure n)), StrictMono σ ∧ ‖u‖ ≤ R ∧
      ∀ φ : Lp ℝ 2 (GaussMeasure n),
        Filter.Tendsto (fun j => inner ℝ (v (σ j)) φ) Filter.atTop
          (nhds (inner ℝ u φ)) := by
  -- Steps 1-2: `L²(γ_n)` is separable, because it is the closure of the span of the
  -- countable Hermite family
  have hsep : TopologicalSpace.SeparableSpace (Lp ℝ 2 (GaussMeasure n)) := by
    rw [← TopologicalSpace.isSeparable_univ_iff]
    have hcount : (Set.range (HermiteL2 (n := n))).Countable := Set.countable_range _
    have h1 : TopologicalSpace.IsSeparable
        ((Submodule.span ℝ (Set.range (HermiteL2 (n := n))) :
          Submodule ℝ (Lp ℝ 2 (GaussMeasure n))) : Set (Lp ℝ 2 (GaussMeasure n))) :=
      hcount.isSeparable.span
    have h2 : closure ((Submodule.span ℝ (Set.range (HermiteL2 (n := n))) :
        Submodule ℝ (Lp ℝ 2 (GaussMeasure n))) : Set (Lp ℝ 2 (GaussMeasure n)))
        = Set.univ :=
      Set.eq_univ_of_forall fun x => HermiteL2Complete n Submodule.mem_top
    rw [← h2]
    exact TopologicalSpace.isSeparable_closure.mpr h1
  -- Steps 3-4: pass to the dual, extract weak-*, and transport back by Riesz
  -- the dual sequence, in the weak-* topology
  have hmem : ∀ k, (StrongDual.toWeakDual (innerSL ℝ (v k)))
      ∈ (WeakDual.toStrongDual ⁻¹'
          Metric.closedBall (0 : StrongDual ℝ (Lp ℝ 2 (GaussMeasure n))) R) := by
    intro k
    simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
    rw [show WeakDual.toStrongDual (StrongDual.toWeakDual (innerSL ℝ (v k)))
        = innerSL ℝ (v k) from rfl, innerSL_apply_norm]
    exact hbd k
  obtain ⟨Λ, hΛmem, σ, hσ, htend⟩ :=
    WeakDual.isSeqCompact_closedBall ℝ (Lp ℝ 2 (GaussMeasure n))
      (0 : StrongDual ℝ (Lp ℝ 2 (GaussMeasure n))) R hmem
  refine ⟨σ, (InnerProductSpace.toDual ℝ (Lp ℝ 2 (GaussMeasure n))).symm
    (WeakDual.toStrongDual Λ), hσ, ?_, ?_⟩
  · -- the norm bound transports through the Riesz isometry
    rw [LinearIsometryEquiv.norm_map]
    simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] at hΛmem
    exact hΛmem
  · intro φ
    rw [InnerProductSpace.toDual_symm_apply]
    exact ((WeakDual.eval_continuous φ).tendsto Λ).comp htend
