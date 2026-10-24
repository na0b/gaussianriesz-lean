import GaussianRiesz.PVCoreSmooth
open MeasureTheory
theorem GaussRieszKernelSmoothOffDiagonal {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) (j : Fin n)
    (z : EuclideanSpace ℝ (Fin n)) (σ : ℝ) (hσ : 0 < σ)
    (hvan : ∀ y : EuclideanSpace ℝ (Fin n), ‖z - y‖ ≤ σ → f y = 0) :
    Integrable (fun y : EuclideanSpace ℝ (Fin n) => GaussRieszKernel j z y * f y) volume
      ∧ (Real.sqrt Real.pi)⁻¹ * ∫ s in Set.Ioi (0 : ℝ), (Real.sqrt s)⁻¹ *
          (Real.exp (-s) * ((Real.sqrt 2)⁻¹ *
            ∫ ζ, fderiv ℝ f (Real.exp (-s) • z + Real.sqrt (1 - Real.exp (-2 * s)) • ζ)
              (EuclideanSpace.single j (1 : ℝ)) ∂(GaussMeasure n)))
        = ∫ y : EuclideanSpace ℝ (Fin n), GaussRieszKernel j z y * f y := by
  -- `PVCoreSmooth` gives integrability of the truncated integrand at EVERY radius and the
  -- `epsilon -> 0` limit of the truncated integrals.  The extra hypothesis -- that `f` vanishes
  -- on the closed ball of radius `sigma` about `z` -- makes the truncated integral INDEPENDENT
  -- of the radius on `(0, sigma]`: the discarded region carries no mass.  A function that is
  -- eventually constant along a filter converges to that constant, so the limit `PVCoreSmooth`
  -- names must BE the untruncated integral.  No principal value is taken.
  obtain ⟨hpv1, hpv2⟩ := PVCoreSmooth f hf hfc j z
  have hkey : ∀ ε : ℝ, 0 < ε → ε ≤ σ →
      Integrable (fun y : EuclideanSpace ℝ (Fin n) => GaussRieszKernel j z y * f y) volume
        ∧ ∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖z - y‖},
              GaussRieszKernel j z y * f y
            = ∫ y : EuclideanSpace ℝ (Fin n), GaussRieszKernel j z y * f y := by
    intro ε hε hεσ
    have hΩm : MeasurableSet {y : EuclideanSpace ℝ (Fin n) | ε < ‖z - y‖} :=
      measurableSet_lt measurable_const (by fun_prop)
    have hoff : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        y ∉ {y : EuclideanSpace ℝ (Fin n) | ε < ‖z - y‖} →
          GaussRieszKernel j z y * f y = 0 := by
      refine Filter.Eventually.of_forall fun y hnot => ?_
      have h1 : ‖z - y‖ ≤ ε := not_lt.1 hnot
      rw [hvan y (by linarith), mul_zero]
    refine ⟨?_, setIntegral_eq_integral_of_ae_compl_eq_zero hoff⟩
    have hind := (integrable_indicator_iff hΩm).2 (hpv1 ε hε)
    refine hind.congr ?_
    filter_upwards [hoff] with y hy
    by_cases hmem : y ∈ {y : EuclideanSpace ℝ (Fin n) | ε < ‖z - y‖}
    · rw [Set.indicator_of_mem hmem]
    · rw [Set.indicator_of_notMem hmem, hy hmem]
  refine ⟨(hkey σ hσ le_rfl).1, ?_⟩
  have hconst : (fun ε : ℝ => ∫ y in {y : EuclideanSpace ℝ (Fin n) | ε < ‖z - y‖},
        GaussRieszKernel j z y * f y)
      =ᶠ[nhdsWithin 0 (Set.Ioi (0 : ℝ))]
        (fun _ => ∫ y : EuclideanSpace ℝ (Fin n), GaussRieszKernel j z y * f y) := by
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (gt_mem_nhds hσ)] with ε hε hεσ
    exact (hkey ε hε hεσ.le).2
  exact tendsto_nhds_unique (hpv2.congr' hconst) tendsto_const_nhds
