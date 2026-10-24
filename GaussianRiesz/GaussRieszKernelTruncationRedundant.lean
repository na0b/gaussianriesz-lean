import GaussianRiesz.GaussRieszKernelFarMajorant
open MeasureTheory
theorem GaussRieszKernelTruncationRedundant {n : ℕ} (j : Fin n)
    (x₀ : EuclideanSpace ℝ (Fin n)) (ρ : ℝ) (hρ : 0 < ρ)
    (h : EuclideanSpace ℝ (Fin n) → ℝ) (hmem : MemLp h 1 (GaussMeasure n))
    (hvan : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      y ∈ Metric.ball x₀ (3 * ρ / 4) → h y = 0) :
    ∀ z ∈ Metric.ball x₀ (ρ / 2),
      Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
          GaussRieszKernel j z y * h y) volume
        ∧ ∫ y : EuclideanSpace ℝ (Fin n), GaussRieszKernel j z y * h y
            = ∫ y in {y : EuclideanSpace ℝ (Fin n) | ρ / 4 < ‖z - y‖},
              GaussRieszKernel j z y * h y := by
  -- The far majorant supplies integrability on the truncated region at radius `rho/4`, for
  -- every centre `z` of norm at most `R = |x_0| + rho + 1`, which every `z` in `B(x_0, rho/2)`
  -- satisfies.  What the hypothesis on `h` adds is that the DISCARDED region carries nothing:
  -- `|z - y| <= rho/4` and `|z - x_0| < rho/2` force `|y - x_0| < 3 rho/4`, where `h` vanishes
  -- almost everywhere.  So the integrand vanishes a.e. off the region, which both extends the
  -- integrability to all of `R^n` and makes the two integrals equal.
  obtain ⟨C, hC0, hCa, hCb⟩ :=
    (GaussRieszKernelFarMajorant j).1 (‖x₀‖ + ρ + 1) (ρ / 4)
      (by positivity) (by positivity)
  intro z hz
  have hzx : ‖z - x₀‖ < ρ / 2 := by
    rw [← dist_eq_norm]; exact Metric.mem_ball.1 hz
  have hzR : ‖z‖ ≤ ‖x₀‖ + ρ + 1 := by
    have h1 : ‖z‖ ≤ ‖z - x₀‖ + ‖x₀‖ := by
      calc ‖z‖ = ‖(z - x₀) + x₀‖ := by congr 1; abel
        _ ≤ ‖z - x₀‖ + ‖x₀‖ := norm_add_le _ _
    linarith
  have hΩm : MeasurableSet {y : EuclideanSpace ℝ (Fin n) | ρ / 4 < ‖z - y‖} :=
    measurableSet_lt measurable_const (by fun_prop)
  obtain ⟨hint, -⟩ := hCb h hmem z hzR
  have hoff : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      y ∉ {y : EuclideanSpace ℝ (Fin n) | ρ / 4 < ‖z - y‖} →
        GaussRieszKernel j z y * h y = 0 := by
    filter_upwards [hvan] with y hy hnot
    have h2 : y ∈ Metric.ball x₀ (3 * ρ / 4) := by
      rw [Metric.mem_ball, dist_eq_norm]
      have h3 : ‖y - z‖ = ‖z - y‖ := norm_sub_rev _ _
      calc ‖y - x₀‖ = ‖(y - z) + (z - x₀)‖ := by congr 1; abel
        _ ≤ ‖y - z‖ + ‖z - x₀‖ := norm_add_le _ _
        _ < 3 * ρ / 4 := by rw [h3]; linarith
    rw [hy h2, mul_zero]
  refine ⟨?_, (setIntegral_eq_integral_of_ae_compl_eq_zero hoff).symm⟩
  have hind : Integrable (Set.indicator {y : EuclideanSpace ℝ (Fin n) | ρ / 4 < ‖z - y‖}
      (fun y => GaussRieszKernel j z y * h y)) volume :=
    (integrable_indicator_iff hΩm).2 hint
  refine hind.congr ?_
  filter_upwards [hoff] with y hy
  by_cases hmem2 : y ∈ {y : EuclideanSpace ℝ (Fin n) | ρ / 4 < ‖z - y‖}
  · rw [Set.indicator_of_mem hmem2]
  · rw [Set.indicator_of_notMem hmem2, hy hmem2]
