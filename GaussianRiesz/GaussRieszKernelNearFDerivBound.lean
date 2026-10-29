module

public import GaussianRiesz.GaussRieszKernel
public import GaussianRiesz.GaussRieszKernelNearSliceBounds
public import GaussianRiesz.TauPowerIntegralBounds
public import GaussianRiesz.RpowPowerReductionsToNegPower
public import GaussianRiesz.GaussRieszKernelNearBallUniformTauMajorant
public import GaussianRiesz.OneSubReflectionIntegralTransfer

@[expose] public section
open MeasureTheory Filter Topology
theorem GaussRieszKernelNearFDerivBound {n : ℕ} (j : Fin n) (R M : ℝ)
    (hR : 0 < R) (hMR : M = R + 3) :
      ∃ C : ℝ, 0 < C ∧ ∀ x y : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ R + 1 → ‖y‖ ≤ M →
          0 < ‖x - y‖ → ‖x - y‖ ≤ 2 →
          IntegrableOn (fun r : ℝ =>
              (y j - r * x j) / ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r))
                * Real.exp (-‖r • x - y‖ ^ 2 / (1 - r ^ 2))) (Set.Ioo (0:ℝ) 1) volume →
        ∃ g : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ,
          HasFDerivAt (fun w : EuclideanSpace ℝ (Fin n) => GaussRieszKernel j w y) g x
            ∧ ‖g‖ ≤ C * ‖x - y‖ ^ (-((n:ℝ) + 1)) := by
  classical
  have hn : 0 < n := Fin.pos j
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hM : 3 ≤ M := by rw [hMR]; linarith
  obtain ⟨hrefl, hreflint⟩ := OneSubReflectionIntegralTransfer
  -- continuity of the slice in `r`, for every base point
  have hΦcont : ∀ w z : EuclideanSpace ℝ (Fin n), ContinuousOn (fun r : ℝ =>
      (z j - r * w j) / ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r))
        * Real.exp (-‖r • w - z‖ ^ 2 / (1 - r ^ 2))) (Set.Ioo (0:ℝ) 1) := by
    intro w z r hr
    obtain ⟨hr0, hr1⟩ := hr
    refine ContinuousAt.continuousWithinAt ?_
    have h1 : (1 - r ^ 2) ≠ 0 := by nlinarith
    have h2 : r ≠ 0 := ne_of_gt hr0
    have hlogr : 0 < -Real.log r := by
      have := Real.log_neg hr0 hr1; linarith
    have h3 : Real.sqrt (-Real.log r) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hlogr)
    have h4 : (1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) ≠ 0 := by
      have : (0:ℝ) < 1 - r ^ 2 := by nlinarith
      positivity
    fun_prop (disch := first | assumption | positivity | simp_all)
  obtain ⟨K1, hK1pos, hK1⟩ := TauPowerIntegralBounds.1 ((n:ℝ)/2 + 3/2) (by linarith)
  obtain ⟨Kb, hKbpos, hKb⟩ := TauPowerIntegralBounds.1 ((n:ℝ)/2 + 5/2) (by linarith)
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hcn : (0:ℝ) < Real.sqrt 2 * Real.pi ^ (-((n : ℝ) + 1) / 2) := by positivity
  refine ⟨(Real.sqrt 2 * Real.pi ^ (-((n : ℝ) + 1) / 2)) * (Real.exp (M ^ 2)
        * (K1 * (9/128 : ℝ) ^ (1 - ((n:ℝ)/2 + 3/2))
          + 8 * Kb * (9/128 : ℝ) ^ (-((n:ℝ)/2 + 3/2)))
      + Real.exp (M ^ 2)
        * ((8 * M / 3) ^ ((n:ℝ)/2 + 3/2) * 2 ^ (-((n:ℝ)/2 + 3/2) + ((n:ℝ) + 1))
          + 8 * (8 * M / 3) ^ ((n:ℝ)/2 + 5/2) * 2 ^ (1 - ((n:ℝ)/2 + 3/2) + ((n:ℝ) + 1))
          + 4 * M ^ 2 * (8 * M / 3) ^ ((n:ℝ)/2 + 1/2)
            * 2 ^ (1 - ((n:ℝ)/2 + 3/2) + ((n:ℝ) + 1)))), by positivity, ?_⟩
  intro x y hxR hyM hd0 hd2 hΦint
  obtain ⟨G, hGcont, hGderiv⟩ := (GaussRieszKernelNearSliceBounds j M hM y hyM).2.2
  have hUmem : ∀ w ∈ Metric.ball x (‖x - y‖ / 4), ‖w‖ ≤ M ∧ 3 * ‖x - y‖ / 4 ≤ ‖w - y‖
      ∧ ‖w - y‖ ≤ 5 * ‖x - y‖ / 4 := by
    intro w hw
    have hwx : ‖w - x‖ < ‖x - y‖ / 4 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hw
    refine ⟨?_, ?_, ?_⟩
    · have h1 : ‖w‖ - ‖x‖ ≤ ‖w - x‖ := norm_sub_norm_le w x
      rw [hMR]; linarith
    · have h1 : ‖x - y‖ - ‖w - x‖ ≤ ‖w - y‖ := by
        have e1 : x - y = (w - y) - (w - x) := by abel
        have h2 := norm_sub_le (w - y) (w - x)
        rw [← e1] at h2
        linarith
      linarith
    · have e1 : w - y = (w - x) + (x - y) := by abel
      have h2 : ‖(w - x) + (x - y)‖ ≤ ‖w - x‖ + ‖x - y‖ := norm_add_le _ _
      rw [← e1] at h2
      linarith
  -- the `w`-uniform majorant on the ball, in `tau`
  have hGbd := GaussRieszKernelNearBallUniformTauMajorant M hM x y hyM hd0 G
    (fun w hwM r hr0 hr1 => (hGderiv w hwM r hr0 hr1).2) hUmem
  -- integrability of the majorant
  obtain ⟨hNa, hNabd⟩ := hK1 (9/128 * ‖x - y‖ ^ 2) (by positivity)
  obtain ⟨hNb, hNbbd⟩ := hKb (9/128 * ‖x - y‖ ^ 2) (by positivity)
  have hsubIoi : Set.Ioo (0:ℝ) 1 ⊆ Set.Ioi (0:ℝ) := fun t ht => ht.1
  have hsubae : (Set.Ioo (0:ℝ) 1 : Set ℝ) ≤ᵐ[(volume : Measure ℝ)] Set.Ioi (0:ℝ) :=
    hsubIoi.eventuallyLE
  have hNint : IntegrableOn (fun τ : ℝ =>
      Real.exp (M ^ 2) * (τ ^ (-((n:ℝ)/2 + 3/2))
          * Real.exp (-(9/128 * ‖x - y‖ ^ 2) / τ))
        + Real.exp (M ^ 2) * (8 * ‖x - y‖ ^ 2) * (τ ^ (-((n:ℝ)/2 + 5/2))
          * Real.exp (-(9/128 * ‖x - y‖ ^ 2) / τ))) (Set.Ioo (0:ℝ) 1) volume :=
    ((hNa.mono_set hsubIoi).const_mul (Real.exp (M ^ 2))).add
      ((hNb.mono_set hsubIoi).const_mul (Real.exp (M ^ 2) * (8 * ‖x - y‖ ^ 2)))
  have hcint : IntegrableOn (fun _ : ℝ => Real.exp (M ^ 2)
      * ((‖x - y‖ / (8 * M / 3)) ^ (-((n:ℝ)/2 + 3/2))
        + 8 * ‖x - y‖ ^ 2 * (‖x - y‖ / (8 * M / 3)) ^ (-((n:ℝ)/2 + 5/2))
        + 4 * M ^ 2 * (‖x - y‖ / (8 * M / 3)) ^ (-((n:ℝ)/2 + 1/2))))
      (Set.Ioo (0:ℝ) 1) volume := by
    refine integrableOn_const ?_
    simp [Real.volume_Ioo]
  have hBint := hNint.add hcint
  have hboundint : IntegrableOn (fun r : ℝ =>
      Real.exp (M ^ 2) * ((1 - r) ^ (-((n:ℝ)/2 + 3/2))
            * Real.exp (-(9/128 * ‖x - y‖ ^ 2) / (1 - r)))
          + Real.exp (M ^ 2) * (8 * ‖x - y‖ ^ 2) * ((1 - r) ^ (-((n:ℝ)/2 + 5/2))
            * Real.exp (-(9/128 * ‖x - y‖ ^ 2) / (1 - r)))
        + Real.exp (M ^ 2)
          * ((‖x - y‖ / (8 * M / 3)) ^ (-((n:ℝ)/2 + 3/2))
            + 8 * ‖x - y‖ ^ 2 * (‖x - y‖ / (8 * M / 3)) ^ (-((n:ℝ)/2 + 5/2))
            + 4 * M ^ 2 * (‖x - y‖ / (8 * M / 3)) ^ (-((n:ℝ)/2 + 1/2))))
      (Set.Ioo (0:ℝ) 1) volume := by
    have h := hreflint _ 1 hBint
    simpa using h
  -- the derivative under the integral sign
  have hball : Metric.ball x (‖x - y‖ / 4) ∈ nhds x := Metric.ball_mem_nhds x (by positivity)
  have hbound : ∀ᵐ r ∂(volume.restrict (Set.Ioo (0:ℝ) 1)),
      ∀ w ∈ Metric.ball x (‖x - y‖ / 4), ‖innerSL ℝ (G w r)‖
        ≤ (Real.exp (M ^ 2) * ((1 - r) ^ (-((n:ℝ)/2 + 3/2))
                * Real.exp (-(9/128 * ‖x - y‖ ^ 2) / (1 - r)))
              + Real.exp (M ^ 2) * (8 * ‖x - y‖ ^ 2) * ((1 - r) ^ (-((n:ℝ)/2 + 5/2))
                * Real.exp (-(9/128 * ‖x - y‖ ^ 2) / (1 - r))))
            + Real.exp (M ^ 2)
              * ((‖x - y‖ / (8 * M / 3)) ^ (-((n:ℝ)/2 + 3/2))
                + 8 * ‖x - y‖ ^ 2 * (‖x - y‖ / (8 * M / 3)) ^ (-((n:ℝ)/2 + 5/2))
                + 4 * M ^ 2 * (‖x - y‖ / (8 * M / 3)) ^ (-((n:ℝ)/2 + 1/2))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr w hw
    rw [innerSL_apply_norm]
    have h := hGbd w hw (1 - r) (by linarith [hr.2]) (by linarith [hr.1])
    rwa [sub_sub_cancel] at h
  have hdiff : ∀ᵐ r ∂(volume.restrict (Set.Ioo (0:ℝ) 1)),
      ∀ w ∈ Metric.ball x (‖x - y‖ / 4),
        HasFDerivAt (fun v : EuclideanSpace ℝ (Fin n) =>
          (y j - r * v j) / ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r))
            * Real.exp (-‖r • v - y‖ ^ 2 / (1 - r ^ 2))) (innerSL ℝ (G w r)) w := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr w hw
    exact (hGderiv w (hUmem w hw).1 r hr.1 hr.2).1
  have hdi := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := volume.restrict (Set.Ioo (0:ℝ) 1))
    (F := fun (w : EuclideanSpace ℝ (Fin n)) (r : ℝ) =>
      (y j - r * w j) / ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r))
        * Real.exp (-‖r • w - y‖ ^ 2 / (1 - r ^ 2)))
    (F' := fun (w : EuclideanSpace ℝ (Fin n)) (r : ℝ) => innerSL ℝ (G w r))
    hball
    (Filter.Eventually.of_forall
      (fun w => (hΦcont w y).aestronglyMeasurable measurableSet_Ioo))
    hΦint
    (((innerSL ℝ).continuous.comp_continuousOn (hGcont x)).aestronglyMeasurable
      measurableSet_Ioo)
    hbound
    hboundint
    hdiff
  refine ⟨(Real.sqrt 2 * Real.pi ^ (-((n : ℝ) + 1) / 2))
    • (∫ r in Set.Ioo (0:ℝ) 1, innerSL ℝ (G x r)), ?_, ?_⟩
  · have hfun : (fun w : EuclideanSpace ℝ (Fin n) => GaussRieszKernel j w y)
        = fun w : EuclideanSpace ℝ (Fin n) =>
          (Real.sqrt 2 * Real.pi ^ (-((n : ℝ) + 1) / 2))
            * ∫ r in Set.Ioo (0:ℝ) 1,
              (y j - r * w j) / ((1 - r ^ 2) ^ ((n : ℝ) / 2 + 1) * Real.sqrt (-Real.log r))
                * Real.exp (-‖r • w - y‖ ^ 2 / (1 - r ^ 2)) := by
      funext w
      rw [GaussRieszKernel]
    rw [hfun]
    exact hdi.const_mul _
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hcn]
    have hxball : x ∈ Metric.ball x (‖x - y‖ / 4) := Metric.mem_ball_self (by positivity)
    have hGxint : IntegrableOn (fun r : ℝ => ‖innerSL ℝ (G x r)‖)
        (Set.Ioo (0:ℝ) 1) volume := by
      refine Integrable.mono' hboundint
        ((continuous_norm.comp_continuousOn
          ((innerSL ℝ).continuous.comp_continuousOn (hGcont x))).aestronglyMeasurable
            measurableSet_Ioo) ?_
      filter_upwards [hbound] with r hr
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact hr x hxball
    -- the value of the majorant integral
    have hFARCval : ∫ _r in Set.Ioo (0:ℝ) 1, Real.exp (M ^ 2)
          * ((‖x - y‖ / (8 * M / 3)) ^ (-((n:ℝ)/2 + 3/2))
            + 8 * ‖x - y‖ ^ 2 * (‖x - y‖ / (8 * M / 3)) ^ (-((n:ℝ)/2 + 5/2))
            + 4 * M ^ 2 * (‖x - y‖ / (8 * M / 3)) ^ (-((n:ℝ)/2 + 1/2)))
        = Real.exp (M ^ 2)
          * ((‖x - y‖ / (8 * M / 3)) ^ (-((n:ℝ)/2 + 3/2))
            + 8 * ‖x - y‖ ^ 2 * (‖x - y‖ / (8 * M / 3)) ^ (-((n:ℝ)/2 + 5/2))
            + 4 * M ^ 2 * (‖x - y‖ / (8 * M / 3)) ^ (-((n:ℝ)/2 + 1/2))) := by
      rw [setIntegral_const]
      simp
    -- the three `d`-power reductions
    obtain ⟨hb1, hb2, hf1, hf2, hf3⟩ :=
      RpowPowerReductionsToNegPower hn1 M hM ‖x - y‖ hd0 hd2
    -- the pointwise majorant at `w = x`
    have hbdpt : ∀ r ∈ Set.Ioo (0:ℝ) 1, ‖innerSL ℝ (G x r)‖
        ≤ Real.exp (M ^ 2) * ((1 - r) ^ (-((n:ℝ)/2 + 3/2))
              * Real.exp (-(9/128 * ‖x - y‖ ^ 2) / (1 - r)))
            + Real.exp (M ^ 2) * (8 * ‖x - y‖ ^ 2) * ((1 - r) ^ (-((n:ℝ)/2 + 5/2))
              * Real.exp (-(9/128 * ‖x - y‖ ^ 2) / (1 - r)))
          + Real.exp (M ^ 2)
            * ((‖x - y‖ / (8 * M / 3)) ^ (-((n:ℝ)/2 + 3/2))
              + 8 * ‖x - y‖ ^ 2 * (‖x - y‖ / (8 * M / 3)) ^ (-((n:ℝ)/2 + 5/2))
              + 4 * M ^ 2 * (‖x - y‖ / (8 * M / 3)) ^ (-((n:ℝ)/2 + 1/2))) := by
      intro r hr
      rw [innerSL_apply_norm]
      have h := hGbd x hxball (1 - r) (by linarith [hr.2]) (by linarith [hr.1])
      rwa [sub_sub_cancel] at h
    -- the majorant integral, one summand at a time
    have hP1le : ∫ τ in Set.Ioo (0:ℝ) 1,
          (τ ^ (-((n:ℝ)/2 + 3/2)) * Real.exp (-(9/128 * ‖x - y‖ ^ 2) / τ))
        ≤ K1 * (9/128 * ‖x - y‖ ^ 2) ^ (1 - ((n:ℝ)/2 + 3/2)) := by
      refine le_trans (setIntegral_mono_set hNa ?_ hsubae) hNabd
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
      have hτ0 : (0:ℝ) < τ := hτ
      show (0:ℝ) ≤ _
      positivity
    have hP2le : ∫ τ in Set.Ioo (0:ℝ) 1,
          (τ ^ (-((n:ℝ)/2 + 5/2)) * Real.exp (-(9/128 * ‖x - y‖ ^ 2) / τ))
        ≤ Kb * (9/128 * ‖x - y‖ ^ 2) ^ (1 - ((n:ℝ)/2 + 5/2)) := by
      refine le_trans (setIntegral_mono_set hNb ?_ hsubae) hNbbd
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
      have hτ0 : (0:ℝ) < τ := hτ
      show (0:ℝ) ≤ _
      positivity
    have hNbd : ∫ τ in Set.Ioo (0:ℝ) 1,
          (Real.exp (M ^ 2) * (τ ^ (-((n:ℝ)/2 + 3/2))
              * Real.exp (-(9/128 * ‖x - y‖ ^ 2) / τ))
            + Real.exp (M ^ 2) * (8 * ‖x - y‖ ^ 2) * (τ ^ (-((n:ℝ)/2 + 5/2))
              * Real.exp (-(9/128 * ‖x - y‖ ^ 2) / τ)))
        ≤ Real.exp (M ^ 2) * (K1 * (9/128 : ℝ) ^ (1 - ((n:ℝ)/2 + 3/2))
            + 8 * Kb * (9/128 : ℝ) ^ (-((n:ℝ)/2 + 3/2))) * ‖x - y‖ ^ (-((n:ℝ) + 1)) := by
      rw [integral_add ((hNa.mono_set hsubIoi).const_mul (Real.exp (M ^ 2)))
          ((hNb.mono_set hsubIoi).const_mul (Real.exp (M ^ 2) * (8 * ‖x - y‖ ^ 2))),
        integral_const_mul, integral_const_mul]
      have hle := add_le_add (mul_le_mul_of_nonneg_left hP1le
          (le_of_lt (Real.exp_pos (M ^ 2))))
        (mul_le_mul_of_nonneg_left hP2le
          (show (0:ℝ) ≤ Real.exp (M ^ 2) * (8 * ‖x - y‖ ^ 2) by positivity))
      refine le_trans hle (le_of_eq ?_)
      rw [hb1]
      calc Real.exp (M ^ 2) * (K1 * ((9/128 : ℝ) ^ (1 - ((n:ℝ)/2 + 3/2))
              * ‖x - y‖ ^ (-((n:ℝ) + 1))))
            + Real.exp (M ^ 2) * (8 * ‖x - y‖ ^ 2)
              * (Kb * (9/128 * ‖x - y‖ ^ 2) ^ (1 - ((n:ℝ)/2 + 5/2)))
          = Real.exp (M ^ 2) * (K1 * ((9/128 : ℝ) ^ (1 - ((n:ℝ)/2 + 3/2))
              * ‖x - y‖ ^ (-((n:ℝ) + 1))))
            + Real.exp (M ^ 2) * Kb
              * (8 * ‖x - y‖ ^ 2 * (9/128 * ‖x - y‖ ^ 2) ^ (1 - ((n:ℝ)/2 + 5/2))) := by ring
        _ = Real.exp (M ^ 2) * (K1 * ((9/128 : ℝ) ^ (1 - ((n:ℝ)/2 + 3/2))
              * ‖x - y‖ ^ (-((n:ℝ) + 1))))
            + Real.exp (M ^ 2) * Kb
              * (8 * (9/128 : ℝ) ^ (-((n:ℝ)/2 + 3/2))
                * ‖x - y‖ ^ (-((n:ℝ) + 1))) := by rw [hb2]
        _ = Real.exp (M ^ 2) * (K1 * (9/128 : ℝ) ^ (1 - ((n:ℝ)/2 + 3/2))
              + 8 * Kb * (9/128 : ℝ) ^ (-((n:ℝ)/2 + 3/2)))
            * ‖x - y‖ ^ (-((n:ℝ) + 1)) := by ring
    -- assemble
    have hNrint : IntegrableOn (fun r : ℝ => (Real.exp (M ^ 2) * ((1 - r) ^ (-((n:ℝ)/2 + 3/2))
                * Real.exp (-(9/128 * ‖x - y‖ ^ 2) / (1 - r)))
              + Real.exp (M ^ 2) * (8 * ‖x - y‖ ^ 2) * ((1 - r) ^ (-((n:ℝ)/2 + 5/2))
                * Real.exp (-(9/128 * ‖x - y‖ ^ 2) / (1 - r))))) (Set.Ioo (0:ℝ) 1) volume := by
      have h := hreflint _ 1 hNint
      simpa using h
    have hstep3 : ∫ r in Set.Ioo (0:ℝ) 1, ((Real.exp (M ^ 2) * ((1 - r) ^ (-((n:ℝ)/2 + 3/2))
                * Real.exp (-(9/128 * ‖x - y‖ ^ 2) / (1 - r)))
              + Real.exp (M ^ 2) * (8 * ‖x - y‖ ^ 2) * ((1 - r) ^ (-((n:ℝ)/2 + 5/2))
                * Real.exp (-(9/128 * ‖x - y‖ ^ 2) / (1 - r))))
          + Real.exp (M ^ 2)
              * ((‖x - y‖ / (8 * M / 3)) ^ (-((n:ℝ)/2 + 3/2))
                + 8 * ‖x - y‖ ^ 2 * (‖x - y‖ / (8 * M / 3)) ^ (-((n:ℝ)/2 + 5/2))
                + 4 * M ^ 2 * (‖x - y‖ / (8 * M / 3)) ^ (-((n:ℝ)/2 + 1/2))))
        = (∫ τ in Set.Ioo (0:ℝ) 1, (Real.exp (M ^ 2) * (τ ^ (-((n:ℝ)/2 + 3/2))
                * Real.exp (-(9/128 * ‖x - y‖ ^ 2) / τ))
              + Real.exp (M ^ 2) * (8 * ‖x - y‖ ^ 2) * (τ ^ (-((n:ℝ)/2 + 5/2))
                * Real.exp (-(9/128 * ‖x - y‖ ^ 2) / τ)))) + (Real.exp (M ^ 2)
              * ((‖x - y‖ / (8 * M / 3)) ^ (-((n:ℝ)/2 + 3/2))
                + 8 * ‖x - y‖ ^ 2 * (‖x - y‖ / (8 * M / 3)) ^ (-((n:ℝ)/2 + 5/2))
                + 4 * M ^ 2 * (‖x - y‖ / (8 * M / 3)) ^ (-((n:ℝ)/2 + 1/2)))) := by
      rw [integral_add hNrint hcint, hFARCval]
      congr 1
      have h := hrefl (fun τ : ℝ => (Real.exp (M ^ 2) * (τ ^ (-((n:ℝ)/2 + 3/2))
              * Real.exp (-(9/128 * ‖x - y‖ ^ 2) / τ))
            + Real.exp (M ^ 2) * (8 * ‖x - y‖ ^ 2) * (τ ^ (-((n:ℝ)/2 + 5/2))
              * Real.exp (-(9/128 * ‖x - y‖ ^ 2) / τ)))) 1
      simpa using h
    have hFARCbd : Real.exp (M ^ 2)
              * ((‖x - y‖ / (8 * M / 3)) ^ (-((n:ℝ)/2 + 3/2))
                + 8 * ‖x - y‖ ^ 2 * (‖x - y‖ / (8 * M / 3)) ^ (-((n:ℝ)/2 + 5/2))
                + 4 * M ^ 2 * (‖x - y‖ / (8 * M / 3)) ^ (-((n:ℝ)/2 + 1/2))) ≤ (Real.exp (M ^ 2)
              * ((8 * M / 3) ^ ((n:ℝ)/2 + 3/2) * 2 ^ (-((n:ℝ)/2 + 3/2) + ((n:ℝ) + 1))
                + 8 * (8 * M / 3) ^ ((n:ℝ)/2 + 5/2)
                  * 2 ^ (1 - ((n:ℝ)/2 + 3/2) + ((n:ℝ) + 1))
                + 4 * M ^ 2 * (8 * M / 3) ^ ((n:ℝ)/2 + 1/2)
                  * 2 ^ (1 - ((n:ℝ)/2 + 3/2) + ((n:ℝ) + 1)))) * ‖x - y‖ ^ (-((n:ℝ) + 1)) := by
      have h := mul_le_mul_of_nonneg_left (add_le_add (add_le_add hf1 hf2) hf3)
        (Real.exp_pos (M ^ 2)).le
      calc Real.exp (M ^ 2)
              * ((‖x - y‖ / (8 * M / 3)) ^ (-((n:ℝ)/2 + 3/2))
                + 8 * ‖x - y‖ ^ 2 * (‖x - y‖ / (8 * M / 3)) ^ (-((n:ℝ)/2 + 5/2))
                + 4 * M ^ 2 * (‖x - y‖ / (8 * M / 3)) ^ (-((n:ℝ)/2 + 1/2)))
          ≤ Real.exp (M ^ 2)
            * ((8 * M / 3) ^ ((n:ℝ)/2 + 3/2) * 2 ^ (-((n:ℝ)/2 + 3/2) + ((n:ℝ) + 1))
                * ‖x - y‖ ^ (-((n:ℝ) + 1))
              + 8 * (8 * M / 3) ^ ((n:ℝ)/2 + 5/2)
                * 2 ^ (1 - ((n:ℝ)/2 + 3/2) + ((n:ℝ) + 1)) * ‖x - y‖ ^ (-((n:ℝ) + 1))
              + 4 * M ^ 2 * (8 * M / 3) ^ ((n:ℝ)/2 + 1/2)
                * 2 ^ (1 - ((n:ℝ)/2 + 3/2) + ((n:ℝ) + 1)) * ‖x - y‖ ^ (-((n:ℝ) + 1))) := h
        _ = (Real.exp (M ^ 2)
              * ((8 * M / 3) ^ ((n:ℝ)/2 + 3/2) * 2 ^ (-((n:ℝ)/2 + 3/2) + ((n:ℝ) + 1))
                + 8 * (8 * M / 3) ^ ((n:ℝ)/2 + 5/2)
                  * 2 ^ (1 - ((n:ℝ)/2 + 3/2) + ((n:ℝ) + 1))
                + 4 * M ^ 2 * (8 * M / 3) ^ ((n:ℝ)/2 + 1/2)
                  * 2 ^ (1 - ((n:ℝ)/2 + 3/2) + ((n:ℝ) + 1)))) * ‖x - y‖ ^ (-((n:ℝ) + 1)) := by ring
    have hT : ‖∫ r in Set.Ioo (0:ℝ) 1, innerSL ℝ (G x r)‖
        ≤ ((Real.exp (M ^ 2) * (K1 * (9/128 : ℝ) ^ (1 - ((n:ℝ)/2 + 3/2))
              + 8 * Kb * (9/128 : ℝ) ^ (-((n:ℝ)/2 + 3/2)))) + (Real.exp (M ^ 2)
              * ((8 * M / 3) ^ ((n:ℝ)/2 + 3/2) * 2 ^ (-((n:ℝ)/2 + 3/2) + ((n:ℝ) + 1))
                + 8 * (8 * M / 3) ^ ((n:ℝ)/2 + 5/2)
                  * 2 ^ (1 - ((n:ℝ)/2 + 3/2) + ((n:ℝ) + 1))
                + 4 * M ^ 2 * (8 * M / 3) ^ ((n:ℝ)/2 + 1/2)
                  * 2 ^ (1 - ((n:ℝ)/2 + 3/2) + ((n:ℝ) + 1))))) * ‖x - y‖ ^ (-((n:ℝ) + 1)) := by
      calc ‖∫ r in Set.Ioo (0:ℝ) 1, innerSL ℝ (G x r)‖
          ≤ ∫ r in Set.Ioo (0:ℝ) 1, ‖innerSL ℝ (G x r)‖ := norm_integral_le_integral_norm _
        _ ≤ ∫ r in Set.Ioo (0:ℝ) 1, ((Real.exp (M ^ 2) * ((1 - r) ^ (-((n:ℝ)/2 + 3/2))
                * Real.exp (-(9/128 * ‖x - y‖ ^ 2) / (1 - r)))
              + Real.exp (M ^ 2) * (8 * ‖x - y‖ ^ 2) * ((1 - r) ^ (-((n:ℝ)/2 + 5/2))
                * Real.exp (-(9/128 * ‖x - y‖ ^ 2) / (1 - r))))
              + Real.exp (M ^ 2)
              * ((‖x - y‖ / (8 * M / 3)) ^ (-((n:ℝ)/2 + 3/2))
                + 8 * ‖x - y‖ ^ 2 * (‖x - y‖ / (8 * M / 3)) ^ (-((n:ℝ)/2 + 5/2))
                + 4 * M ^ 2 * (‖x - y‖ / (8 * M / 3)) ^ (-((n:ℝ)/2 + 1/2)))) :=
            setIntegral_mono_on hGxint hboundint measurableSet_Ioo hbdpt
        _ = (∫ τ in Set.Ioo (0:ℝ) 1, (Real.exp (M ^ 2) * (τ ^ (-((n:ℝ)/2 + 3/2))
                * Real.exp (-(9/128 * ‖x - y‖ ^ 2) / τ))
              + Real.exp (M ^ 2) * (8 * ‖x - y‖ ^ 2) * (τ ^ (-((n:ℝ)/2 + 5/2))
                * Real.exp (-(9/128 * ‖x - y‖ ^ 2) / τ)))) + (Real.exp (M ^ 2)
              * ((‖x - y‖ / (8 * M / 3)) ^ (-((n:ℝ)/2 + 3/2))
                + 8 * ‖x - y‖ ^ 2 * (‖x - y‖ / (8 * M / 3)) ^ (-((n:ℝ)/2 + 5/2))
                + 4 * M ^ 2 * (‖x - y‖ / (8 * M / 3)) ^ (-((n:ℝ)/2 + 1/2)))) := hstep3
        _ ≤ (Real.exp (M ^ 2) * (K1 * (9/128 : ℝ) ^ (1 - ((n:ℝ)/2 + 3/2))
              + 8 * Kb * (9/128 : ℝ) ^ (-((n:ℝ)/2 + 3/2)))) * ‖x - y‖ ^ (-((n:ℝ) + 1)) + (Real.exp (M ^ 2)
              * ((8 * M / 3) ^ ((n:ℝ)/2 + 3/2) * 2 ^ (-((n:ℝ)/2 + 3/2) + ((n:ℝ) + 1))
                + 8 * (8 * M / 3) ^ ((n:ℝ)/2 + 5/2)
                  * 2 ^ (1 - ((n:ℝ)/2 + 3/2) + ((n:ℝ) + 1))
                + 4 * M ^ 2 * (8 * M / 3) ^ ((n:ℝ)/2 + 1/2)
                  * 2 ^ (1 - ((n:ℝ)/2 + 3/2) + ((n:ℝ) + 1)))) * ‖x - y‖ ^ (-((n:ℝ) + 1)) := add_le_add hNbd hFARCbd
        _ = ((Real.exp (M ^ 2) * (K1 * (9/128 : ℝ) ^ (1 - ((n:ℝ)/2 + 3/2))
              + 8 * Kb * (9/128 : ℝ) ^ (-((n:ℝ)/2 + 3/2)))) + (Real.exp (M ^ 2)
              * ((8 * M / 3) ^ ((n:ℝ)/2 + 3/2) * 2 ^ (-((n:ℝ)/2 + 3/2) + ((n:ℝ) + 1))
                + 8 * (8 * M / 3) ^ ((n:ℝ)/2 + 5/2)
                  * 2 ^ (1 - ((n:ℝ)/2 + 3/2) + ((n:ℝ) + 1))
                + 4 * M ^ 2 * (8 * M / 3) ^ ((n:ℝ)/2 + 1/2)
                  * 2 ^ (1 - ((n:ℝ)/2 + 3/2) + ((n:ℝ) + 1))))) * ‖x - y‖ ^ (-((n:ℝ) + 1)) := by ring
    calc Real.sqrt 2 * Real.pi ^ (-((n : ℝ) + 1) / 2)
            * ‖∫ r in Set.Ioo (0:ℝ) 1, innerSL ℝ (G x r)‖
        ≤ Real.sqrt 2 * Real.pi ^ (-((n : ℝ) + 1) / 2)
            * (((Real.exp (M ^ 2) * (K1 * (9/128 : ℝ) ^ (1 - ((n:ℝ)/2 + 3/2))
              + 8 * Kb * (9/128 : ℝ) ^ (-((n:ℝ)/2 + 3/2)))) + (Real.exp (M ^ 2)
              * ((8 * M / 3) ^ ((n:ℝ)/2 + 3/2) * 2 ^ (-((n:ℝ)/2 + 3/2) + ((n:ℝ) + 1))
                + 8 * (8 * M / 3) ^ ((n:ℝ)/2 + 5/2)
                  * 2 ^ (1 - ((n:ℝ)/2 + 3/2) + ((n:ℝ) + 1))
                + 4 * M ^ 2 * (8 * M / 3) ^ ((n:ℝ)/2 + 1/2)
                  * 2 ^ (1 - ((n:ℝ)/2 + 3/2) + ((n:ℝ) + 1))))) * ‖x - y‖ ^ (-((n:ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left hT hcn.le
      _ = Real.sqrt 2 * Real.pi ^ (-((n : ℝ) + 1) / 2)
            * ((Real.exp (M ^ 2) * (K1 * (9/128 : ℝ) ^ (1 - ((n:ℝ)/2 + 3/2))
              + 8 * Kb * (9/128 : ℝ) ^ (-((n:ℝ)/2 + 3/2)))) + (Real.exp (M ^ 2)
              * ((8 * M / 3) ^ ((n:ℝ)/2 + 3/2) * 2 ^ (-((n:ℝ)/2 + 3/2) + ((n:ℝ) + 1))
                + 8 * (8 * M / 3) ^ ((n:ℝ)/2 + 5/2)
                  * 2 ^ (1 - ((n:ℝ)/2 + 3/2) + ((n:ℝ) + 1))
                + 4 * M ^ 2 * (8 * M / 3) ^ ((n:ℝ)/2 + 1/2)
                  * 2 ^ (1 - ((n:ℝ)/2 + 3/2) + ((n:ℝ) + 1))))) * ‖x - y‖ ^ (-((n:ℝ) + 1)) := by ring
